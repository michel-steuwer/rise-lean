import Lean
open Lean Elab Command Meta

inductive LambType where
  | nat
  | fn : LambType → LambType → LambType

@[reducible] def LambType.denote : LambType → Type
  | nat    => Nat
  | fn a b => a.denote → b.denote

inductive LambTerm' (rep : LambType → Type) : LambType → Type where
  | var   : rep ty → LambTerm' rep ty
  | const : Nat → LambTerm' rep .nat
  | prim : String → LambTerm' rep ty
  | app   : LambTerm' rep (.fn dom ran) → LambTerm' rep dom → LambTerm' rep ran
  | abst  : (rep dom → LambTerm' rep ran) → LambTerm' rep (.fn dom ran)

def LambTerm (ty : LambType) := {rep : LambType → Type} → LambTerm' rep ty

def identity : LambTerm' rep (.fn .nat .nat) :=
  .abst (fun x => .var x)

#check identity


open LambType

def LambType.toExpr : LambType → Expr
  | .nat => mkConst ``LambType.nat
  | .fn a b => mkAppN (mkConst ``LambType.fn) #[a.toExpr, b.toExpr]


declare_syntax_cat                  lamb_expr
syntax "lamb" ident "." lamb_expr : lamb_expr
syntax ident                      : lamb_expr
syntax lamb_expr:10 lamb_expr:11        : lamb_expr
syntax num                        : lamb_expr

-- TODO: i wonder if the manual context management is necessary at all?
abbrev ElabCtx := List (Name × Expr × Expr) -- name, fvar, and lambtype

partial def elabLamb (stx : Syntax) (rep : Expr) (ctx : ElabCtx) : TermElabM (Expr × Expr) :=
  match stx with
  | `(lamb_expr| lamb $x:ident . $b:lamb_expr) => do
    let domType := mkConst ``LambType.nat -- all consts are nat for now
    let repDomType := mkApp rep domType

    -- creates new fvar and passes it to context (this do block)
    withLocalDeclD x.getId repDomType fun fvar => do
      let (b', ranType) ← elabLamb b rep ((x.getId, fvar, domType) :: ctx)
      let abstFn ← mkLambdaFVars #[fvar] b' -- adds binder & replaces every fvar in b' with a bound var
      let fnType ← mkAppM ``LambType.fn #[domType, ranType]
      let term := mkAppN (mkConst ``LambTerm'.abst) #[rep, domType, ranType, abstFn]
      return (term, fnType)


  | `(lamb_expr| $x:ident) => do
    match ctx.find? (fun (name, _, _) => name == x.getId) with
    | some (_, e, t) =>
      match e.getAppFn with
      | .const ``LambTerm'.prim _ => return (e, t)
      | _ => let term := mkAppN (mkConst ``LambTerm'.var) #[rep, t, e]
             return (term, t)
    | none => throwErrorAt x s!"unknown identifier {x}"



  | `(lamb_expr| $e1s:lamb_expr $e2s:lamb_expr) => do
      let (e1, e1Type) ← elabLamb e1s rep ctx
      let (e2, e2Type) ← elabLamb e2s rep ctx

      -- TODO: check e1 is .fn, get dom type from there
      -- throwError e1Type.getAppFn
      match e1Type.getAppFn with
      | .const ``LambType.fn _ => throwErrorAt e1s "{e1} is not a function!"
      | _ => throwError "hi"

      let domType := mkConst ``LambType.nat -- todo
      let ranType := mkConst ``LambType.nat -- todo
      let term := mkAppN (mkConst ``LambTerm'.app) #[rep, domType, ranType, e1, e2]
      -- TODO: get e1 range type
      return (term, e1Type)

  | `(lamb_expr| $n:num) => do
    let natType := mkConst ``LambType.nat
    let term := mkAppN (mkConst ``LambTerm'.const) #[rep, mkNatLit n.getNat]
    return (term, natType)

  | _ => throwUnsupportedSyntax


def mkPrim (name : String) (t : LambType) (rep: Expr) :=
  let t := t.toExpr
  (name.toName, mkAppN (mkConst ``LambTerm'.prim) #[rep, t, mkStrLit name], t)

elab "[lamb|" l:lamb_expr "]" : term => do
  -- creates implicit parameter rep. otherwise result contains metavariable, which AppBuilder doesn't like
  let repMVar ← mkFreshExprMVar
                  (← mkArrow (mkConst ``LambType) (mkSort levelOne))
                  (userName := "rep".toName)
  let context : ElabCtx := [
    -- adding "primitives" to context.
    ("plus", fn nat <| fn nat nat),
    ("mult", fn nat <| fn nat nat),
    ("inc",  fn nat nat),
    ("one",  nat)
    -- ...
  ].map (fun (n, t) => mkPrim n t repMVar)

  let (term, _) ← elabLamb l repMVar context
  return term

--set_option pp.explicit true
#check [lamb| 3]

#check [lamb| lamb x . x ]

#check [lamb| inc 3 ]


example : LambTerm (fn nat nat) := [lamb| lamb x . x]
example : LambTerm (nat)        := [lamb| plus 1 2]

#check [lamb| lamb x . lamb y . plus x ]

#check identity

def identity2 : LambTerm (.fn .nat .nat) :=
  .abst (fun x => .var x)

def identity3 : LambTerm (.fn .nat .nat) :=
  [lamb| lamb x . x ]

-- def pretty (e : LambTerm' (fun _ => String) ty) (i : Nat := 1) : String :=
--   match e with
--   | .var s     => s
--   | .const n   => toString n
--   | .abst f     =>
--     let x := s!"x_{i}"
--     s!"(fun {x} => {pretty (f x) (i+1)})"

-- #eval pretty [lamb| lamb x . x]

-- @[simp] def denote : LambTerm' LambType.denote ty → ty.denote
--   | .var x    => x
--   | .const n  => n
--   | .abst f    => fun x => denote (f x)

-- axiom plus : LambTerm (fn nat nat)
-- axiom two  : LambTerm (nat)

-- @[reducible] def LambTerm.type (_ : LambTerm ty) : LambType := ty

-- theorem x : plus.type.denote = Nat → Nat := by grind

-- axiom t : String -> Nat
-- axiom b : String

-- #check t b


-- def reduce (t : LambTerm ty1) : LambTerm ty2 :=
--   match t with
--   | .app e1 e2 => match e1 with
--     | .abst f a => f
--     | x => x
--   | x => x
