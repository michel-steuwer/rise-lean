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

declare_syntax_cat                  lamb_expr
syntax "lamb" ident "." lamb_expr : lamb_expr
syntax ident                      : lamb_expr
syntax lamb_expr lamb_expr        : lamb_expr
syntax num                        : lamb_expr
syntax "plus" : lamb_expr

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

  | `(lamb_expr| plus) => do
    match ctx.find? (fun (name, _, _) => name == "plus".toName) with
    | some (_, fvar, lambType) =>
      return (fvar, lambType)
    | none => throwError s!"unknown identifier plus"


  | `(lamb_expr| $x:ident) => do
    match ctx.find? (fun (name, _, _) => name == x.getId) with
    | some (_, fvar, lambType) =>
      let term := mkAppN (mkConst ``LambTerm'.var) #[rep, lambType, fvar]
      return (term, lambType)
    -- TODO: could probably do better here. the error doesn't show where exactly
    --       the unknown identifier was found.
    | none => throwError s!"unknown identifier {x}"



  | `(lamb_expr| $e1:lamb_expr $e2:lamb_expr) => do
      let (e1, e1Type) ← elabLamb e1 rep ctx
      let (e2, e2Type) ← elabLamb e2 rep ctx

      -- TODO: check e1 is .fn, get dom type from there
      -- let term := mkAppN (mkConst ``LambTerm'.app) #[rep, e1, e2]
      return (e1, e1Type)

  | `(lamb_expr| $n:num) => do
    let natType := mkConst ``LambType.nat
    let term := mkAppN (mkConst ``LambTerm'.const) #[rep, mkNatLit n.getNat]
    return (term, natType)

  | _ => throwUnsupportedSyntax


elab "[lamb|" l:lamb_expr "]" : term => do
  -- creates implicit parameter rep. otherwise result contains metavariable, which AppBuilder doesn't like
  let repMVar ← mkFreshExprMVar
                  (← mkArrow (mkConst ``LambType) (mkSort levelOne))
                  (userName := "rep".toName)
  let context : ElabCtx := [
    -- adding "primitive" to context. could be made nicer with a LambType.toExpr.
    ("plus".toName,
     mkAppN (mkConst ``LambTerm'.prim) #[repMVar,
                  mkAppN (mkConst ``LambType.fn)
                  #[mkConst ``LambType.nat, mkConst ``LambType.nat],
                  mkStrLit "plus"
                  ],
     mkAppN (mkConst ``LambType.fn)
             #[mkConst ``LambType.nat, mkConst ``LambType.nat]),
  ]
  let (term, _) ← elabLamb l repMVar context
  return term

--set_option pp.explicit true
open LambType


#check [lamb| 3]

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
