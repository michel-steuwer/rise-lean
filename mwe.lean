import Lean
open Lean Elab Command Term Meta

inductive LambType where
  | nat
  | fn : LambType → LambType → LambType

inductive LambTerm' (rep : LambType → Type) : LambType → Type where
  | var   : rep ty → LambTerm' rep ty
  | const : Nat → LambTerm' rep .nat
  | abst  : (rep dom → LambTerm' rep ran) → LambTerm' rep (.fn dom ran)

def LambTerm (ty : LambType) := {rep : LambType → Type} → LambTerm' rep ty

def identity : LambTerm (.fn .nat .nat) :=
  .abst (fun x => .var x)

declare_syntax_cat                  lamb_expr
syntax "lamb" ident "." lamb_expr : lamb_expr
syntax ident                      : lamb_expr
syntax num                        : lamb_expr

-- Context for the elaborator, mapping variable names to their expressions and types
abbrev ElabCtx := List (Name × Expr × Expr) -- name, fvar, and lambtype as an Expr

-- The recursive elaborator for lambda expressions
partial def elabLamb (stx : Syntax) (rep : Expr) (ctx : ElabCtx) : TermElabM (Expr × Expr) :=
  match stx with
  | `(lamb_expr| lamb $x:ident . $b:lamb_expr) => do
    -- For simplicity, we assume all bound variables are nats.
    -- A real implementation would need type inference or annotations.
    let domTyExpr := Lean.mkConst ``LambType.nat
    let repDomTy := Lean.mkApp rep domTyExpr

    withLocalDeclD x.getId repDomTy fun fvar => do
      let (b', ranTyExpr) ← elabLamb b rep ((x.getId, fvar, domTyExpr) :: ctx)
      let abstFn ← mkLambdaFVars #[fvar] b'
      let fnTyExpr ← mkAppM ``LambType.fn #[domTyExpr, ranTyExpr]
      let term := Lean.mkAppN (Lean.mkConst ``LambTerm'.abst) #[rep, domTyExpr, ranTyExpr, abstFn]
      return (term, fnTyExpr)

  | `(lamb_expr| $x:ident) => do
    match ctx.find? (fun (name, _, _) => name == x.getId) with
    | some (_, fvar, ltyExpr) =>
      let term := Lean.mkAppN (Lean.mkConst ``LambTerm'.var) #[rep, ltyExpr, fvar]
      return (term, ltyExpr)
    | none => throwError s!"unknown identifier {x}"

  | `(lamb_expr| $n:num) => do
    let natTyExpr := Lean.mkConst ``LambType.nat
    let term := Lean.mkAppN (Lean.mkConst ``LambTerm'.const) #[rep, mkNatLit n.getNat]
    return (term, natTyExpr)

  | _ => throwUnsupportedSyntax

-- The top-level elaborator that sets up the polymorphic 'rep'
elab "[lamb|" l:lamb_expr "]" : term => do
  -- We create a binder for `rep` which makes `LambTerm` polymorphic.
  withLocalDeclD `rep (← mkArrow (Lean.mkConst ``LambType) (mkSort levelOne)) fun repVar => do
    let (term, _) ← elabLamb l repVar []
    mkLambdaFVars #[repVar] term

--set_option pp.explicit true

-- This should now work and produce a term of type `LambTerm .nat`
#reduce [lamb| 3]

-- This should also work, producing a term of type `LambTerm (.fn .nat .nat)`
#reduce [lamb| lamb x . lamb y . y ]

-- Example of a more complex term
#reduce [lamb| lamb x . lamb y . x]

#check identity

def iidentity : LambTerm (.fn .nat .nat) :=
  .abst (fun x => .var x)

def iiiidentity : LambTerm (.fn .nat .nat) :=
  [lamb| lamb x . x ]

def iiidentity : (rep : LambType → Type) → LambTerm' rep (LambType.nat.fn LambType.nat) :=
  [lamb| lamb x . x ]

def pretty (e : LambTerm' (fun _ => String) ty) (i : Nat := 1) : String :=
  match e with
  | .var s     => s
  | .const n   => toString n
  --| .app f a   => s!"({pretty f i} {pretty a i})"
  --| .plus a b  => s!"({pretty a i} + {pretty b i})"
  | .abst f     =>
    let x := s!"x_{i}"
    s!"(fun {x} => {pretty (f x) (i+1)})"

#eval pretty $ [lamb| lamb x . x] (fun _ => String)
