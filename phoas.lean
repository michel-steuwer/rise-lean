
import Lean

inductive Ty where
  | nat
  | fn : Ty → Ty → Ty

@[reducible] def Ty.denote : Ty → Type
  | nat    => Nat
  | fn a b => a.denote → b.denote

example : Ty := Ty.fn Ty.nat Ty.nat

inductive Term' (rep : Ty → Type) : Ty → Type
  | var   : rep ty → Term' rep ty
  | const : Nat → Term' rep .nat
  | plus  : Term' rep .nat → Term' rep .nat → Term' rep .nat
  | lam   : (rep dom → Term' rep ran) → Term' rep (.fn dom ran)
  | app   : Term' rep (.fn dom ran) → Term' rep dom → Term' rep ran
  | let   : Term' rep ty₁ → (rep ty₁ → Term' rep ty₂) → Term' rep ty₂


open Ty (nat fn)

namespace FirstTry
  def Term (ty : Ty) := (rep : Ty → Type) → Term' rep ty

  def add : Term (fn nat (fn nat nat)) := fun _rep =>
    .lam fun x => .lam fun y => .plus (.var x) (.var y)

  def three_the_hard_way : Term nat := fun rep =>
    .app (.app (add rep) (.const 1)) (.const 2)
end FirstTry



def Term (ty : Ty) := {rep : Ty → Type} → Term' rep ty

declare_syntax_cat imp_lit
syntax (name:=mylamb) "lam" ident "." term : imp_lit


open Lean Elab Command Term Meta

-- @[term_elab mylamb]
-- def myTerm1Impl : TermElab := fun stx type? => do
--   mkAppM ``Term'.lam #[]
--   --mkAppM ``List.get! #[.const ``mytermValues [], mkNatLit 0] -- `MetaM` code



def elabIMPLit : Syntax → TermElabM Expr
  | `(imp_lit| lam $x:ident . $b:term) => do
    let type ← mkFreshTypeMVar
    withLocalDeclD x.getId type fun fvar => do
      let b ← elabTerm b none
      let laam ← mkLambdaFVars #[fvar] b
      mkAppM ``Term'.lam #[laam]
  | _ => throwUnsupportedSyntax

elab "test_elabIMPLit " l:imp_lit : term => elabIMPLit l

#reduce test_elabIMPLit lam x . Term'.var x     -- IMPLit.nat 4
-- #reduce test_elabIMPLit true  -- IMPLit.bool true
-- #reduce test_elabIMPLit false -- IMPLit.bool true

-- macro_rules
--   | `(lamb $x:ident ! $body:term) => `(Term.lam (fun $x => $x))

-- #check lamb as ! as

--  | `({ $var:ident : $ty:term | $body:term }) => `(setOf (fun ($var : $ty) => $body))
--  | `({ $var:ident ∈ $s:term | $body:term }) => `(setOf (fun $var => $var ∈ $s ∧ $body))



def add : Term (fn nat (fn nat nat)) :=
  .lam fun x => .lam fun y => .plus (.var x) (.var y)

def three_the_hard_way : Term nat :=
  .app (.app add (.const 1)) (.const 2)

def countVars : Term' (fun _ => Unit) ty → Nat
  | .var _    => 1
  | .const _  => 0
  | .plus a b => countVars a + countVars b
  | .app f a  => countVars f + countVars a
  | .lam b    => countVars (b ())
  | .let a b  => countVars a + countVars (b ())

example : countVars add = 2 := rfl

def pretty (e : Term' (fun _ => String) ty) (i : Nat := 1) : String :=
  match e with
  | .var s     => s
  | .const n   => toString n
  | .app f a   => s!"({pretty f i} {pretty a i})"
  | .plus a b  => s!"({pretty a i} + {pretty b i})"
  | .lam f     =>
    let x := s!"x_{i}"
    s!"(fun {x} => {pretty (f x) (i+1)})"
  | .let a b  =>
    let x := s!"x_{i}"
    s!"(let {x} := {pretty a i}; => {pretty (b x) (i+1)}"

#eval pretty three_the_hard_way

#eval pretty add

def idd : Term (fn nat nat) :=
  .lam (fun x => .var x)

#eval pretty idd


def squash : Term' (Term' rep) ty → Term' rep ty
 | .var e    => e
 | .const n  => .const n
 | .plus a b => .plus (squash a) (squash b)
 | .lam f    => .lam fun x => squash (f (.var x))
 | .app f a  => .app (squash f) (squash a)
 | .let a b  => .let (squash a) fun x => squash (b (.var x))

def Term1 (ty1 ty2 : Ty) := {rep : Ty → Type} → rep ty1 → Term' rep ty2

def subst (e : Term1 ty1 ty2) (e' : Term ty1) : Term ty2 :=
  squash (e e')

#eval pretty <| subst (fun x => .plus (.var x) (.const 5)) three_the_hard_way

@[simp] def denote : Term' Ty.denote ty → ty.denote
  | .var x    => x
  | .const n  => n
  | .plus a b => denote a + denote b
  | .app f a  => denote f (denote a)
  | .lam f    => fun x => denote (f x)
  | .let a b  => denote (b (denote a))

example : denote three_the_hard_way = 3 :=
  rfl


@[simp] def constFold : Term' rep ty → Term' rep ty
  | .var x    => .var x
  | .const n  => .const n
  | .app f a  => .app (constFold f) (constFold a)
  | .lam f    => .lam fun x => constFold (f x)
  | .let a b  => .let (constFold a) fun x => constFold (b x)
  | .plus a b =>
    match constFold a, constFold b with
    | .const n, .const m => .const (n+m)
    | a',       b'       => .plus a' b'


theorem constFold_sound (e : Term' Ty.denote ty) : denote (constFold e) = denote e := by
  induction e with simp [*]
  | plus a b iha ihb =>
    split
    next he₁ he₂ => simp [← iha, ← ihb, he₁, he₂]
    next => simp [iha, ihb]
