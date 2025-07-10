import Lean

-- Why parametric higher-order abstract syntax (PHOAS)?
-- Let's start with first-order abstract syntax (FOAS):
namespace FOAS
inductive Term
  | var   : String → Term
  | const : Nat → Term
  | abst  : String → Term → Term
-- Variables are represented by Strings. This works, but means that Lean doesn't know about
-- the object language's binders, and we have to manually implement things such as name analysis and beta-reduction.
-- This will also make it more cumbersome to prove things about our object language.
end FOAS

-- We can do better: with _higher_-order abstract syntax (HOAS).
-- That is, we represent binders of the object language with binders of the meta language (Lean).
-- So now, the Term.abst constructor takes a function Term → Term.
--
-- But this leads to the following error:

namespace HOAS
/--
error: (kernel) arg #1 of 'HOAS.Term.abst' has a non positive occurrence of the datatypes being declared
-/
#guard_msgs in
inductive Term
  | var   : Term -- UGH
  | const : Nat → Term
  | abst  : (Term → Term) → Term
--        [1] ^

-- The Lean kernel has a "strict positivity restriction": When defining an inductive type, the type
-- being defined must not occur to the left of an arrow in the type of a constructor argument. This happens at [1].
-- It's not allowed because it would break normalization.
-- "We would be able to prove every theorem with an inifinite loop"

def uhoh (t : Term) : Term :=
  match t with
    | .abst f => f t
    | _ => t

-- uhoh (Term.abst uhoh)

-- ← This term would loop forever.

end HOAS

-- So, enter PHOAS!

-- First, we'll also make our language typed.

inductive Ty where
  | nat
  | fn : Ty → Ty → Ty

@[reducible] def Ty.denote : Ty → Type
  | nat    => Nat
  | fn a b => a.denote → b.denote

-- Now we define Term'. It is parametrized by a type family `rep` which stands for "representation of variables".
-- In Term'.abst, we again have a function as argument, but that function now only takes a variable as argument.
--
-- The `rep` parameter is treated as an unconstrained choice of which data should be annotated on each variable.
-- And the caller decides which data should be annotated - we construct terms in our language without mentioning `rep`.

inductive Term' (rep : Ty → Type) : Ty → Type
  | var   : rep ty → Term' rep ty
  | const : Nat → Term' rep .nat
  | plus  : Term' rep .nat → Term' rep .nat → Term' rep .nat
  | abst   : (rep dom → Term' rep ran) → Term' rep (.fn dom ran)
  | app   : Term' rep (.fn dom ran) → Term' rep dom → Term' rep ran
  | let   : Term' rep ty₁ → (rep ty₁ → Term' rep ty₂) → Term' rep ty₂

open Ty (nat fn)
def Term (ty : Ty) := {rep : Ty → Type} → Term' rep ty


def  lxx : Term' rep (fn nat nat) := .abst (fun x => .var x)
--#eval pretty lxx

def add : Term (fn nat (fn nat nat)) :=
  .abst fun x => .abst fun y => .plus (.var x) (.var y)

def three_the_hard_way : Term nat :=
  .app (.app add (.const 1)) (.const 2)

def countVars : Term' (fun _ => Unit) ty → Nat
  | .var _    => 1
  | .const _  => 0
  | .plus a b => countVars a + countVars b
  | .app f a  => countVars f + countVars a
  | .abst b    => countVars (b ())
  | .let a b  => countVars a + countVars (b ())

example : countVars add = 2 := rfl

def pretty (e : Term' (fun _ => String) ty) (i : Nat := 1) : String :=
  match e with
  | .var s     => s
  | .const n   => toString n
  | .app f a   => s!"({pretty f i} {pretty a i})"
  | .plus a b  => s!"({pretty a i} + {pretty b i})"
  | .abst f     =>
    let x := s!"x_{i}"
    s!"(fun {x} => {pretty (f x) (i+1)})"
  | .let a b  =>
    let x := s!"x_{i}"
    s!"(let {x} := {pretty a i}; => {pretty (b x) (i+1)}"


#eval pretty three_the_hard_way

#eval pretty add

def idd : Term (fn nat nat) :=
  .abst (fun x => .var x)

#eval pretty idd


def squash : Term' (Term' rep) ty → Term' rep ty
 | .var e    => e
 | .const n  => .const n
 | .plus a b => .plus (squash a) (squash b)
 | .abst f    => .abst fun x => squash (f (.var x))
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
  | .abst f    => fun x => denote (f x)
  | .let a b  => denote (b (denote a))

example : denote three_the_hard_way = 3 :=
  rfl


@[simp] def constFold : Term' rep ty → Term' rep ty
  | .var x    => .var x
  | .const n  => .const n
  | .app f a  => .app (constFold f) (constFold a)
  | .abst f    => .abst fun x => constFold (f x)
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
