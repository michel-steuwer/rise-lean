open My

namespace My

inductive Ty where
| scalar : Ty
| array : Nat -> Ty -> Ty
deriving Repr, BEq

end My

declare_syntax_cat my_ty

syntax "float" : my_ty
syntax num " . " my_ty : my_ty

syntax "ty%" my_ty : term

macro_rules
| `(term| ty% float) => `(Ty.scalar)
| `(term| ty% $n:num . $t:my_ty) => `(Ty.array $n (ty% $t))

#eval ty% 1 . 2 . float
#eval ty% 1 . 2 . float == Ty.array 1 (Ty.array 2 Ty.scalar)