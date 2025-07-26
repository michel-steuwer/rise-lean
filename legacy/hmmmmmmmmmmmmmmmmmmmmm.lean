inductive LambType where
  | nat
  | fn : LambType → LambType → LambType

@[reducible] def LambType.denote : LambType → Type
  | nat    => Nat
  | fn a b => a.denote → b.denote

inductive LambTerm' : LambType → Type where
  | var   : Nat → LambTerm' .nat
  | const : Nat → LambTerm' rep
  | prim : String → LambTerm' rep
  | app   : LambTerm' (.fn dom ran) → LambTerm' dom → LambTerm' ran
  | abst  : LambTerm' a → LambTerm' (.fn a a)


def identity : LambTerm' <| .fn .nat .nat :=
  .abst <| .var 0

