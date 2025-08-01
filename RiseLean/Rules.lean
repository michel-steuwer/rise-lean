import RiseLean.Prelude
import RiseLean.Program
import RiseLean.Traversable
import Elevate.Prelude

def rule.transpose_transpose : Strategy RExpr :=
  fun e => match e with
    | .app (.const `transpose) (.app (.const `transpose) x) =>
      .ok x
    | _ => .error "rule.transpose_transpose"


#eval
let input := [RiseC|
  fun (x : 32 . 32 .float) => transpose (transpose x) ].expr ;
let expected := [RiseC|
  fun (x : 32 . 32 .float) => x ].expr;
match (Strategy.topDown rule.transpose_transpose) input with
  | .ok computed =>
    computed == expected
  | .error _ => false
