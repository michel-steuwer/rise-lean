import Elevate.Prelude
import RiseLean.Prelude

namespace Traversable

def RExpr.all (s: Strategy RExpr) : Strategy RExpr :=
  fun e => match e with
    | .lit _ | .bvar _ _ => .ok e
    | .app f e => do
      let f' <- s f
      let e' <- s e
      return (.app f' e')
    | .lam b e => do
      let e' <- s e
      return (.lam b e')
    | .ulam b e => do
      let e' <- s e
      return (.ulam b e')

def RExpr.some (s: Strategy RExpr) : Strategy RExpr :=
  fun e => match e with
    | .lit _ | .bvar _ _ => .error ""
    | .app f e =>
      match (s f, s e) with
        | (.ok f', .ok e') => .ok (.app f' e')
        | (.ok f',      _) => .ok (.app f' e )
        | (_,      .ok e') => .ok (.app f  e')
        | _ => .error ""
    | .lam b e =>
      match s e with
        | .ok e' => .ok (.lam b e')
        | _ => .error ""
    | .ulam b e => do
      match s e with
        | .ok e' => .ok (.ulam b e')
        | _ => .error ""

def RExpr.one (s: Strategy RExpr) : Strategy RExpr :=
  fun e => match e with
    | .lit _ | .bvar _ _ => .error ""
    | .app f e =>
      match s f with
        | .ok f' => .ok (.app f' e)
        | _ => match s e with
          | .ok e' => .ok (.app f e')
          | _ => .error ""
    | .lam b e =>
      match s e with
        | .ok e' => .ok (.lam b e')
        | _ => .error ""
    | .ulam b e => do
      match s e with
        | .ok e' => .ok (.ulam b e')
        | _ => .error ""

instance : Traversable RExpr where
  all := RExpr.all
  some := RExpr.some
  one := RExpr.one
