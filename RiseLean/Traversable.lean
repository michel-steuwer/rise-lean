import Elevate.Prelude
import RiseLean.Prelude

namespace Traversable

def RExpr.all (s: Strategy RExpr) : Strategy RExpr :=
  fun e => match e with
    | .lit _ | .bvar _ | .fvar _ | .const _ => .ok e
    | .app f e => do
      let f' <- s f
      let e' <- s e
      return (.app f' e')
    | .lam bn bt e => do
      let e' <- s e
      return (.lam bn bt e')
    | .ulam bn bt e => do
      let e' <- s e
      return (.ulam bn bt e')

def RExpr.some (s: Strategy RExpr) : Strategy RExpr :=
  fun e => match e with
    | .lit _ | .bvar _ | .fvar _ | .const _ => .error ""
    | .app f e =>
      match (s f, s e) with
        | (.ok f', .ok e') => .ok (.app f' e')
        | (.ok f',      _) => .ok (.app f' e )
        | (_,      .ok e') => .ok (.app f  e')
        | _ => .error ""
    | .lam bn bt e =>
      match s e with
        | .ok e' => .ok (.lam bn bt e')
        | _ => .error ""
    | .ulam bn bt e => do
      match s e with
        | .ok e' => .ok (.ulam bn bt e')
        | _ => .error ""

def RExpr.one (s: Strategy RExpr) : Strategy RExpr :=
  fun e => match e with
    | .lit _ | .bvar _ | .fvar _ | .const _ => .error ""
    | .app f e =>
      match s f with
        | .ok f' => .ok (.app f' e)
        | _ => match s e with
          | .ok e' => .ok (.app f e')
          | _ => .error ""
    | .lam bn bt e =>
      match s e with
        | .ok e' => .ok (.lam bn bt e')
        | _ => .error ""
    | .ulam bn bt e => do
      match s e with
        | .ok e' => .ok (.ulam bn bt e')
        | _ => .error ""

instance : Traversable RExpr where
  all := RExpr.all
  some := RExpr.some
  one := RExpr.one
