import Lean
open Lean Elab Meta Command

inductive RKind
  | data
  | nat
--  | ...

inductive RExpr where
  | bvar (deBruijnIndex : Nat) (userName : String)
  -- | const (declName : Name) (us : List VLevel)
  | prim (name : String)
  | lit (val : Nat)
  | app (fn arg : RExpr)
  
  | lam (body : RExpr)
  | pi (implicit : Bool) (binderType body : RExpr) -- maybe have this in a separate thing RType

abbrev RTypingCtx := Array (Name × Option RExpr)
abbrev RKindingCtx := Array (Option Name × RExpr) -- necessary?

-- def dot : RExpr := .lam (.app (.app (.prim "reduce") (.prim "add")) (.lit 0))
def s : RExpr := .lam <| .lam (.app (.app
                                      (.prim "plus")
                                      (.bvar 0 "a"))
                                    (.bvar 1 "b"))


declare_syntax_cat                         rise_expr
-- syntax rise_lit                          : rise_expr
syntax num : rise_expr
syntax ident                             : rise_expr
syntax "fun" "(" ident "," rise_expr ")" : rise_expr
syntax rise_expr "(" rise_expr ")"       : rise_expr -- application
syntax rise_expr "|>" rise_expr          : rise_expr -- sugar for application


partial def elabRExpr (tctx : RTypingCtx) : Syntax → TermElabM Expr
  | `(rise_expr| $l:num) => do
    let x ← mkAppM ``RExpr.lit #[mkNatLit l.getNat]
    return x
  | `(rise_expr| $i:ident) => do
    match tctx.reverse.findIdx? (λ (name, _) => name == i.getId) with
    | some idx =>
      mkAppM ``RExpr.bvar #[mkNatLit <| idx, mkStrLit i.getId.toString]
    | none => throwErrorAt i s!"unknown identifier {mkConst i.getId}"
  | `(rise_expr| fun ( $x:ident , $b:rise_expr )) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) b
    return b
  | `(rise_expr| $e1:rise_expr ( $e2:rise_expr )) => do
      let e1 ← elabRExpr tctx e1 -- TODO: these should return a new context?
      let e2 ← elabRExpr tctx e2
      mkAppM ``RExpr.app #[e1, e2]
  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f($e))
    elabRExpr tctx s
  | _ => throwUnsupportedSyntax

elab "[Rise|" l:rise_expr "]" : term => do
  let tctx : RTypingCtx := #[]

  let term ← elabRExpr tctx l
  return term

#check [Rise| fun(as, as)]
#check [Rise| fun(as, fun(bs, as(bs)))]
#check [Rise| fun(as, fun(bs, as(bs (fun(c, c)))))]
#check [Rise| fun(as, as (fun(as, as)))]


