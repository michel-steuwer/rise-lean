import RiseLean.Type
import Lean
open Lean Elab Meta

abbrev RTypingCtx := Array (Name × Option RType)

inductive RExpr where
  | bvar (deBruijnIndex : Nat) (userName : String)
  -- | const (declName : Name) (us : List VLevel)
  | lit (val : Nat)
  | app (fn arg : RExpr)

  | lam (body : RExpr) (binderKind : Option RType)
  | ulam (body : RExpr) (binderType : Option RKind)
deriving Repr

-- def dot : RExpr := .lam (.app (.app (.prim "reduce") (.prim "add")) (.lit 0))
-- def s : RExpr := .lam <| .lam (.app (.app
--                                       (.prim "plus")
--                                       (.bvar 0 "a"))
--                                     (.bvar 1 "b"))


declare_syntax_cat rise_expr
syntax num                                                  : rise_expr
syntax ident                                                : rise_expr
syntax "fun" "(" ident (":" rise_type)? ")" "=>" rise_expr  : rise_expr
syntax "fun"     ident (":" rise_type)?     "=>" rise_expr  : rise_expr
syntax "fun" "(" ident (":" rise_kind)  ")" "=>" rise_expr  : rise_expr
syntax:50 rise_expr:50 rise_expr:51                         : rise_expr
syntax:40 rise_expr:41 "|>" rise_expr:40                    : rise_expr
syntax:60 "(" rise_expr ")"                                 : rise_expr

-- a ToExpr instance would be nice to have!

partial def elabRExpr (tctx : RTypingCtx) (kctx : RKindingCtx) (mctx : MVarCtx) : Syntax → TermElabM Expr
  | `(rise_expr| $l:num) => do
    mkAppM ``RExpr.lit #[mkNatLit l.getNat]

  | `(rise_expr| $i:ident) => do
    match tctx.reverse.findIdx? (λ (name, _) => name == i.getId) with
      | some index =>
        mkAppM ``RExpr.bvar #[mkNatLit <| index, mkStrLit i.getId.toString]
      -- could give a hint here if we find the identifier in the kinding context.
      | none => throwErrorAt i s!"unknown identifier {mkConst i.getId}"

  | `(rise_expr| fun $x:ident => $b:rise_expr )
  | `(rise_expr| fun ($x:ident) => $b:rise_expr ) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) kctx mctx b
    let none := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
    mkAppM ``RExpr.lam #[b, none]

  | `(rise_expr| fun $x:ident : $t:rise_type => $b:rise_expr )
  | `(rise_expr| fun ( $x:ident : $t:rise_type ) => $b:rise_expr ) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) kctx mctx b
    -- let syntaxTerm : TSyntax `term ← `([RiseT| $t])
    -- let t ← Term.elabTerm syntaxTerm (some (mkConst ``RType))
    let t ← elabRType kctx mctx t
    let some := mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RType, t]
    mkAppM ``RExpr.lam #[b, some]

  | `(rise_expr| fun ( $x:ident : $t:rise_kind ) => $b:rise_expr ) => do
    let syntaxTerm : TSyntax `term ← `([RiseK| $t])
    let t ← Term.elabTerm syntaxTerm none --(mkConst ``RKind) --(some (mkConst ``RType))
    let b ← elabRExpr tctx (kctx.push (x.getId, t)) mctx b
    let some := mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RKind, t]
    -- let none := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
    mkAppM ``RExpr.ulam #[b, some]

  | `(rise_expr| $e1:rise_expr $e2:rise_expr ) => do
      let e1 ← elabRExpr tctx kctx mctx e1
      let e2 ← elabRExpr tctx kctx mctx e2
      mkAppM ``RExpr.app #[e1, e2]

  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f $e)
    elabRExpr tctx kctx mctx s

  | `(rise_expr| ( $e:rise_expr )) => do
    let s ← `(rise_expr| $e)
    elabRExpr tctx kctx mctx s

  | _ => throwUnsupportedSyntax

elab "[RiseE|" e:rise_expr "]" : term => do
  let p ← liftMacroM <| expandMacros e
  elabRExpr #[] #[] #[] p

--set_option pp.explicit true
#check [RiseE| fun as => as]
#check [RiseE| fun as => fun bs => (as bs)]
#check [RiseE| fun as => fun bs => as bs (fun c => c)]
#check [RiseE| fun as => as (fun as => as)]

#check [RiseE| fun x => x]

#check [RiseE| fun(x : nat) => 3]

-- trying to use x at term level. it's not legal,
-- because x is only in the kinding context
-- #check [RiseE| fun(x : nat) => x]

#check [RiseE| fun(x : 5 . float) => x]

#check [RiseE| fun(x : nat) => 3]

#check [RiseE| fun(n : nat) => fun(x : n . float) => x]
