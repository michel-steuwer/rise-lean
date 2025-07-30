import RiseLean.Prelude
import RiseLean.Type
import Lean
open Lean Elab Meta


declare_syntax_cat rise_expr
syntax num                                                  : rise_expr
syntax ident                                                : rise_expr
syntax "fun" "(" ident (":" rise_type)? ")" "=>" rise_expr  : rise_expr
syntax "fun"     ident (":" rise_type)?     "=>" rise_expr  : rise_expr
syntax "fun" "(" ident (":" rise_kind)  ")" "=>" rise_expr  : rise_expr
syntax:50 rise_expr:50 rise_expr:51                         : rise_expr
syntax:40 rise_expr:41 "|>" rise_expr:40                    : rise_expr
syntax:60 "(" rise_expr ")"                                 : rise_expr

partial def elabToRExpr : Syntax → RElabM RExpr
  | `(rise_expr| $l:num) => do
    return RExpr.lit l.getNat

  | `(rise_expr| $i:ident) => do
    let tctx ← getTCtx
    match tctx.reverse.findIdx? (λ (name, _) => name == i.getId) with
      | some index =>
        return RExpr.bvar index i.getId.toString
      -- could give a hint here if we find the identifier in the kinding context.
      | none => throwErrorAt i s!"unknown identifier {i.getId}"

  | `(rise_expr| fun $x:ident => $b:rise_expr )
  | `(rise_expr| fun ($x:ident) => $b:rise_expr ) => do
    let b ← withNewTerm (x.getId, none) do elabToRExpr b
    return RExpr.lam none b

  | `(rise_expr| fun $x:ident : $t:rise_type => $b:rise_expr )
  | `(rise_expr| fun ( $x:ident : $t:rise_type ) => $b:rise_expr ) => do
    let b ← withNewTerm (x.getId, none) do elabToRExpr b
    let t ← elabToRType t
    return RExpr.lam (some t) b

  | `(rise_expr| fun ( $x:ident : $k:rise_kind ) => $b:rise_expr ) => do
    let k ← elabToRKind k
    let b ← withNewMVar (x.getId, k, none) do elabToRExpr b
    return RExpr.ulam (some k) b

  | `(rise_expr| $e1:rise_expr $e2:rise_expr ) => do
      let e1 ← elabToRExpr e1
      let e2 ← elabToRExpr e2
      return RExpr.app e1 e2

  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f $e)
    elabToRExpr s

  | `(rise_expr| ( $e:rise_expr )) => do
    let s ← `(rise_expr| $e)
    elabToRExpr s

  | _ => throwUnsupportedSyntax

instance : ToExpr RExpr where
  toExpr :=
    let rec go : RExpr → Expr
    | RExpr.lit n =>
        mkAppN (mkConst ``RExpr.lit) #[mkNatLit n]
    | RExpr.bvar index name =>
        mkAppN (mkConst ``RExpr.bvar) #[mkNatLit index, mkStrLit name]
    | RExpr.lam tyOpt body =>
        let bodyExpr := go body
        let tyOptExpr := match tyOpt with
          | none => mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
          | some ty => mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RType, toExpr ty]
        mkAppN (mkConst ``RExpr.lam) #[tyOptExpr, bodyExpr]
    | RExpr.ulam kindOpt body =>
        let bodyExpr := go body
        let kindOptExpr := match kindOpt with
          | none => mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RKind)
          | some kind => mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RKind, toExpr kind]
        mkAppN (mkConst ``RExpr.ulam) #[kindOptExpr, bodyExpr]
    | RExpr.app e1 e2 =>
        mkAppN (mkConst ``RExpr.app) #[go e1, go e2]
    go
  toTypeExpr := mkConst ``RExpr

def elabRExpr (stx : Syntax) : RElabM Expr := do
  let rexpr ← elabToRExpr stx
  return toExpr rexpr

elab "[RiseE|" e:rise_expr "]" : term => do
  let p ← liftMacroM <| expandMacros e
  liftToTermElabM <| elabRExpr p

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

-- TODO: do we want to parse this as n being an implicit parameter?
#check [RiseE| fun(n : nat) => fun(x : n . float) => x]
