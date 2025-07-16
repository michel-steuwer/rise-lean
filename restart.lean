import Lean
open Lean Elab Meta Command

inductive RNat
  | nat: Nat → RNat

declare_syntax_cat rise_nat
syntax num                    : rise_nat
-- syntax ident                  : rise_nat

syntax "[RiseN|" rise_nat "]" : term

macro_rules
  | `([RiseN| $n:num]) => `(RNat.nat $n)
  -- | `([RiseN| $x:ident]) => `($x)

--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RData
  | array  : RNat → RData → RData
  | pair   : RData → RData → RData
  | index  : RNat → RData
  | scalar : RData
  | vector : RNat → RData

declare_syntax_cat rise_data
syntax:50 rise_nat "." rise_data:50       : rise_data
syntax:50 "float"                         : rise_data
syntax:10 rise_data "×" rise_data         : rise_data
syntax ident                              : rise_data
-- syntax "idx" "[" rise_nat "]"          : rise_data -- TODO: weird error when using a var named idx in normal code. possible to scope syntax such that normal code is not affected? i was hoping that syntax_cat is doing that, but it's not.
syntax "(" rise_data ")"                  : rise_data

syntax "[RiseD|" rise_data "]" : term

macro_rules
  | `([RiseD| float]) => `(RData.scalar)
  | `([RiseD| $x:ident]) => `($x)
  | `([RiseD| $n:rise_nat . $d:rise_data]) => `(RData.array [RiseN| $n] [RiseD| $d])
  | `([RiseD| $l:rise_data × $r:rise_data]) => `(RData.pair [RiseD| $l] [RiseD| $r])
  | `([RiseD| ($d:rise_data)]) => `([RiseD| $d])

--   κ ::= nat | data                                (Natural Number Kind, Datatype Kind)
inductive RKind
  | nat
  | data

declare_syntax_cat               rise_kind
syntax "nat"                   : rise_kind
syntax "data"                  : rise_kind
syntax "[RiseK|" rise_kind "]" : term

macro_rules
  | `([RiseK| nat]) => `(RKind.nat)
  | `([RiseK| data]) => `(RKind.data)

--   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
inductive RType where
  | bvar (debruijnIndex : Nat) (userName : Option String)
  | data (dt : RData)
  | pi (implicit : Bool) (body : RType) (binderType : RKind)

declare_syntax_cat                        rise_type
syntax rise_data                        : rise_type
syntax rise_type "→" rise_type : rise_type
syntax "(" rise_type ")" : rise_type
syntax "{" ident ":" "data" "}" "→" rise_type : rise_type
syntax "{" rise_nat ":" "nat" "}" "→" rise_type : rise_type
syntax "[RiseT|" rise_type "]"          : term


abbrev RKindingCtx := Array (Name × Expr)

partial def elabRType (kctx : RKindingCtx) : Syntax → TermElabM Expr
  | `(rise_type| $d:rise_data) => do
    let x ← `(RType.data [RiseD| $d])
    Term.elabTerm x none
  -- | `([RiseT| $l:rise_type → $r:rise_type]) => `(RType.fn [RiseT| $l] [RiseT| $r])
  -- | `([RiseT| ($t:rise_type)]) => `([RiseT| $t])
  | _ => throwError "hi"
  -- | _ => throwUnsupportedSyntax
  -- | `([RiseT| {$x:ident : $k:rise_kind} → $t:rise_type]) => `(fun $x => [RiseT| $t])
  -- | `([RiseT| {$x:ident : data} → $t:rise_type]) => `(RType.dfn fun {$x : RData} => [RiseT| $t])
  -- | `([RiseT| {$x:ident : nat} → $t:rise_type]) => `(RType._fn fun {$x : RNat} => [RiseT| $t])
      -- let x ← `([RiseN| $x])
  -- | `([RiseT| {$x:ident : $k:rise_kind} → $t:rise_type]) => `(fun ($x : [RiseK| $k]) => [RiseT| $t])

inductive RExpr where
  | bvar (deBruijnIndex : Nat) (userName : String)
  -- | const (declName : Name) (us : List VLevel)
  -- | prim (name : String)
  | lit (val : Nat)
  | app (fn arg : RExpr)

  | lam (body : RExpr) (binderType : Option RType)
  | ulam (body : RExpr) (binderType : Option RKind)

abbrev RTypingCtx := Array (Name × Option RType)

-- def dot : RExpr := .lam (.app (.app (.prim "reduce") (.prim "add")) (.lit 0))
-- def s : RExpr := .lam <| .lam (.app (.app
--                                       (.prim "plus")
--                                       (.bvar 0 "a"))
--                                     (.bvar 1 "b"))


declare_syntax_cat                         rise_expr
-- syntax rise_lit                          : rise_expr
syntax num : rise_expr
syntax ident                             : rise_expr
syntax "fun" "(" ident (":" rise_type)? "," rise_expr ")" : rise_expr
syntax "fun" "(" ident (":" rise_kind) "," rise_expr ")" : rise_expr
syntax rise_expr "(" rise_expr ")"       : rise_expr -- application
syntax rise_expr "|>" rise_expr          : rise_expr -- sugar for application


partial def elabRExpr (tctx : RTypingCtx) (kctx : RKindingCtx): Syntax → TermElabM Expr
  | `(rise_expr| $l:num) => do
    let x ← mkAppM ``RExpr.lit #[mkNatLit l.getNat]
    return x

  | `(rise_expr| $i:ident) => do
    match tctx.reverse.findIdx? (λ (name, _) => name == i.getId) with
    | some idx =>
      mkAppM ``RExpr.bvar #[mkNatLit <| idx, mkStrLit i.getId.toString]
    | none => throwErrorAt i s!"unknown identifier {mkConst i.getId}"
    -- | none =>
    --   match kctx.reverse.findIdx? (λ (name, _) => name == i.getId) with
    --   | some idx =>
    --     mkAppM ``RExpr.bvar #[mkNatLit <| idx, mkStrLit i.getId.toString]
    --   | none => throwErrorAt i s!"unknown identifier {mkConst i.getId}"

  | `(rise_expr| fun ( $x:ident , $b:rise_expr )) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) kctx b
    let none := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
    mkAppM ``RExpr.lam #[b, none]

  | `(rise_expr| fun ( $x:ident : $t:rise_type, $b:rise_expr )) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) kctx b
    -- let syntaxTerm : TSyntax `term ← `([RiseT| $t])
    -- let t ← Term.elabTerm syntaxTerm (some (mkConst ``RType))
    let t ← elabRType kctx t
    let some := mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RType, t]
    mkAppM ``RExpr.lam #[b, some]

  | `(rise_expr| fun ( $x:ident : $t:rise_kind, $b:rise_expr )) => do
    let syntaxTerm : TSyntax `term ← `([RiseK| $t])
    let t ← Term.elabTerm syntaxTerm none --(mkConst ``RKind) --(some (mkConst ``RType))
    let b ← elabRExpr tctx (kctx.push (x.getId, t)) b
    let some := mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RKind, t]
    -- let none := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
    mkAppM ``RExpr.ulam #[b, some]

  | `(rise_expr| $e1:rise_expr ( $e2:rise_expr )) => do
      let e1 ← elabRExpr tctx kctx e1
      let e2 ← elabRExpr tctx kctx e2
      mkAppM ``RExpr.app #[e1, e2]

  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f($e))
    elabRExpr tctx kctx s

  | _ => throwUnsupportedSyntax

elab "[Rise|" l:rise_expr "]" : term => do
  let tctx : RTypingCtx := #[
    ("map", none),
    ("reduce", none),
    ("zip", none),
    ("add", none),
    ("mult", none),
    ("fst", none),
    ("snd", none)
  ].map (fun (n, t) => (n.toName, t))

  let kctx : RKindingCtx := #[]

  let term ← elabRExpr tctx kctx l
  return term

--set_option pp.explicit true
#check [Rise| fun(as, as)]
#check [Rise| fun(as, fun(bs, as(bs)))]
#check [Rise| fun(as, fun(bs, as(bs (fun(c, c)))))]
#check [Rise| fun(as, as (fun(as, as)))]
-- #check [Rise| map(reduce(zip(filter)))]

#check [Rise|

fun(as, fun(bs,
     zip(as)(bs) |> map(fun(ab, mult(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )

]

#check [Rise| fun(x : float, x)]

#check [Rise| fun(x : nat, 3)]

-- trying to use x at term level. it's not legal,
-- because x is only in the kinding context
-- #check [Rise| fun(x : nat, x)]

#check [Rise| fun(x : 5 . float, x)]

#check [Rise| fun(n : nat, fun(x : n . float, x)]

#check [Rise| fun(n : nat, fun(a : k . float, reduce(add)(0)(a)))]
