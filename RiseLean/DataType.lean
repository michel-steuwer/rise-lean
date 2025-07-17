import Lean
open Lean Elab Meta Command

abbrev RKindingCtx := Array (Name × Expr)


inductive RNat
  | bvar (deBruijnIndex : Nat) (userName : String)
  | nat: Nat → RNat

declare_syntax_cat rise_nat
syntax num                    : rise_nat
syntax ident                  : rise_nat

syntax "[RiseN|" rise_nat "]" : term

partial def elabRNat (kctx : RKindingCtx) : Syntax → TermElabM Expr
  | `(rise_nat| $n:num) => mkAppM ``RNat.nat #[mkNatLit n.getNat]
  | `(rise_nat| $x:ident) =>
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some idx =>
      mkAppM ``RNat.bvar #[mkNatLit <| idx, mkStrLit x.getId.toString]
    | none => throwErrorAt x s!"unknown identifier {mkConst x.getId}"
  | _ => throwUnsupportedSyntax

-- macro_rules
  -- | `([RiseN| $n:num]) => `(RNat.nat $n)
--  | `([RiseN| $x:ident]) => `($x)

--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RData
  | bvar (deBruijnIndex : Nat) (userName : String)
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

-- macro_rules
--   | `([RiseD| float]) => `(RData.scalar)
--   | `([RiseD| $x:ident]) => `($x)
--   | `([RiseD| $n:rise_nat . $d:rise_data]) => `(RData.array [RiseN| $n] [RiseD| $d])
--   | `([RiseD| $l:rise_data × $r:rise_data]) => `(RData.pair [RiseD| $l] [RiseD| $r])
--   | `([RiseD| ($d:rise_data)]) => `([RiseD| $d])

partial def elabRData (kctx : RKindingCtx) : Syntax → TermElabM Expr
  | `(rise_data| float) =>
    return mkConst ``RData.scalar

  | `(rise_data| $x:ident) =>
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some idx =>
      mkAppM ``RData.bvar #[mkNatLit <| idx, mkStrLit x.getId.toString]
    | none => throwErrorAt x s!"unknown identifier {mkConst x.getId}"

  | `(rise_data| $n:rise_nat . $d:rise_data) => do
    let nExpr ← elabRNat kctx n
    let dExpr ← elabRData kctx d
    return mkApp2 (mkConst ``RData.array) nExpr dExpr

  | `(rise_data| $l:rise_data × $r:rise_data) => do
    let lExpr ← elabRData kctx l
    let rExpr ← elabRData kctx r
    return mkApp2 (mkConst ``RData.pair) lExpr rExpr

  | `(rise_data| ($d:rise_data)) =>
    elabRData kctx d

  | _ => throwUnsupportedSyntax

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



partial def elabRType (kctx : RKindingCtx) : Syntax → TermElabM Expr
  | `(rise_type| $d:rise_data) => do
    let d ← elabRData kctx d
    mkAppM ``RType.data #[d]
  -- | `([RiseT| $l:rise_type → $r:rise_type]) => `(RType.fn [RiseT| $l] [RiseT| $r])
  -- | `([RiseT| ($t:rise_type)]) => `([RiseT| $t])
  | _ => throwError "hi"
  -- | _ => throwUnsupportedSyntax
  -- | `([RiseT| {$x:ident : $k:rise_kind} → $t:rise_type]) => `(fun $x => [RiseT| $t])
  -- | `([RiseT| {$x:ident : data} → $t:rise_type]) => `(RType.dfn fun {$x : RData} => [RiseT| $t])
  -- | `([RiseT| {$x:ident : nat} → $t:rise_type]) => `(RType._fn fun {$x : RNat} => [RiseT| $t])
      -- let x ← `([RiseN| $x])
  -- | `([RiseT| {$x:ident : $k:rise_kind} → $t:rise_type]) => `(fun ($x : [RiseK| $k]) => [RiseT| $t])
