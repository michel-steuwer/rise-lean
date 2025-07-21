import Lean
open Lean Elab Meta Command

abbrev RKindingCtx := Array (Name × Expr)
abbrev MVarCtx := Array (Name × Expr)


--   κ ::= nat | data                                (Natural Number Kind, Datatype Kind)
inductive RKind
  | nat
  | data
deriving BEq, Hashable, Repr

--   n ::= 0 | n + n | n · n | ...                   (Natural Number Literals, Binary Operations)
inductive RNat
  | bvar (deBruijnIndex : Nat) (userName : String)
  | mvar (id : Nat) (userName : String)
  | nat: Nat → RNat
deriving Repr, BEq

--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RData
  | bvar (deBruijnIndex : Nat) (userName : String)
  | mvar (id : Nat) (userName : String)
  | array  : RNat → RData → RData
  | pair   : RData → RData → RData
  | index  : RNat → RData
  | scalar : RData
  | vector : RNat → RData
deriving Repr, BEq

inductive Plicity
  | ex
  | im
deriving Repr, BEq

--   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
inductive RType where
  | data (dt : RData)
  -- do we need this distinction? yes, but we could do these cases with universe level. would need a RType.sort variant though
  | upi (binderKind : RKind) (pc : Plicity) (body : RType)
  | pi (binderType : RType) (body : RType)
deriving Repr, BEq

-- only for Check::infer! to be able to panic
instance : Inhabited RType where
  default := RType.data .scalar

declare_syntax_cat               rise_kind
syntax "nat"                   : rise_kind
syntax "data"                  : rise_kind
syntax "[RiseK|" rise_kind "]" : term

macro_rules
  | `([RiseK| nat]) => `(RKind.nat)
  | `([RiseK| data]) => `(RKind.data)

declare_syntax_cat rise_nat
syntax num                    : rise_nat
syntax ident                  : rise_nat

syntax "[RiseN|" rise_nat "]" : term

partial def elabRNat (kctx : RKindingCtx) (mctx : MVarCtx) : Syntax → TermElabM Expr
  | `(rise_nat| $n:num) => mkAppM ``RNat.nat #[mkNatLit n.getNat]
  | `(rise_nat| $x:ident) =>
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some idx =>
      mkAppM ``RNat.bvar #[mkNatLit <| idx, mkStrLit x.getId.toString]
    | none =>
      match mctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
      | some idx =>
        mkAppM ``RNat.mvar #[mkNatLit <| idx, mkStrLit x.getId.toString]
      | none => throwErrorAt x s!"unknown identifier {mkConst x.getId}"
  | _ => throwUnsupportedSyntax

-- macro_rules
  -- | `([RiseN| $n:num]) => `(RNat.nat $n)
--  | `([RiseN| $x:ident]) => `($x)


declare_syntax_cat rise_data
syntax:50 rise_nat "." rise_data:50       : rise_data
syntax:50 "float"                         : rise_data
syntax:10 rise_data "×" rise_data         : rise_data
syntax ident                              : rise_data
syntax "idx" "[" rise_nat "]"          : rise_data -- TODO: weird error when using a var named idx in normal code. possible to scope syntax such that normal code is not affected? i was hoping that syntax_cat is doing that, but it's not.
syntax "(" rise_data ")"                  : rise_data

syntax "[RiseD|" rise_data "]" : term

partial def elabRData (kctx : RKindingCtx) (mctx : MVarCtx): Syntax → TermElabM Expr
  | `(rise_data| float) =>
    return mkConst ``RData.scalar

  | `(rise_data| $x:ident) =>
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some index =>
      mkAppM ``RData.bvar #[mkNatLit <| index, mkStrLit x.getId.toString]
    | none =>
      match mctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
      | some index =>
        mkAppM ``RData.mvar #[mkNatLit <| index, mkStrLit x.getId.toString]
      | none => throwErrorAt x s!"unknown identifier {mkConst x.getId}"

  | `(rise_data| $n:rise_nat . $d:rise_data) => do
    let n ← elabRNat kctx mctx n
    let d ← elabRData kctx mctx d
    mkAppM ``RData.array #[n, d]

  | `(rise_data| $l:rise_data × $r:rise_data) => do
    let l ← elabRData kctx mctx l
    let r ← elabRData kctx mctx r
    mkAppM ``RData.pair #[l, r]

  | `(rise_data| idx [$n:rise_nat]) => do
    let n <- elabRNat kctx mctx n
    mkAppM ``RData.index #[n]

  | `(rise_data| ($d:rise_data)) =>
    elabRData kctx mctx d

  | _ => throwUnsupportedSyntax



  -- | mvar (id : Nat) (userName : String) (kind : RKind)
  -- | bvar (debruijnIndex : Nat) (userName : String)


declare_syntax_cat                        rise_type
syntax rise_data                                 : rise_type
syntax rise_type "→" rise_type                   : rise_type
syntax "(" rise_type ")"                         : rise_type
syntax "{" ident+ ":" rise_kind "}" "→" rise_type : rise_type
syntax "(" ident ":" rise_kind ")" "→" rise_type : rise_type

syntax "[RiseT|" rise_type "]"          : term

-- set_option pp.raw true
-- set_option pp.raw.maxDepth 10


-- i bet this could be written nicer
macro_rules
  | `(rise_type| {$x:ident $y:ident $xs:ident* : $k:rise_kind} → $t:rise_type) =>
    match xs with
    | #[] =>
      `(rise_type| {$x : $k} → {$y : $k} → $t)
    | _ =>
      `(rise_type| {$x : $k} → {$y : $k} → {$xs* : $k} → $t)

partial def elabRType (kctx : RKindingCtx) (mctx : MVarCtx): Syntax → TermElabM Expr
  | `(rise_type| $d:rise_data) => do
    let d ← elabRData kctx mctx d
    mkAppM ``RType.data #[d]
  | `(rise_type| $l:rise_type → $r:rise_type) => do
    let t ← elabRType kctx mctx l
    let body ← elabRType kctx mctx r
    mkAppM ``RType.pi #[t, body]
  | `(rise_type| ($t:rise_type)) => do
    elabRType kctx mctx t
  | `(rise_type| {$x:ident : $k:rise_kind} → $t:rise_type) => do
    let k ← `([RiseK| $k])
    let k ← Term.elabTerm k none
    let body ← elabRType kctx (mctx.push (x.getId,k)) t
    mkAppM ``RType.upi #[k, mkConst ``Plicity.im, body]
  | `(rise_type| ($x:ident : $k:rise_kind) → $t:rise_type) => do
    let k ← `([RiseK| $k])
    let k ← Term.elabTerm k none
    let body ← elabRType (kctx.push (x.getId,k)) mctx t
    mkAppM ``RType.upi #[k, mkConst ``Plicity.ex, body]
  | l => dbg_trace l
      throwError "elab"


elab "[RiseT|" l:rise_type "]" : term => do
  -- macros run before elab, but we still have to manually expand macros?
  let l ← liftMacroM <| expandMacros l
  let kctx : RKindingCtx := #[]
  let mctx: MVarCtx := #[]
  let term ← elabRType kctx mctx l
  return term


  
#check [RiseT| float]
#check [RiseT| {δ : data} → δ → δ → δ]
#check [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1] 
#guard [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1] == 
  RType.upi RKind.data Plicity.im
        (RType.upi RKind.data Plicity.im
          ((RType.data ((RData.mvar 1 "δ1").pair (RData.mvar 0 "δ2"))).pi (RType.data (RData.mvar 1 "δ1"))))

def RNat.liftmvars (n : Nat) : RNat → RNat
  | .mvar id un => .mvar (id + n) un
  | .bvar id un => .bvar id un
  | .nat k      => .nat k

def RData.liftmvars (n : Nat) : RData → RData
  | .bvar n un  => .bvar n un
  | .mvar id un => .mvar (id + n) un
  | .array k d  => .array (k.liftmvars n) (d.liftmvars n)
  | .pair l r   => .pair (l.liftmvars n) (r.liftmvars n)
  | .index k    => .index (k.liftmvars n)
  | .scalar     => .scalar
  | .vector k   => .vector (k.liftmvars n)

def RType.liftmvars (n : Nat) : RType → RType
  | .upi bk pc b   => .upi bk pc (b.liftmvars n)
  | .pi bt b    => .pi (bt.liftmvars n) (b.liftmvars n)
  | .data dt    => .data (dt.liftmvars n)



-- def RNat.mapMVars (f : Nat → String → (Nat × String)) : RNat → RNat
--   | .mvar id un => let (nId, nUn) := f(id un); .mvar nId nUn
--   | .bvar id un => .bvar id un
--   | .nat k      => .nat k

-- def RData.mapMVars (f : Nat → String → (Nat × String) ) : RData → RData
--   | .bvar n un  => .bvar n un
--   | .mvar id un => .mvar (id + n) un
--   | .array k d  => .array (k.mapMVars n) (d.mapMVars n)
--   | .pair l r   => .pair (l.mapMVars n) (r.mapMVars n)
--   | .index k    => .index (k.mapMVars n)
--   | .scalar     => .scalar
--   | .vector k   => .vector (k.mapMVars n)

-- def RType.mapMVars (f : Nat → String → (Nat × String) ) : RType → RType
--   | .upi bk b   => .upi bk (b.mapMVars n)
--   | .pi bt b    => .pi (bt.mapMVars n) (b.mapMVars n)
--   | .data dt    => .data (dt.mapMVars n)

  
#reduce [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1].liftmvars 5


private def RNat.getmvarsAux : RNat → Array (Nat × String × RKind) → Array (Nat × String × RKind)
  | .mvar id un, acc => acc.push (id, un, .nat)
  | .bvar _id _un, acc => acc
  | .nat _k, acc      => acc

private def RData.getmvarsAux : RData → Array (Nat × String × RKind) → Array (Nat × String × RKind)
  | .bvar _n _un, acc  => acc
  | .mvar id un, acc => acc.push (id, un, .data)
  | .array k d, acc  => d.getmvarsAux (k.getmvarsAux acc)
  | .pair l r, acc   => r.getmvarsAux (l.getmvarsAux acc)
  | .index k, acc    => k.getmvarsAux acc
  | .scalar, acc     => acc
  | .vector k, acc   => k.getmvarsAux acc


private def RType.getmvarsAux : RType → Array (Nat × String × RKind) → Array (Nat × String × RKind)
  | .upi _bk _pc b, acc   => b.getmvarsAux acc
  | .pi bt b, acc    => b.getmvarsAux (bt.getmvarsAux acc)
  | .data dt, acc    => dt.getmvarsAux acc

-- now have to deduplicate and sort. very silly approach but it works for now.
def RType.getmvars (t : RType) : Array (String × RKind) :=
  let sorted := (t.getmvarsAux #[]).qsort (fun (n1, _, _) (n2, _, _) => n1 ≤ n2)
  let deduped := sorted.foldl (fun acc x => 
    if acc.any (fun y => y == x) then acc else acc.push x) #[]
  deduped.map (fun (_, s, r) => (s, r))

#eval [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1].getmvars

