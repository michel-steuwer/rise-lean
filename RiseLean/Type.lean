import Lean
import RiseLean.Prelude
open Lean Elab Meta Command

-- abbrev MVarCtx := Array (Name × Expr)


instance : ToString RKind where
  toString
    | RKind.nat => "nat"
    | RKind.data => "data"
    | RKind.type => "type"


declare_syntax_cat rise_kind
syntax "nat"                   : rise_kind
syntax "data"                  : rise_kind
syntax "[RiseK|" rise_kind "]" : term

macro_rules
  | `([RiseK| nat]) => `(RKind.nat)
  | `([RiseK| data]) => `(RKind.data)

partial def elabToRKind : Syntax -> TermElabM RKind
  | `(rise_kind| nat ) => return RKind.nat
  | `(rise_kind| data ) => return RKind.data
  | _ => throwUnsupportedSyntax

instance : ToExpr RKind where
  toExpr e := match e with
  | RKind.nat => mkConst ``RKind.nat
  | RKind.data => mkConst ``RKind.data
  | RKind.type => mkConst ``RKind.type
  toTypeExpr := mkConst ``RKind 
  


instance : ToString RNat where
  toString
    -- | RNat.bvar idx name => s!"{name}@{idx}"
    | RNat.mvar id name => s!"?{name}_{id}"
    | RNat.nat n => s!"{n}"

declare_syntax_cat rise_nat
syntax num                    : rise_nat
syntax ident                  : rise_nat

syntax "[RiseN|" rise_nat "]" : term

partial def elabToRNat (kctx : KCtx) (mctx : MVCtx) : Syntax → TermElabM RNat
  | `(rise_nat| $n:num) => return RNat.nat n.getNat
  | `(rise_nat| $x:ident) =>
    -- match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    -- | some idx =>
    --   return RNat.bvar idx x.getId.toString
    -- | none =>
      match mctx.reverse.findIdx? (λ (name, _, _) => name == x.getId) with
      | some idx =>
        return RNat.mvar idx x.getId.toString
      | none => throwErrorAt x s!"rnat: unknown identifier {mkConst x.getId}"
  | _ => throwUnsupportedSyntax

instance : ToExpr RNat where
  toExpr e := match e with
  -- | RNat.bvar deBruijnIndex userName =>
  --   let f := mkConst ``RNat.bvar
  -- mkAppN f #[mkNatLit deBruijnIndex, mkStrLit userName]
  | RNat.mvar id userName =>
    let f := mkConst ``RNat.mvar
    mkAppN f #[mkNatLit id, mkStrLit userName]
  | RNat.nat n =>
    let f := mkConst ``RNat.nat
    mkAppN f #[mkNatLit n]
  toTypeExpr := mkConst ``RNat 
  
partial def elabRNat (kctx : KCtx) (mctx : MVCtx) : Syntax → TermElabM Expr
  | stx => do
    let n ← elabToRNat kctx mctx stx
    return toExpr n



-- def RData.beq (a : RData) (b : RData) : Bool :=
--     match a, b with
--     | .bvar ia _, .bvar ib _ => ia == ib
--     | .mvar ia _, .mvar ib _ => true -- <- very likely incorrect :D -- ia == ib
--     | .array na da,.array nb db => na == nb && da.beq db
--     | .pair da1 da2,.pair db1 db2 => da1.beq db1 && da2.beq db2
--     | .index ia,.index ib => ia == ib
--     | .scalar, .scalar => true
--     | .vector na, .vector nb => na == nb
--     | _, _ => false

-- instance : BEq RData where
--   beq := RData.beq

def RData.toString : RData → String
  | RData.bvar idx name => s!"{name}@{idx}"
  | RData.mvar id name => s!"?{name}_{id}"
  | RData.array n d => s!"{n}.{RData.toString d}"
  | RData.pair d1 d2 => s!"{RData.toString d1} × {RData.toString d2}"
  | RData.index n => s!"idx[{n}]"
  | RData.scalar => "scalar"
  | RData.vector n => s!"{n}<float>"

instance : ToString RData where
  toString := RData.toString

declare_syntax_cat rise_data
syntax:50 rise_nat "." rise_data:50       : rise_data
syntax:50 "float"                         : rise_data
syntax:10 rise_data "×" rise_data         : rise_data
syntax ident                              : rise_data
syntax "idx" "[" rise_nat "]"          : rise_data -- TODO: weird error when using a var named idx in normal code. possible to scope syntax such that normal code is not affected? i was hoping that syntax_cat is doing that, but it's not.
syntax rise_nat "<" "float" ">"        : rise_data
syntax "(" rise_data ")"                  : rise_data

partial def elabToRData (kctx : KCtx) (mctx : MVCtx): Syntax → TermElabM RData
  | `(rise_data| float) => return RData.scalar

  | `(rise_data| $x:ident) =>
    match kctx.reverse.findIdx? (λ (name, _) => name == x.getId) with
    | some index =>
      return RData.bvar index x.getId.toString
    | none =>
      match mctx.reverse.findIdx? (λ (name, _, _) => name == x.getId) with
      | some index =>
        return RData.mvar index x.getId.toString
      | none => throwErrorAt x s!"rdata: unknown identifier {mkConst x.getId}"

  | `(rise_data| $n:rise_nat . $d:rise_data) => do
    let n ← elabToRNat kctx mctx n
    let d ← elabToRData kctx mctx d
    return RData.array n d

  | `(rise_data| $l:rise_data × $r:rise_data) => do
    let l ← elabToRData kctx mctx l
    let r ← elabToRData kctx mctx r
    return RData.pair l r

  | `(rise_data| idx [$n:rise_nat]) => do
    let n <- elabToRNat kctx mctx n
    return RData.index n

  | `(rise_data| $n:rise_nat < float >) => do
    let n <- elabToRNat kctx mctx n
    return RData.vector n

  | `(rise_data| ($d:rise_data)) =>
    elabToRData kctx mctx d

  | _ => throwUnsupportedSyntax

instance : ToExpr RData where
  toExpr := 
    let rec go : RData → Expr
    | RData.scalar => mkConst ``RData.scalar
    | RData.bvar deBruijnIndex userName =>
      mkAppN (mkConst ``RData.bvar) #[mkNatLit deBruijnIndex, mkStrLit userName]
    | RData.mvar id userName =>
      mkAppN (mkConst ``RData.mvar) #[mkNatLit id, mkStrLit userName]
    | RData.array n d =>
      mkAppN (mkConst ``RData.array) #[toExpr n, go d]
    | RData.pair l r =>
      mkAppN (mkConst ``RData.pair) #[go l, go r]
    | RData.index n =>
      mkAppN (mkConst ``RData.index) #[toExpr n]
    | RData.vector n =>
      mkAppN (mkConst ``RData.vector) #[toExpr n]
    go
  toTypeExpr := mkConst ``RData

partial def elabRData (kctx : KCtx) (mctx : MVCtx): Syntax → TermElabM Expr
  | stx => do
    let d ← elabToRData kctx mctx stx
    return toExpr d

instance : ToString Plicity where
  toString
    | Plicity.ex => "explicit"
    | Plicity.im => "implicit"

instance : ToExpr Plicity where
  toExpr e := match e with
  | Plicity.ex => mkConst ``Plicity.ex
  | Plicity.im => mkConst ``Plicity.im
  toTypeExpr := mkConst ``Plicity 
  

-- only for Check::infer! to be able to panic
instance : Inhabited RType where
  default := RType.data .scalar

def RType.toString : RType → String
  | RType.data dt => RData.toString dt
  | RType.upi kind pc un body =>
      let plicityStr := if pc == Plicity.im then "{" else "("
      let plicityEnd := if pc == Plicity.im then "}" else ")"
      s!"{plicityStr}{un} : {kind}{plicityEnd} → {RType.toString body}"
  | RType.pi binderType body => s!"{RType.toString binderType} → {RType.toString body}"

instance : ToString RType where
  toString := RType.toString


declare_syntax_cat rise_type
syntax rise_data                                  : rise_type
syntax rise_type "→" rise_type                    : rise_type
syntax "(" rise_type ")"                          : rise_type
syntax "{" ident+ ":" rise_kind "}" "→" rise_type : rise_type
syntax "(" ident ":" rise_kind ")" "→" rise_type  : rise_type

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



partial def elabToRType (kctx : KCtx) (mctx : MVCtx): Syntax → TermElabM RType
  | `(rise_type| $d:rise_data) => do
    let d ← elabToRData kctx mctx d
    return RType.data d
  | `(rise_type| $l:rise_type → $r:rise_type) => do
    let t ← elabToRType kctx mctx l
    let body ← elabToRType kctx mctx r
    return RType.pi t body
  | `(rise_type| ($t:rise_type)) => do
    elabToRType kctx mctx t
  | `(rise_type| {$x:ident : $k:rise_kind} → $t:rise_type) => do
    let k ← elabToRKind k
    let body ← elabToRType kctx (mctx.push (x.getId, k, none)) t
    return RType.upi k Plicity.im x.getId.toString body
  | `(rise_type| ($x:ident : $k:rise_kind) → $t:rise_type) => do
    let k ← elabToRKind k
    let body ← elabToRType (kctx.push (x.getId, some k)) mctx t
    return RType.upi k Plicity.ex x.getId.toString body
  | _ => throwUnsupportedSyntax

instance : ToExpr RType where
  toExpr := 
    let rec go : RType → Expr
    | RType.data d =>
      let f := mkConst ``RType.data
      mkAppN f #[toExpr d]
    | RType.upi binderKind pc userName body =>
      let f := mkConst ``RType.upi
      mkAppN f #[toExpr binderKind, toExpr pc, mkStrLit userName, go body]
    | RType.pi binderType body =>
      let f := mkConst ``RType.pi
      mkAppN f #[go binderType, go body]
    go
  toTypeExpr := mkConst ``RType 

  
partial def elabRType (kctx : KCtx) (mctx : MVCtx): Syntax → TermElabM Expr
  | stx => do
    let t ← elabToRType kctx mctx stx
    return toExpr t

elab "[RiseT|" t:rise_type "]" : term => do
  -- macros run before elab, but we still have to manually expand macros?
  let t ← liftMacroM <| expandMacros t
  let kctx : KCtx := #[]
  let mctx: MVCtx := #[]
  let term ← elabRType kctx mctx t
  return term


open PrettyPrinter Delaborator SubExpr
-- set_option pp.rawOnError true
@[app_unexpander RType.pi]
def unexpandRiseDataArray : Unexpander
  | `($(_) $l $r) => `($l → $r)
  | _ => throw ()


#check [RiseT| float]
#check [RiseT| float → float ]
#check [RiseT| {δ : data} → δ → δ → δ]
#check [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1]
#guard [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1] ==
  RType.upi RKind.data Plicity.im "δ1"
        (RType.upi RKind.data Plicity.im "δ2"
          ((RType.data ((RData.mvar 1 "δ1").pair (RData.mvar 0 "δ2"))).pi (RType.data (RData.mvar 1 "δ1"))))


#check [RiseT| {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n . δ1 → n . δ2]

def RData.ismvar : RData → Bool
  | .mvar .. => true
  | _ => false

def RNat.liftmvars (n : Nat) : RNat → RNat
  | .mvar id un => .mvar (id + n) un
  -- | .bvar id un => .bvar id un
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
  | .upi bk pc un b   => .upi bk pc un (b.liftmvars n)
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
  -- | .bvar _id _un, acc => acc
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
  | .upi _bk _pc _un b, acc   => b.getmvarsAux acc
  | .pi bt b, acc    => b.getmvarsAux (bt.getmvarsAux acc)
  | .data dt, acc    => dt.getmvarsAux acc

-- now have to deduplicate and sort. very silly approach but it works for now.
def RType.getmvars (t : RType) : Array (String × RKind) :=
  let sorted := (t.getmvarsAux #[]).qsort (fun (n1, _, _) (n2, _, _) => n1 ≤ n2)
  let deduped := sorted.foldl (fun acc x =>
    if acc.any (fun y => y == x) then acc else acc.push x) #[]
  deduped.map (fun (_, s, r) => (s, r))

#eval [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1].getmvars

def RType.countUniqueMVars : RType → Nat := (· |>.getmvars |>.size)
def RType.countUniqueMVars' : RType → Nat := Array.size ∘ RType.getmvars

-- def RType.subst (x : RType) (v : RType) (t : RType) : RType :=
--   match

def RData.substdata (x : RData) (v : RData) (t : RData) : RData :=
  match x with
  | .array n ad => if x == v then t else .array n (ad.substdata v t)
  | .pair l r => if x == v then t else .pair (l.substdata v t) (r.substdata v t)
  | _ => if x == v then t else x
  -- | .bvar
  -- | .mvar
  -- | .index
  -- | .scalar
  -- | .vector


-- x[v → t] -- should ignore username?
def RType.substdata (x : RType) (v : RData) (t : RData) : RType :=
  match x with
  | .data dt => if dt == v then .data t else .data <| dt.substdata v t
  | .upi bk pc un b => .upi bk pc un (b.substdata v t)
  | .pi bt b => .pi (bt.substdata v t) (b.substdata v t)


def RType.ismvardata : RType → Bool
  | .data (.mvar ..) => true
  | _ => false

-- def RType.tryUnifyData (x : RType) (t : RType) : RType :=
--   match x, t with
--   | .data m@(.mvar ..), .data .. => x.substdata m t
--   | _, _ => panic! s!"unexpected unify: {repr x} with {repr t}"

def RType.gettopmvar : RType → Option RData
  | .data m@(.mvar ..) => some m
  | _ => none

def RType.getRKind : RType → RKind
  | .data .. => .data
  | _ => .type -- not sure if correct
  -- never .nat? is my model wrong?
