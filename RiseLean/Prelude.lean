import Lean

--
-- Kind
--   κ ::= nat | data (Natural Number Kind, Datatype Kind)
inductive RKind
  | nat
  | data
  | type
  -- | etc
deriving BEq, Hashable, Repr

-- Nat
--   n ::= 0 | n + n | n · n | ... (Natural Number Literals, Binary Operations)
inductive RNat
  | bvar (deBruijnIndex : Nat) (userName : String)
  | mvar (id : Nat) (userName : String)
  | nat: Nat → RNat
deriving Repr, BEq, DecidableEq

-- DataType
--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RData
  | bvar (deBruijnIndex : Nat) (userName : Lean.Name)
  | mvar (id : Nat) (userName : Lean.Name)
  | array  : RNat → RData → RData
  | pair   : RData → RData → RData
  | index  : RNat → RData
  | scalar : RData
  | vector : RNat → RData
deriving Repr, BEq

-- Im-/ex-plicity of parameters
inductive Plicity
  | ex
  | im
deriving Repr, BEq

-- Types
--   τ ::= δ | τ → τ | (x : κ) → τ (Data Type, Function Type, Dependent Function Type)
inductive RType where
  | data (dt : RData)
  -- do we need this distinction? yes, but we could do these cases with universe level. would need a RType.sort variant though
  | upi (binderKind : RKind) (pc : Plicity) (userName : Lean.Name) (body : RType)
  | pi (binderType : RType) (body : RType)
deriving Repr, BEq


inductive RExpr where
  | bvar (deBruijnIndex : Nat)
  | fvar (userName : Lean.Name) -- this is a problem when multiple idents have the same name?
-- mvar
  | const (userName : Lean.Name)
  | lit (val : Nat)
  | app (fn arg : RExpr)

  | lam (binderName : Lean.Name) (binderType : Option RType) (body : RExpr)
  | ulam (binderName : Lean.Name) (binderKind : Option RKind) (body : RExpr)
deriving Repr

-- abbrev MVCtxElem := Lean.Name × RKind × Option RType
-- abbrev MVCtx := Array MVCtxElem

abbrev KCtxElem := Lean.Name × Option RKind
abbrev KCtx := Array KCtxElem

abbrev TCtxElem := Lean.Name × Option RType
abbrev TCtx := Array TCtxElem

structure MetaVarDeclaration where
  userName : Lean.Name := Lean.Name.anonymous
  kind : RKind
  type : Option RType := none

abbrev RMVarId := Nat
abbrev RBVarId := Nat

-- def f : RMVarId → Nat := (·)
-- def x : BVarId := 0
-- example : Nat := f x


inductive SubstEnum
  | data (rdata : RData)
  | nat (rnat : RNat)

abbrev Substitution := List (RMVarId × SubstEnum)



def RNat.substNat (t : RNat) (x : RMVarId) (s : RNat) : RNat :=
    match t with
    | .mvar y _ => if x == y then s else t
    | .bvar .. => t
    | .nat _ => t

def RNat.subst (t : RNat) (x : RMVarId) (s : SubstEnum) : RNat :=
  match s with
  | .data _ => t
  | .nat s => t.substNat x s

def RData.substNat (t : RData) (x : RMVarId) (s : RNat) : RData :=
  match t with
  | .mvar .. => t
  | .array k d => .array (k.substNat x s) d
  | .pair l r => .pair (l.substNat x s) (r.substNat x s)
  | .bvar id un => .bvar id un
  | .index k => .index (k.substNat x s)
  | .scalar => .scalar
  | .vector k => .vector (k.substNat x s)

def RData.substData (t : RData) (x : RMVarId) (s : RData) : RData :=
  match t with
  | .mvar y _ => if x == y then s else t
  | .array k d => .array k (d.substData x s)
  | .pair l r => .pair (l.substData x s) (r.substData x s)
  | .bvar id un => .bvar id un
  | .index k => .index k
  | .scalar => .scalar
  | .vector k => .vector k

def RData.subst (t : RData) (x : RMVarId) (s : SubstEnum) : RData :=
  match s with
  | .data s => t.substData x s
  | .nat s => t.substNat x s

def RType.substNat (t : RType) (x : RMVarId) (s : RNat) : RType :=
  match t with
  | .data dt => .data (dt.substNat x s)
  | .upi bk pc un body => .upi bk pc un (body.substNat x s)
  | .pi binderType body => .pi (binderType.substNat x s) (body.substNat x s)

def RType.substData (t : RType) (x : RMVarId) (s : RData) : RType :=
  match t with
  | .data dt => .data (dt.substData x s)
  | .upi bk pc un body => .upi bk pc un (body.substData x s)
  | .pi binderType body => .pi (binderType.substData x s) (body.substData x s)

def RType.subst (t : RType) (x : RMVarId) (s : SubstEnum) : RType :=
  match s with
  | .data s => t.substData x s
  | .nat s => t.substNat x s

def RNat.has (v : RMVarId) : RNat → Bool
  | .mvar id _ => id == v
  | .bvar .. => false
  | .nat _ => false

def RData.has (v : RMVarId) : RData → Bool
  | .mvar id _ => id == v
  | .bvar .. => false
  | .array _ d => d.has v
  | .pair l r => l.has v || r.has v
  | .index .. => false
  | .scalar => false
  | .vector .. => false

def RNat.apply (t : RNat) (subst : Substitution) : RNat :=
  subst.foldr (fun (id, replacement) acc => acc.subst id replacement) t

def RData.apply (t : RData) (subst : Substitution) : RData :=
  subst.foldr (fun (id, replacement) acc => acc.subst id replacement) t

def RType.apply (t : RType) (subst : Substitution) : RType :=
  subst.foldr (fun (id, replacement) acc => acc.subst id replacement) t

structure RContext where
  gtctx : TCtx := #[]
  ltctx : TCtx := #[]
  kctx : KCtx := #[]
  -- mctx : MVCtx
  -- debug : Bool := false
  -- depth : Nat := 0

structure RState where
  unifyResult : Substitution := []
  nextMVarId : RMVarId := 0
  mvars : Lean.PersistentHashMap RMVarId MetaVarDeclaration := {}

abbrev RElabM := ReaderT RContext <| StateRefT RState Lean.Elab.TermElabM

def defaultState : RState := {}
def defaultContext : RContext := {}

def liftToTermElabMWith (ctx : RContext) (initialState : RState) (x : RElabM α) : Lean.Elab.TermElabM α := do
  let (result, _) ← x.run ctx |>.run initialState
  return result

def liftToTermElabM (x : RElabM α) : Lean.Elab.TermElabM α := do
  let (result, _) ← x.run defaultContext |>.run defaultState
  return result

def getFreshMVarId : RElabM RMVarId := do
  let rstate : RState ← get
  set { rstate with nextMVarId := rstate.nextMVarId + 1 }
  return rstate.nextMVarId

def addMVar (id : RMVarId) (userName : Lean.Name) (kind : RKind) (type : Option RType := none) : RElabM Unit := do
  let rstate : RState ← get
  set { rstate with mvars := rstate.mvars.insert id { userName, kind, type } }
  return ()

def findMVar? (id : RMVarId) : RElabM <| Option MetaVarDeclaration := do
  let rstate : RState ← get
  return rstate.mvars.find? id

def addSubst (s : Substitution) : RElabM Unit := do
  modify (λ r => {r with unifyResult := s ++ r.unifyResult})

def applyUnifyResults (t : RType) : RElabM RType := do
  let unifyResults : Substitution := (← get).unifyResult
  return t.apply unifyResults

def withNewLocalTerm (arg : TCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with ltctx := ctx.ltctx.push arg })

def withNewGlobalTerm (arg : TCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with gtctx := ctx.gtctx.push arg })

def findConst? (n : Lean.Name) : RElabM <| Option RType := do
  let gtctx := (← read).gtctx
  return match gtctx.find? (λ (name, _) => name == n) with
  | some (_, rtype) => rtype
  | none => none

def findLocal? (n : Lean.Name) : RElabM <| Option RType := do
  let ltctx := (← read).ltctx
  return match ltctx.find? (λ (name, _) => name == n) with
  | some (_, rtype) => rtype
  | none => none

def ur : RElabM Substitution := do
  return (← get).unifyResult


def withNewTVar (arg : KCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with kctx := ctx.kctx.push arg })

-- def withNewMVCTx (f : MVCtx → MVCtx) : RElabM α → RElabM α :=
-- withReader (fun ctx => { ctx with mctx := f ctx.mctx })

def withNewType (arg : KCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with kctx := ctx.kctx.push arg })

def getLTCtx : RElabM TCtx := do
  return (← read).ltctx

def getGTCtx : RElabM TCtx := do
  return (← read).gtctx

def getKCtx : RElabM KCtx := do
  return (← read).kctx

-- def getMVCtx : RElabM MVCtx := do
-- return (← read).mctx
