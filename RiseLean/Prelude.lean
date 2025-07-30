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
  | bvar (deBruijnIndex : Nat) (userName : String)
  | mvar (id : Nat) (userName : String)
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
  | upi (binderKind : RKind) (pc : Plicity) (userName : String) (body : RType)
  | pi (binderType : RType) (body : RType)
deriving Repr, BEq


inductive RExpr where
  | bvar (deBruijnIndex : Nat) (userName : String)
-- fvar
-- mvar
  | lit (val : Nat)
  | app (fn arg : RExpr)

  | lam (binderType : Option RType) (body : RExpr)
  | ulam (binderKind : Option RKind) (body : RExpr)
deriving Repr

abbrev MVCtxElem := Lean.Name × RKind × Option RType
abbrev MVCtx := Array MVCtxElem

abbrev KCtxElem := Lean.Name × Option RKind
abbrev KCtx := Array KCtxElem

abbrev TCtxElem := Lean.Name × Option RType
abbrev TCtx := Array TCtxElem


abbrev MVarId := Nat

inductive SubstEnum
  | data (rdata : RData)
  | nat (rnat : RNat)

abbrev Substitution := List (MVarId × SubstEnum)


structure RContext where
  tctx : TCtx
  kctx : KCtx
  mctx : MVCtx
  -- debug : Bool := false
  -- depth : Nat := 0

structure RState where
  unifyResult : Substitution
  nextMVarId : MVarId

abbrev RElabM := ReaderT RContext <| StateRefT RState Lean.Elab.TermElabM

def defaultState : RState := { unifyResult := [], nextMVarId := 0 }
def defaultContext : RContext := { tctx := #[], mctx := #[], kctx := #[]}

def liftToTermElabMWith (ctx : RContext) (initialState : RState) (x : RElabM α) : Lean.Elab.TermElabM α := do
  let (result, _) ← x.run ctx |>.run initialState
  return result

def liftToTermElabM (x : RElabM α) : Lean.Elab.TermElabM α := do
  let (result, _) ← x.run defaultContext |>.run defaultState
  return result

def getMVarId : RElabM MVarId := do
  let rstate : RState ← get
  set { rstate with nextMVarId := rstate.nextMVarId + 1 }
  return rstate.nextMVarId

def withNewTerm (arg : TCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with tctx := ctx.tctx.push arg })

def withNewMVar (arg : MVCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with mctx := ctx.mctx.push arg })

def withNewMVCTx (f : MVCtx → MVCtx) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with mctx := f ctx.mctx })

def withNewType (arg : KCtxElem) : RElabM α → RElabM α :=
  withReader (fun ctx => { ctx with kctx := ctx.kctx.push arg })

def getTCtx : RElabM TCtx := do
  return (← read).tctx

def getKCtx : RElabM KCtx := do
  return (← read).kctx

def getMVCtx : RElabM MVCtx := do
  return (← read).mctx
