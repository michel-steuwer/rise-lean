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
  -- | bvar (deBruijnIndex : Nat) (userName : String)
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

abbrev MVCtx := Array (Lean.Name × RKind × Option RType)
abbrev KCtx := Array (Lean.Name × Option RKind)
abbrev TCtx := Array (Lean.Name × Option RType)

abbrev MVarId := Nat

inductive SubstEnum
  | data (rdata : RData)
  | nat (rnat : RNat)

abbrev Substitution := List (MVarId × SubstEnum)

structure RContext where
  tctx : TCtx
  mctx : MVCtx
  -- debug : Bool := false
  -- depth : Nat := 0

structure RState where
  unifyResult : Substitution
  nextMVarId : MVarId

abbrev RElabM := ReaderT RContext <| StateRefT RState Lean.Elab.TermElabM


def liftToTermElabM' (ctx : RContext) (initialState : RState) (x : RElabM α) : Lean.Elab.TermElabM α := do
  let (result, _) ← x.run ctx |>.run initialState
  return result

def liftToTermElabM (x : RElabM α) : Lean.Elab.TermElabM α := do
  let ctx := { tctx := #[], mctx := #[]}
  let initialState := { unifyResult := [], nextMVarId := 0 }
  let (result, _) ← x.run ctx |>.run initialState
  return result

def getMVarId : RElabM MVarId := do
  let rstate : RState ← get
  set { rstate with nextMVarId := rstate.nextMVarId + 1 }
  return rstate.nextMVarId
