
--   n ::= 0 | n + n | n · n | ...                   (Natural Number Literals, Binary Operations)
-- (definition omits identifiers)
 
inductive RiseNat
  | nat: Nat → RiseNat

  
--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
--

-- inductive RiseArray : Nat → Type _ where
  


inductive RiseData
  | array  : RiseNat → RiseData → RiseData
  | pair   : RiseData → RiseData → RiseData
  | index  : RiseNat → RiseData
  | scalar : RiseData
  | vector : RiseNat → RiseData

--   κ ::= nat | data                                (Natural Number Kind, Datatype Kind)
inductive RiseKind
  | nat
  | data



--   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
inductive RiseType where
  | any : RiseType
  | data : RiseData → RiseType
  | fn : RiseType → RiseType → RiseType
  | dfn : (RiseData → RiseType) → RiseType
