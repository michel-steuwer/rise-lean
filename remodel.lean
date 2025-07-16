
--   n ::= 0 | n + n | n · n | ...                   (Natural Number Literals, Binary Operations)
-- (definition omits identifiers)
 
inductive RiseNat
  | nat: Nat → RiseNat

  
-- --   κ ::= nat | data                                (Natural Number Kind, Datatype Kind)
-- --   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
--

  


--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RiseData : Type 1 where
  | array  : RiseData → Nat → RiseData
  | pair   : RiseData → RiseData → RiseData
  | index  : Nat → RiseData
  | scalar : RiseData
  | vector : Nat → RiseData

def RiseData.denote : RiseData → Type
  | RiseData.scalar => Float
  | RiseData.vector n => Fin n → Float
  | RiseData.index n => Fin n
  | RiseData.pair δ₁ δ₂ => δ₁.denote × δ₂.denote
  | RiseData.array δ n => Fin n → δ.denote

-- map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
axiom map : {n : Nat} → {δ₁ δ₂ : RiseData} → (δ₁.denote → δ₂.denote) → (δ₁.array n).denote → (δ₂.array n).denote 


-- TODO: hmm...
#reduce RiseData.denote $ RiseData.array (RiseData.array RiseData.scalar 4) 5 
---------------------------------------------------------------------------
-- ----------------------------------------


inductive RiseArray (α : Type _): Nat → Type _ where
  | mk : RiseArray α n
  
def RiseData.denote2 : RiseData → Type
  | RiseData.array δ n => RiseArray δ.denote2 n
  | _ => sorry
  -- | RiseData.scalar => Float
  -- | RiseData.vector n => Fin n → Float
  -- | RiseData.index n => Fin n
  -- | RiseData.pair δ₁ δ₂ => δ₁.denote2 × δ₂.denote2

-- inductive RiseKind
--   | nat
--   | data



-- inductive RiseType where
--   | any : RiseType
--   | data : RiseData → RiseType
--   | fn : RiseType → RiseType → RiseType
--   | dfn : (RiseData → RiseType) → RiseType
