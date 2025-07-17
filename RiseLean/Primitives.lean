import RiseLean.DataType

-- High-Level Primitives:
inductive RiseHighLevelPrimitive
--         id : {δ : data} → δ → δ
  |        id : RiseData → RiseData → RiseHighLevelPrimitive
--        add : {δ : data} → δ → δ → δ
  |       add : RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--       mult : {δ : data} → δ → δ → δ
  |      mult : RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--       todo : {δ : data} → δ → δ → δ
  |      todo : RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--        fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
  |       fst : RiseData → RiseData → RiseHighLevelPrimitive
--        snd : {δ1 δ2 : data} → δ1 × δ2 → δ2
  |       snd : RiseData → RiseData → RiseHighLevelPrimitive
--        map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
  |       map : (RiseData → RiseData) → RiseData → RiseData  → RiseHighLevelPrimitive
--     reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n.δ → δ
  |    reduce : (RiseData → RiseData → RiseData) → RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--        zip : {n : nat} → {δ1 δ2 : data} → n.δ1 → n.δ2 → n.(δ1 × δ2)
  |       zip : RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--      split : (n : nat) → {m : nat} → {δ : data} → nm.δ → n.m.δ
  |     split : RiseData → RiseData → RiseHighLevelPrimitive
--       join : {n m : nat} → {δ : data} → n.m.δ → nm.δ
  |      join : RiseData → RiseData → RiseHighLevelPrimitive
--  transpose : {n m : nat} → {δ : data} → n.m.δ → m.n.δ
  | transpose : RiseData → RiseData → RiseHighLevelPrimitive
--   generate : {n : nat} → {δ : data} → (idx [n] → δ) → n.δ
  |  generate : (RiseData → RiseData) → RiseData → RiseHighLevelPrimitive

-- Low-Level Primitives:
inductive RiseLowLevelPrimitive
--           mapSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
  |          mapSeq : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
--     mapSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
  |    mapSeqUnroll : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
--           mapPar : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
  |          mapPar : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
--        reduceSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
  |       reduceSeq : (RiseData → RiseData → RiseData) → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--  reduceSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
  | reduceSeqUnroll : (RiseData → RiseData → RiseData) → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--            toMem : {δ1 δ2 : data} → δ1 → {δ1 → δ2} → δ2 -- TODO: very different type in shine repo
  |           toMem : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--           mapVec : {n : nat} → {δ1 δ2 : data} → {δ1 → δ2} → n<δ1> → n<δ2> -- TODO: doesn't exist in shine repo
  |          mapVec : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--         asVector : (n : nat) → {m : nat} → {δ : data} → nm.δ → m.n<δ>
  |        asVector : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--         asScalar : {n m : nat} → {δ : data} → n.m<δ> → nm.δ
  |        asScalar : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive

inductive RisePrimitive
  | RiseHighLevelPrimitive
  | RiseLowLevelPrimitive
