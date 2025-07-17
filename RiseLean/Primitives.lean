import RiseLean.DataType

inductive RHLPrimitive where
  |        id : RType -> RHLPrimitive 
  |       add : RType -> RHLPrimitive 
  |      mult : RType -> RHLPrimitive 
  |      todo : RType -> RHLPrimitive 
  |       fst : RType -> RHLPrimitive 
  |       snd : RType -> RHLPrimitive 
  |       map : RType -> RHLPrimitive 
  |    reduce : RType -> RHLPrimitive 
  |       zip : RType -> RHLPrimitive 
  |     split : RType -> RHLPrimitive 
  |      join : RType -> RHLPrimitive 
  | transpose : RType -> RHLPrimitive 
  |  generate : RType -> RHLPrimitive 

def ps : Array RHLPrimitive := #[

        .id [RiseT| {δ : data} → δ → δ],
       .add [RiseT| {δ : data} → δ → δ → δ],
      .mult [RiseT| {δ : data} → δ → δ → δ],
      .todo [RiseT| {δ : data} → δ → δ → δ],
       .fst [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ1],
       .snd [RiseT| {δ1 δ2 : data} → δ1 × δ2 → δ2],
       .map [RiseT| {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2],
    .reduce [RiseT| {n : nat} → {δ : data} → (δ → δ → δ) → δ → n.δ → δ],
       .zip [RiseT| {n : nat} → {δ1 δ2 : data} → n.δ1 → n.δ2 → n.(δ1 × δ2)],
     .split [RiseT| (n : nat) → {m : nat} → {δ : data} → nm.δ → n.m.δ],
      .join [RiseT| {n m : nat} → {δ : data} → n.m.δ → nm.δ],
 .transpose [RiseT| {n m : nat} → {δ : data} → n.m.δ → m.n.δ],
  .generate [RiseT| {n : nat} → {δ : data} → (idx [n] → δ) → n.δ],
]


#reduce ps
-- High-Level Primitives:
-- structure RiseHighLevelPrimitive
--         id : {δ : data} → δ → δ
--        add : {δ : data} → δ → δ → δ
--       mult : {δ : data} → δ → δ → δ
--       todo : {δ : data} → δ → δ → δ
--        fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
--        snd : {δ1 δ2 : data} → δ1 × δ2 → δ2
--        map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--     reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n.δ → δ
--        zip : {n : nat} → {δ1 δ2 : data} → n.δ1 → n.δ2 → n.(δ1 × δ2)
--      split : (n : nat) → {m : nat} → {δ : data} → nm.δ → n.m.δ
--       join : {n m : nat} → {δ : data} → n.m.δ → nm.δ
--  transpose : {n m : nat} → {δ : data} → n.m.δ → m.n.δ
--   generate : {n : nat} → {δ : data} → (idx [n] → δ) → n.δ

-- -- Low-Level Primitives:
-- inductive RiseLowLevelPrimitive
-- --           mapSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--   |          mapSeq : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
-- --     mapSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--   |    mapSeqUnroll : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
-- --           mapPar : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--   |          mapPar : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
-- --        reduceSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--   |       reduceSeq : (RiseData → RiseData → RiseData) → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
-- --  reduceSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--   | reduceSeqUnroll : (RiseData → RiseData → RiseData) → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
-- --            toMem : {δ1 δ2 : data} → δ1 → {δ1 → δ2} → δ2 -- TODO: very different type in shine repo
--   |           toMem : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
-- --           mapVec : {n : nat} → {δ1 δ2 : data} → {δ1 → δ2} → n<δ1> → n<δ2> -- TODO: doesn't exist in shine repo
--   |          mapVec : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
-- --         asVector : (n : nat) → {m : nat} → {δ : data} → nm.δ → m.n<δ>
--   |        asVector : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
-- --         asScalar : {n m : nat} → {δ : data} → n.m<δ> → nm.δ
--   |        asScalar : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive

-- inductive RisePrimitive
--   | RiseHighLevelPrimitive
--   | RiseLowLevelPrimitive
