import RiseLean.DataType

inductive RHighLevelPrimitive where
  |        id
  |       add
  |      mult
  |      todo
  |       fst
  |       snd
  |       map
  |    reduce
  |       zip
  |     split
  |      join
  | transpose
  |  generate

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
       .map [RiseT| {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n . δ1 → n . δ2],
    .reduce [RiseT| {n : nat} → {δ : data} → (δ → δ → δ) → δ → n . δ → δ],
       .zip [RiseT| {n : nat} → {δ1 δ2 : data} → n . δ1 → n . δ2 → n . (δ1 × δ2)],
     -- .split [RiseT| (n : nat) → {m : nat} → {δ : data} → n * m . δ → n . m . δ],
      -- .join [RiseT| {n m : nat} → {δ : data} → n . m . δ → n * m . δ],
 .transpose [RiseT| {n m : nat} → {δ : data} → n . m . δ → m . n . δ],
  .generate [RiseT| {n : nat} → {δ : data} → (idx [ n ] → δ) → n . δ],
]

#check  [RiseT| {n m : nat} → {δ : data} → n . m . δ → m . n . δ]
open RData
#reduce ps


-- Command that prints the constructor names as strings
-- elab "getRHLPrimitiveConstructors" : command => do
--   let env ← getEnv
--   let indName := `RHLPrimitive
--   -- match env.find? indName with
--   logInfo m!"{env.find? indName}"
  -- | some (ConstantInfo.inductInfo indVal) =>
  --     let ctors := indVal.ctors
  --     let ctorStrs := ctors.map (fun n => n.toString)
  --     logInfo m!"Constructors: {ctorStrs}"
  -- | _ => logError m!"Inductive type {indName} not found or not an inductive type"


-- High-Level Primitives:
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

-- Low-Level Primitives:
--           mapSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--     mapSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--           mapPar : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--        reduceSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--  reduceSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--            toMem : {δ1 δ2 : data} → δ1 → {δ1 → δ2} → δ2 -- TODO: very different type in shine repo
--           mapVec : {n : nat} → {δ1 δ2 : data} → {δ1 → δ2} → n<δ1> → n<δ2> -- TODO: doesn't exist in shine repo
--         asVector : (n : nat) → {m : nat} → {δ : data} → nm.δ → m.n<δ>
--         asScalar : {n m : nat} → {δ : data} → n.m<δ> → nm.δ
