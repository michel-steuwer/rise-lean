import RiseLean.Prelude
import RiseLean.Expr
import RiseLean.Type
import RiseLean.Unification

-- set_option linter.unusedVariables false
--
-- def check (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (t1 t2: RType) : Except String Bool :=
--   -- match t1, t2 with
--   -- | .pi bt1 b1, .pi bt2 b2 =>
--   return t1 == t2


partial def addImplicits (t: RType) : RElabM RType := do
  match t with
  | .upi bk .im un b => do
    let mid ← getFreshMVarId
    addMVar mid un bk none
    let newB := b.bvar2mvar mid
    addImplicits newB
  | x => return x

partial def inferAux (e: RExpr) : RElabM RType := do
  -- dbg_trace (repr e)
  match e with
  | .const un => match (← findConst? un) with
    | some t => return t
    | none => throwError "unknown identifier {un}"
    
  | .lam un bt body =>
    match bt with
    | .some t =>
      let body := body.bvar2fvar un -- why does this call cause "fail to show termination?"
      let bodyt ← withNewLocalTerm (un, bt) do inferAux body
      return .pi t bodyt
    | none =>
      let body := body.bvar2fvar un -- why does this call cause "fail to show termination?"
      let id ← getFreshMVarId
      addMVar id Lean.Name.anonymous RKind.data  
      let t :=  RType.data (.mvar id Lean.Name.anonymous)
      let bodyt ← withNewLocalTerm (un, t) do inferAux body
      let t ← applyUnifyResults t
      let bodyt ← applyUnifyResults bodyt
      return .pi t bodyt
            -- throwError "todo lam"
    --   let t := RType.data (.mvar 0 "todo")
    --   let (bodyt, s) ← withNewTVar ("todo".toName, some RKind.data) do
    --                    withNewTerm ("todo".toName, t) do
    --                     inferAux s body
    --   dbg_trace (bodyt, s)
    --   let t := t.apply s -- TODO: not enough
    --   return (.pi t bodyt, s)

  | .ulam un bk body =>
    throwError "todo ulam"
    -- match bk with
    -- | some bk =>
    --   let (bodyt, s) ← withNewMVar ("todo".toName, bk, none) do inferAux s body
    --   return (.upi bk .ex "todo" bodyt, s)
    -- | none => throwError "todo: infer ulam arg without annotation"

  | .fvar id =>
    match (← findLocal? id) with
    | some t => return t
    | none => throwError "todo: infer fvar without annotation"
    -- throwError "unexpected fvar {id}"

    -- let tctx ← getTCtx
    -- match tctx.reverse[id]!.2 with
    -- | some t => return t
    -- | none => throwError "todo: infer bvar without annotation"
  | .bvar id =>
    throwError "unexpected bvar {id}"

  | .lit _ => return RType.data .scalar

  | .app f e =>
    let ft ← inferAux f
    let ft ← addImplicits ft
    let et ← inferAux e
    let et ← addImplicits et
    match ft with
    | .pi blt brt =>
      match blt.unify et with
      | some sub =>
        addSubst sub
        return brt.apply sub
        -- applyUnifyResults brt
      | none =>
        throwError s!"\n{repr f}\n\n{repr e}\n\ncannot unify {blt} with {et}"
    | .upi bk .im un b =>
      throwError s!"unexpected upi {ft}"
    | _ => throwError s!"not a function type: {ft}"
  -- | _ => Except.error s!"todo: infer {repr e}"


-- def infer (e : RExpr) : Except String RType :=
--   let mctx : MVCtx := #[]
--   let kctx : KCtx := #[]
--   let tctx : TCtx := #[]
--   inferAux mctx kctx tctx e

-- Q: do we have polymorphism or do we need a type annotation here?
-- #eval infer [Rise| fun(a, a)] -- defaults to data
-- #eval infer [Rise| fun(x : ?dt, x)] -- defaults to data
-- fun(n, n) --default to nat




-- def infer! (e : RExpr) : RType :=
--   match infer e with
--   | .ok t => t
--   | .error s => panic! s

-- def infer? (e : RExpr) : Bool :=
--   match infer e with
--   | .ok _ => true
--   | .error _ => false

-- #reduce infer [RiseC| 0]
-- #guard infer! [RiseC| 0] == (RType.data (RData.scalar))


-- -- TODO: add int etc.
-- example : infer [RiseC| 0] = .ok [RiseT| float] := rfl

-- #eval toString <| infer [RiseC| add]
-- #guard infer! [Rise| add] ==
-- (RType.upi
--   (RKind.data)
--   (Plicity.im)
--   "δ"
--   (RType.pi (RType.data (RData.mvar 0 "δ")) (RType.pi (RType.data (RData.mvar 0 "δ")) (RType.data (RData.mvar 0 "δ")))))

-- #eval infer [Rise| add(add)]
-- #guard !infer? [Rise| add(add)]

-- #eval toString <| infer [Rise| add(0)]
-- #guard infer? [Rise| add(0)]
-- #guard infer! [Rise| add(0)] ==
--   RType.pi (RType.data (RData.scalar)) (RType.data (RData.scalar))

-- #check [Rise| reduce(add)(0)]
-- #eval toString <| infer [Rise| reduce(add)(0)]
-- -- infer reduce(add)(0)
--   -- infer reduce(add)
--   --     reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n.δ → δ
--   --        add : {δ : data} → δ → δ → δ
--   -- check reduce(add)
--   -- add n and δ to ctx, add add's δ to ctx. mctx:
--   -- [0]: n
--   -- [1]: δ (reduce)
--   -- [2]: δ (add)
--   -- now compare ?δ.1 -> ?δ.1 -> ?δ.1 with ?δ.2 -> ?δ.2 -> ?δ.2
--   -- they are "the same" and should be unified
--   -- ?δ.1 == ?δ.2. but we won't need that info anymore (?)
--   -- return ?δ.1 → ?n.0·?δ.1 → δ.1
-- -- now infer 0 : scalar
-- -- this fits ?δ.1
-- -- unify scalar with ?δ.1
-- -- so ?δ.1 → ?n.0·?δ.1 → δ.1 becomes scalar → ?n.0·scalar → scalar
-- -- so return
-- -- ?n.0·scalar → scalar
-- --
-- -- now the last param *must* fit ?n.0·scalar where ?n.0 is a nat.

-- -- these don't work yet.
-- -- i think what we want to have is a "specificity" relation between types that contain metavars.
-- -- e.g. ?d1 -> ?d1 is more specific than ?d1 -> ?d2
-- -- and ?d1 x ?d2 is more specific than ?d4
-- -- and scalar is more specific than ?d7
-- --
-- -- they are "assignable" though, and we want to continue with the more specific one.
-- --
-- --   def RType.assignable : RType -> RType -> Option RType
-- --
-- --
-- #eval toString <| infer [Rise| map(id)]
-- #eval toString <| infer [Rise| map(add(5))]
-- #eval toString <| infer [Rise| map(fst)]
-- #eval toString <| infer [Rise| fst]
-- #eval toString <| infer [Rise| map(transpose)]

-- #eval IO.println <| toString <| infer [Rise| map(id)]
-- #check [Rise| fun(k : nat, fun(a : k . float, reduce(add)(0)(a)))]

-- -- TODO this or add(a, a)
-- -- #check [Rise| fun(a : 3 . float, add a a)]

-- -- TODO: translate example programs in shine/src/test/scala/rise/core
-- -- /home/n/tub/masters/shine/src/test/scala/apps
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
-- --
--
--
--
--
--
