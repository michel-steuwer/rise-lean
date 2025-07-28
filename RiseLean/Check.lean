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

partial def addImplicits (mctx : MVCtx) (t: RType) : (MVCtx × RType) :=
  match t with
  | .upi bk .im un b =>
    let newB := b--b.liftmvars mctx.size
    let newMctx := mctx.push (un.toName, bk, none)
    addImplicits newMctx newB
  | x => (mctx, x)

def inferAux (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (e: RExpr) : Except String RType := do
  match e with
  | .lam bt body =>
    match bt with
    | .some t =>
      let newTctx := tctx.push ("todo".toName, bt)
      let bodyt ← inferAux mctx kctx newTctx body
      return .pi t bodyt
    | none =>
      let newMctx := mctx.push ("todo".toName, RKind.data, none)
      let t := RType.data (.mvar 0 "todo")
      let newTctx := tctx.push ("todo".toName, t)
      let bodyt ← inferAux newMctx kctx newTctx body
      -- dbg_trace bodyt
      return .pi t bodyt
  | .ulam bk body =>
    match bk with
    | some bk =>
      let newMctx := mctx.push ("todo".toName, bk, none)
      let bodyt ← inferAux newMctx kctx tctx body
      return .upi bk .ex "todo" bodyt
    | none => .error "todo: infer ulam arg without annotation"
  | .bvar id _ => match tctx.reverse[id]!.2 with
    | some t => return t
    | none => .error "todo: infer bvar without annotation"
  | .lit _ => return RType.data .scalar
  | .app f e =>
    let ft ← inferAux mctx kctx tctx f
    let (newMctx, ft) := addImplicits mctx ft
    let et ← inferAux newMctx kctx tctx e
    let (newMctx, et) := addImplicits newMctx et
    match ft.liftmvars (et.getmvars.size) with
    | .pi blt brt =>
      match blt.unify et with
      | some s =>
        -- dbg_trace (blt, et, brt, s, brt.apply s)
        return brt.apply s
      | none => .error s!"\n{repr e}\ncannot unify {blt} with {et}"
    | .upi bk .im un b =>
      Except.error s!"unexpected upi {ft}"
    | _ => Except.error s!"not a function type: {ft}"
  -- | _ => Except.error s!"todo: infer {repr e}"


def infer (e : RExpr) : Except String RType :=
  let mctx : MVCtx := #[]
  let kctx : KCtx := #[]
  let tctx : TCtx := #[]
  inferAux mctx kctx tctx e

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
