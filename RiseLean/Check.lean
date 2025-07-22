import RiseLean.Primitives
import RiseLean.Expr
import RiseLean.DataType
import RiseLean.Unification
import RiseLean.Subst

set_option linter.unusedVariables false

abbrev MVCtx := Array (String × RKind × Option RType)
abbrev KCtx := Array (String × Option RType)
abbrev TCtx := Array (String × Option RType)




-- def addPrimitive (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (name : String) (t : RType) : (MVCtx × KCtx × TCtx) :=
--   let newT := t.liftmvars mctx.size -- might need to .liftbvars here for split.
--   let newMctx := newT
--     |>.getmvars
--     |>.map (λ (n,k) => (s!"{name}_{n}_{mctx.size}", k, none))
--     |> mctx.append

--   -- TODO this won't be enough info to find the correct primitive later...
--   -- maybe adding primitives to the context doesn't make sense.
--   -- they are not free variables after all, they are not bound anywhere. we just know their type, modulo metavariables. but where and how should we store instances of primitives?
--   -- specifically, how should we refer back to them?
--   let newTctx := tctx.push (name, newT)

--   -- kctx used for explicit type params (like n in split), ignored for now.
--   (newMctx,kctx,newTctx)

def check (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (t1 t2: RType) : Except String Bool :=
  -- match t1, t2 with
  -- | .pi bt1 b1, .pi bt2 b2 =>
  return t1 == t2

partial def addImplicits (mctx : MVCtx) (t: RType) : (MVCtx × RType) :=
  match t with
  | .upi bk .im un b =>
    let newB := b--b.liftmvars mctx.size
    let newMctx := mctx.push (un, bk, none)
    addImplicits newMctx newB
  | x => (mctx, x)

def inferAux (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (e: RExpr) : Except String RType := do
  match e with
  -- | .lam a b => sorry
  | .lit _ => return RType.data .scalar
  | .prim p => match primitives.find? (λ (pn,t) => p == pn) with
    | some t => return t.2
    | none => Except.error s!"unknown primitive {repr p}"
  | .app f e =>
    let ft ← inferAux mctx kctx tctx f
    dbg_trace "--- ft"
    dbg_trace ft
    dbg_trace mctx
    let (newMctx, ft) := addImplicits mctx ft
    dbg_trace ft
    dbg_trace newMctx
    dbg_trace "aaa"
    let et ← inferAux newMctx kctx tctx e
    let (newMctx, et) := addImplicits newMctx et
    dbg_trace "--- et"
    dbg_trace et
    dbg_trace newMctx
    dbg_trace "--- et"
    match ft.liftmvars 1 with
    | .pi blt brt =>
      let (blk, ek) := (blt.getRKind, et.getRKind) -- this might be the wrong approach and i should just check the types, not kinds (because k : data => k : type)
      unless blk == ek do
        Except.error s!"kind mismatch: {blt} : {blk} != {et} : {ek}"
      dbg_trace "huhu"
      dbg_trace blt
      dbg_trace et
      match blt.unify et with
      | some s =>
        dbg_trace newMctx
        dbg_trace ft
        dbg_trace (blt, et)
        dbg_trace s
        dbg_trace brt
        dbg_trace brt.subst s
        return brt.subst s
      | none => .error s!"no {blt}, {et}"
    | .upi bk .im un b =>
      Except.error s!"unexpected upi {ft}"
    | _ => Except.error s!"not a function type: {ft}"
  | _ => Except.error "todo"


def infer (e : RExpr) : Except String RType :=
  let mctx : MVCtx := #[]
  let kctx : KCtx := #[]
  let tctx : TCtx := #[]
  inferAux mctx kctx tctx e

-- Q: do we have polymorphism or do we need a type annotation here?
-- #eval infer [Rise| fun(a, a)] -- defaults to data
-- #eval infer [Rise| fun(x : ?dt, x)] -- defaults to data
-- fun(n, n) --default to nat




def infer! (e : RExpr) : RType :=
  match infer e with
  | .ok t => t
  | .error s => panic! s

def infer? (e : RExpr) : Bool :=
  match infer e with
  | .ok _ => true
  | .error _ => false

#reduce infer [Rise| 0]
#guard infer! [Rise| 0] == (RType.data (RData.scalar))


-- TODO: add int etc.
example : infer [Rise| 0] = .ok [RiseT| float] := rfl

#eval toString <| infer [Rise| add]
#guard infer! [Rise| add] ==
(RType.upi
  (RKind.data)
  (Plicity.im)
  "δ"
  (RType.pi (RType.data (RData.mvar 0 "δ")) (RType.pi (RType.data (RData.mvar 0 "δ")) (RType.data (RData.mvar 0 "δ")))))

#eval infer [Rise| add(add)]
#guard !infer? [Rise| add(add)]

#eval toString <| infer [Rise| add(0)]
#guard infer? [Rise| add(0)]
#guard infer! [Rise| add(0)] ==
  RType.pi (RType.data (RData.scalar)) (RType.data (RData.scalar))

#check [Rise| reduce(add)(0)]
#eval toString <| infer [Rise| reduce(add)(0)]
-- infer reduce(add)(0)
  -- infer reduce(add)
  --     reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n.δ → δ
  --        add : {δ : data} → δ → δ → δ
  -- check reduce(add)
  -- add n and δ to ctx, add add's δ to ctx. mctx:
  -- [0]: n
  -- [1]: δ (reduce)
  -- [2]: δ (add)
  -- now compare ?δ.1 -> ?δ.1 -> ?δ.1 with ?δ.2 -> ?δ.2 -> ?δ.2
  -- they are "the same" and should be unified
  -- ?δ.1 == ?δ.2. but we won't need that info anymore (?)
  -- return ?δ.1 → ?n.0·?δ.1 → δ.1
-- now infer 0 : scalar
-- this fits ?δ.1
-- unify scalar with ?δ.1
-- so ?δ.1 → ?n.0·?δ.1 → δ.1 becomes scalar → ?n.0·scalar → scalar
-- so return
-- ?n.0·scalar → scalar
--
-- now the last param *must* fit ?n.0·scalar where ?n.0 is a nat.

-- these don't work yet.
-- i think what we want to have is a "specificity" relation between types that contain metavars.
-- e.g. ?d1 -> ?d1 is more specific than ?d1 -> ?d2
-- and ?d1 x ?d2 is more specific than ?d4
-- and scalar is more specific than ?d7
--
-- they are "assignable" though, and we want to continue with the more specific one.
--
--   def RType.assignable : RType -> RType -> Option RType
--
--
#eval toString <| infer [Rise| map(id)]
#eval toString <| infer [Rise| map(add(5))]
#eval toString <| infer [Rise| map(fst)]
#eval toString <| infer [Rise| fst]
#eval toString <| infer [Rise| map(transpose)]

#eval IO.println <| toString <| infer [Rise| map(id)]
#check [Rise| fun(k : nat, fun(a : k . float, reduce(add)(0)(a)))]

-- TODO this or add(a, a)
-- #check [Rise| fun(a : 3 . float, add a a)]

-- TODO: translate example programs in shine/src/test/scala/rise/core
-- /home/n/tub/masters/shine/src/test/scala/apps
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--
