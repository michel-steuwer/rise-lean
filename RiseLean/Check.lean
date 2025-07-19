import RiseLean.DataType
import RiseLean.Primitives
import RiseLean.Expr

abbrev MVCtx := Array (String × RKind × Option RType)
abbrev KCtx := Array (String × Option RType)
abbrev TCtx := Array (String × Option RType)

#check [Rise| fun(k : nat, fun(a : k . float, reduce(add)(0)(a)))]

#check [Rise| fun(a : 3 . float, add(a)(a))]



def addPrimitive (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (name : String) (t : RType) : (MVCtx × KCtx × TCtx) :=
  let newT := t.liftmvars mctx.size -- might need to .liftbvars here for split.
  let newMctx := newT
    |>.getmvars
    |>.map (λ (n,k) => (s!"{name}_{n}_{mctx.size}", k, none))
    |> mctx.append

  -- TODO this won't be enough info to find the correct primitive later...
  -- maybe adding primitives to the context doesn't make sense.
  -- they are not free variables after all, they are not bound anywhere. we just know their type, modulo metavariables. but where and how should we store instances of primitives?
  -- specifically, how should we refer back to them?
  let newTctx := tctx.push (name, newT)

  -- kctx used for explicit type params (like n in split), ignored for now.
  (newMctx,kctx,newTctx)

def check (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (t1 t2: RType) : Bool :=
  t1 == t2

def inferAux (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (e: RExpr) : Except String RType := do
  match e with
  -- | .lam a b => sorry
  | .lit _ => return RType.data .scalar
  | .prim p => match primitives.find? (λ (pn,t) => p == pn) with
    | some t => return t.2
    | none => Except.error s!"unknown primitive {repr p}"
  | .app f e =>
    let ft ← inferAux mctx kctx tctx f
    let et ← inferAux mctx kctx tctx e
    match ft with
    | .pi bt b => if check mctx kctx tctx et bt
        then return b else Except.error s!"{repr et} != {repr bt}"
    | _ => Except.error s!"{repr f} is not a function type, but {repr ft}"
  | _ => Except.error "todo"


def infer (e : RExpr) : Except String RType :=
  let mctx : MVCtx := #[]
  let kctx : KCtx := #[]
  let tctx : TCtx := #[]
  inferAux mctx kctx tctx e

  -- -- this will be improved once i know what i'm doing
  -- let add := ("add", [RiseT| {δ : data} → δ → δ → δ])
  -- let map := ("map", [RiseT| {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n . δ1 → n . δ2])

  -- -- we actually don't want to add primitives from the very beginning, but rather when we see them. because two instances of the same primitive will have different metavariables.
  -- let (mctx, kctx, tctx) := addPrimitive mctx kctx tctx add.1 add.2
  -- let (mctx, kctx, tctx) := addPrimitive mctx kctx tctx map.1 map.2

  -- dbg_trace (repr mctx)
  -- dbg_trace (repr tctx)
  -- let x := RType.data (RData.scalar)
  -- dbg_trace (repr x)
  -- x

-- Q: do we have polymorphism or do we need a type annotation here?
-- #eval infer [Rise| fun(a, a)]

#eval! infer [Rise| 0]
#eval! infer [Rise| add]
#eval! infer [Rise| add(0)]

-- example programs in shine/src/test/scala/rise/core
