import RiseLean.DataType
import RiseLean.Primitives
import RiseLean.Expr

abbrev MVCtx := Array (String × RKind × Option RType)
abbrev KCtx := Array (String × Option RType)
abbrev TCtx := Array (String × Option RType)

#check [Rise| fun(k : nat, fun(a : k . float, reduce(add)(0)(a)))]

#check [Rise| fun(a : 3 . float, add(a)(a))]

def inferAux (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (e: RExpr) : RType :=
  match e with
  | .lam a b => sorry 
  | _ => sorry


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

def infer (e : RExpr) : RType :=
  let mctx : MVCtx := #[]
  let kctx : KCtx := #[]
  let tctx : TCtx := #[]

  -- this will be improved once i know what i'm doing
  let add := ("add", [RiseT| {δ : data} → δ → δ → δ])
  let map := ("map", [RiseT| {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n . δ1 → n . δ2])

  -- we actually don't want to add primitives from the very beginning, but rather when we see them. because two instances of the same primitive will have different metavariables.
  let (mctx, kctx, tctx) := addPrimitive mctx kctx tctx add.1 add.2
  let (mctx, kctx, tctx) := addPrimitive mctx kctx tctx map.1 map.2

  dbg_trace (repr mctx) 
  dbg_trace (repr tctx) 
  let x := RType.data (RData.scalar)
  dbg_trace (repr x)
  x

#eval infer [Rise| fun(a, a)]

-- example programs in shine/src/test/scala/rise/core
