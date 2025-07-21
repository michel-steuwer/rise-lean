import RiseLean.Primitives
import RiseLean.Expr
import RiseLean.DataType

abbrev MVCtx := Array (String × RKind × Option RType)
abbrev KCtx := Array (String × Option RType)
abbrev TCtx := Array (String × Option RType)

#check [Rise| fun(k : nat, fun(a : k . float, reduce(add)(0)(a)))]

#check [Rise| fun(a : 3 . float, add(a)(a))]



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

def check (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (t1 t2: RType) : Bool :=
  t1 == t2

def addImplicits (mctx : MVCtx) (t: RType) : (MVCtx × RType) :=
  match t with
  | .upi bk .im b =>
    let newMctx := mctx.push ("todo", bk, none)
    addImplicits newMctx b
  | x => (mctx, x)

def tryUnify (mctx : MVCtx) (bt et : RType) : Except String RType :=
  match bt with
  | .data (.mvar n s) => return et
  | _ => Except.error "can't unify {bt} and {et}"
  

def inferAux (mctx : MVCtx) (kctx : KCtx) (tctx : TCtx) (e: RExpr) : Except String RType := do
  match e with
  -- | .lam a b => sorry
  | .lit _ => return RType.data .scalar
  | .prim p => match primitives.find? (λ (pn,t) => p == pn) with
    | some t => return t.2
    | none => Except.error s!"unknown primitive {repr p}"
  | .app f e =>
    let ft ← inferAux mctx kctx tctx f
    let (newMctx, ft) := addImplicits mctx ft
    let et ← inferAux mctx kctx tctx e
    match ft with
    | .pi blt brt =>
      if let some m := blt.gettopmvar then
        let blt := blt.substdata m et
      -- let ft := if blt.ismvardata then ft.tryUnifyData et else ft
        if check newMctx kctx tctx et blt
        then return brt.substdata m et else Except.error s!"{repr et} != {repr blt}"
      if check newMctx kctx tctx et blt
      then return brt else Except.error s!"{repr et} != {repr blt}"
    | .upi bk .im b =>
      Except.error s!"unexpected upi {repr ft}"
    | _ => Except.error s!"not a function type: {repr ft}"
  | _ => Except.error "todo"


def infer (e : RExpr) : Except String RType :=
  let mctx : MVCtx := #[]
  let kctx : KCtx := #[]
  let tctx : TCtx := #[]
  inferAux mctx kctx tctx e

-- Q: do we have polymorphism or do we need a type annotation here?
-- #eval infer [Rise| fun(a, a)]

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

#reduce infer [Rise| add]
#guard infer! [Rise| add] == 
(RType.upi
  (RKind.data)
  (Plicity.im)
  (RType.pi (RType.data (RData.mvar 0 "δ")) (RType.pi (RType.data (RData.mvar 0 "δ")) (RType.data (RData.mvar 0 "δ")))))

#reduce infer [Rise| add(add)]
#guard !infer? [Rise| add(add)]

#reduce infer [Rise| add(0)]
#guard infer? [Rise| add(0)]

-- example programs in shine/src/test/scala/rise/core
