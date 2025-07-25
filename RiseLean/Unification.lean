import RiseLean.Type
import Assert
import Lean

abbrev Substitution := List (Nat × RData)

def RData.subst (t : RData) (x : Nat) (s : RData) : RData :=
  match t with
  | .mvar y _ => if x == y then s else t
  | .array k d => .array k (d.subst x s)
  | .pair l r => .pair (l.subst x s) (r.subst x s)
  | .bvar id un => .bvar id un
  | .index k => .index k
  | .scalar => .scalar
  | .vector k => .vector k

def RType.subst (t : RType) (x : Nat) (s : RData) : RType :=
  match t with
  | .data dt => .data (dt.subst x s)
  | .upi bk pc un body => .upi bk pc un (body.subst x s)
  | .pi binderType body => .pi (binderType.subst x s) (body.subst x s)

def RData.has (v : Nat) : RData → Bool
  | .mvar id _ => id == v
  | .bvar .. => false
  | .array _ d => d.has v
  | .pair l r => l.has v || r.has v
  | .index .. => false
  | .scalar => false
  | .vector .. => false

def RData.apply (t : RData) (subst : Substitution) : RData :=
  subst.foldr (fun (id, replacement) acc => acc.subst id replacement) t

def RType.apply (t : RType) (subst : Substitution) : RType :=
  subst.foldr (fun (id, replacement) acc => acc.subst id replacement) t

-- unification algorithm adapted from
-- https://web.archive.org/web/20250713140859/http://www.cs.cornell.edu/courses/cs3110/2011sp/Lectures/lec26-type-inference/type-inference.htm

-- we could throw errors here instead of just Option
mutual
partial def unifyOne (s t : RData) : Option Substitution :=
  match s, t with
  | .mvar x _, .mvar y _ =>
    if x == y then some [] else some [(x, t)]

  | .mvar x _, term | term, .mvar x _ =>
    if term.has x then
      none
    else
      some [(x, term)]

  | .bvar n1 un1, .bvar n2 un2 =>
    if n1 == n2 && un1 == un2 then some [] else none

  -- todo: rnat unification
  | .array k1 d1, .array k2 d2 =>
    if k1 == k2 then
      unify [(d1, d2)]
    else
      none

  | .pair l1 r1, .pair l2 r2 =>
    unify [(l1, l2), (r1, r2)]

  -- todo: rnat unification
  | .index k1, .index k2 =>
    if k1 == k2 then some [] else none

  | .scalar, .scalar => some []

  -- todo: rnat unification
  | .vector k1, .vector k2 =>
    if k1 == k2 then some [] else none

  | _, _ => none

partial def unify (equations : List (RData × RData)) : Option Substitution :=
  match equations with
  | [] => some []
  | (x, y) :: t => do
    let t2 <- unify t
    let t1 <- unifyOne (x.apply t2) (y.apply t2)
    t1 ++ t2
end

partial def RData.unify (l r : RData) : Option Substitution :=
  let result := unify l r
  result

mutual partial def unifyOneRType (s t : RType) : Option Substitution :=
  match s, t with
  | .data dt1, .data dt2 =>
    unify [(dt1, dt2)]

  | .upi bk1 pc1 un1 body1, .upi bk2 pc2 un2 body2 =>
    if bk1 == bk2 && pc1 == pc2 && un1 == un2 then
      unifyRType [(body1, body2)]
    else
      none

  | .pi binderType1 body1, .pi binderType2 body2 =>
    unifyRType [(binderType1, binderType2), (body1, body2)]

  | _, _ => none

partial def unifyRType (equations : List (RType × RType)) : Option Substitution :=
  match equations with
  | [] => some []
  | (x, y) :: rest => do
    let tailSubst <- unifyRType rest
    let x' <- x.apply tailSubst
    let y' <- y.apply tailSubst
    let headSubst <- unifyOneRType x' y'
    headSubst ++ tailSubst
end

def RType.unify (l r : RType) : Option Substitution :=
  unifyRType [(l, r)]

-- def Substitution.toString (s : Substitution) : String :=
--   let pairs := s.map (fun (id, term) => s!"({id} -> {repr term})")
--   "[" ++ String.intercalate ", " pairs ++ "]"

-- instance : ToString Substitution where
--   toString := Substitution.toString


-- technically, the "_, _" case doesn't check for enough. we would want better checking here, but we trust the algorithm.
private def unifies (l r : RType) : Bool :=
  match l.unify r, r.unify l with
  | some s1, some s2 =>
    -- dbg_trace s1
    -- dbg_trace s2
    -- dbg_trace (l.apply s1, r.apply s1)
    -- dbg_trace (l.apply s2, r.apply s2)
    -- dbg_trace (l.apply s1 == r.apply s1)
    -- dbg_trace (l.apply s2 == r.apply s2)
    l.apply s1 == r.apply s1 && l.apply s2 == r.apply s2
  | _, _ =>
    -- dbg_trace (l.unify r, r.unify l)
    false

/--
  Utility elaborator for Rise Types - adds metavariables to context.
  "[Rise Type with <identifiers> | <rise_type>]"

  TODO (if necessary): make a difference between variables and metavariables.
  TODO (if necessary): currently all metavars are just data
-/
elab "[RTw" mvars:ident* "|" t:rise_type "]" : term => do
  let l ← Lean.Elab.liftMacroM <| Lean.expandMacros t
  let kctx : RKindingCtx := #[]
  let mctx_list ← mvars.toList.mapM (fun var => do
    let name := var.getId
    let kind_expr ← `(RKind.data)
    let kind_elab ← Lean.Elab.Term.elabTerm kind_expr none
    return (name, kind_elab)
  )
  let mctx := mctx_list.toArray
  elabRType kctx mctx l


-- tests. note that both params to unify should have the same mvar context.

#assert (unifies [RTw a     | a                     ] [RTw a     | float                ]) == true
#assert (unifies [RTw a     | float                 ] [RTw a     | a                    ]) == true
#assert (unifies [RTw a     | a                     ] [RTw a     | a                    ]) == true
#assert (unifies [RTw a     | 3 . a                 ] [RTw a     | 3 . float            ]) == true
#assert (unifies [RTw a     | float → a             ] [RTw a     | float → 3<float>     ]) == true
#assert (unifies [RTw a     | 4 . a                 ] [RTw a     | 4 . 5<float>         ]) == true
#assert (unifies [RTw a b   | a                     ] [RTw a b   | b                    ]) == true
#assert (unifies [RTw a b   | a × b                 ] [RTw a b   | float × 5<float>     ]) == true
#assert (unifies [RTw a b   | float × a             ] [RTw a b   | b × 3<float>         ]) == true
#assert (unifies [RTw a b   | a × b                 ] [RTw a b   | 5<float> × float     ]) == true
#assert (unifies [RTw a b   | 5<float> × float      ] [RTw a b   | a × b                ]) == true
#assert (unifies [RTw a b   | a → a                 ] [RTw a b   | a → b                ]) == true
#assert (unifies [RTw a b c | a → b                 ] [RTw a b c | b → c                ]) == true
#assert (unifies [RTw a b c | a → b                 ] [RTw a b c | c → c                ]) == true
#assert (unifies [RTw a b c | a × b                 ] [RTw a b c | c                    ]) == true
#assert (unifies [RTw a b c | a × b → a             ] [RTw a b c | c → float            ]) == true
#assert (unifies [RTw a b c | c → float             ] [RTw a b c | a × b → a            ]) == true
#assert (unifies [RTw a b c | a × b                 ] [RTw a b c | b × c                ]) == true
#assert (unifies [RTw a b c | b × c                 ] [RTw a b c | a × b                ]) == true
#assert (unifies [RTw       | 2 . float             ] [RTw       | 3 . float            ]) == false
#assert (unifies [RTw       | float                 ] [RTw       | 3<float>             ]) == false
#assert (unifies [RTw       | idx[1]                ] [RTw       | idx[2]               ]) == false
#assert (unifies [RTw a     | float → float         ] [RTw a     | a                    ]) == false
#assert (unifies [RTw a     | a                     ] [RTw a     | a → float            ]) == false
#assert (unifies [RTw a     | a → float             ] [RTw a     | a                    ]) == false
#assert (unifies [RTw a     | a                     ] [RTw a     | a × float            ]) == false
#assert (unifies [RTw a     | a × float             ] [RTw a     | a                    ]) == false
#assert (unifies [RTw a b   | a                     ] [RTw a b   | a → b                ]) == false
#assert (unifies [RTw a b c | a × b → a             ] [RTw a b c | c → c                ]) == false
#assert (unifies [RTw a b c | c → c                 ] [RTw a b c | a × b → a            ]) == false
-- TODO
-- #assert (unifies [RTw a     | idx[a]                ] [RTw a     | idx[5]               ]) == true
-- #assert (unifies [RTw a b   | a . b                 ] [RTw a b   | 3 . float            ]) == true
-- #assert (unifies [RTw a b   | a . a                 ] [RTw a b   | 3 . b                ]) == true
-- #assert (unifies [RTw a b   | idx[a]                ] [RTw a b   | idx[b]               ]) == true
