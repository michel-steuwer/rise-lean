import RiseLean.DataType
import RiseLean.TestSyntax
import Assert

abbrev Substitution := List (Nat × RData)

def RData.subst (s : Substitution) : RData → RData
  | .mvar id un => match s.find? (fun (i,_) => i == id) with
    | some (_, d) => d
    | none => .mvar id un
  | .bvar id un => .bvar id un
  | .array k d => .array k (d.subst s)
  | .pair l r => .pair (l.subst s) (r.subst s)
  | .index k => .index k
  | .scalar => .scalar
  | .vector k => .vector k

def RType.subst (s : Substitution) : RType → RType
  | .data dt => .data (dt.subst s)
  | .upi bk pc un body => .upi bk pc un (body.subst s)
  | .pi binderType body => .pi (binderType.subst s) (body.subst s)


def RData.has (v : Nat) : RData → Bool
  | .mvar id _ => id == v
  | .bvar .. => false
  | .array _ d => d.has v
  | .pair l r => l.has v || r.has v
  | .index .. => false
  | .scalar => false
  | .vector .. => false

def Substitution.has (s : Substitution) (id : Nat) : Bool :=
  s.any (λ (_, t) => t.has id)

def Substitution.subst (s1 s2 : Substitution) : Substitution :=
  s1.map (λ (i, t) => (i, t.subst s2))
  
def Substitution.hasCircular (s : Substitution) : Bool :=
  s.any (λ (i, t) => t.has i)

mutual
partial def mergeSubstitutions (s1 s2 : Substitution) : Option Substitution :=
  s2.foldlM (fun acc (id2, d2) =>
    if acc.has id2 then
      let n := (acc.subst [(id2, d2)])
      -- dbg_trace n
      if n.hasCircular then
        none
      else
        some <| (id2, d2) :: n
    else
      match acc.find? (fun (id1, _) => id1 == id2) with
      | some (_, d1) =>
        if d1 == d2 then some acc else none
      | none =>
        some <| (id2, d2) :: acc
  ) s1

-- TODO : RNat unification.

partial def RData.unify (l : RData) (r : RData) : Option Substitution :=
  match l, r with
  | .mvar id1 _, .mvar id2 _ =>
    if id1 == id2 then some [] else some [(id1, r)]

  | .mvar id _, d | d, .mvar id _ =>
    if d.has id then none else some [(id, d)]
    
  | .bvar n1 un1, .bvar n2 un2 =>
    -- TODO : name probably doesnt have to match
    if n1 == n2 && un1 == un2 then some [] else none

  | .array k1 d1, .array k2 d2 =>
    -- TODO : RNat unification.
    if k1 == k2 then RData.unify d1 d2 else none

  | .pair l1 r1, .pair l2 r2 =>
    match RData.unify l1 l2, RData.unify r1 r2 with
    | some s1, some s2 => mergeSubstitutions s1 s2
    | _, _ => none

  | .index k1, .index k2 =>
  -- TODO : RNat unification.
    if k1 == k2 then some [] else none

  | .scalar, .scalar => some []

  | .vector k1, .vector k2 =>
    if k1 == k2 then some [] else none

  | _, _ => none
end
 
def RType.unify (l : RType) (r : RType) : Option Substitution :=
  match l, r with
  | .data dt1, .data dt2 =>
    RData.unify dt1 dt2

  | .upi bk1 pc1 _ body1, .upi bk2 pc2 _ body2 =>
    if bk1 == bk2 && pc1 == pc2 then
      unify body1 body2
    else none

  | .pi binderType1 body1, .pi binderType2 body2 =>
    match unify binderType1 binderType2, unify body1 body2 with
    | some s1, some s2 => mergeSubstitutions s1 s2
    | _, _ => none

  | _, _ => none

private def unifies (l r : RType) : Option Substitution :=
  if let some s := l.unify r then
    if l.subst s == r.subst s then some s else none
  else
    none

-- tests. note that both params to unify should have the same mvar context.
open RType

#assert (unifies [RTw a     | a                     ] [RTw a     | float                ]) == some [(0, RData.scalar)]
#assert (unifies [RTw a     | float                 ] [RTw a     | a                    ]) == some [(0, RData.scalar)]
#assert (unifies [RTw a     | a                     ] [RTw a     | a                    ]) == some []
#assert (unifies [RTw a     | 3 . a                 ] [RTw a     | 3 . float            ]) == some [(0, RData.scalar)]
#assert (unifies [RTw a     | float → a             ] [RTw a     | float → 3<float>     ]) == some [(0, RData.vector (RNat.nat 3))]
#assert (unifies [RTw a     | 4 . a                 ] [RTw a     | 4 . 5<float>         ]) == some [(0, RData.vector (RNat.nat 5))]
#assert (unifies [RTw a b   | a                     ] [RTw a b   | b                    ]) == some [(1, RData.mvar 0 "b")]
#assert (unifies [RTw a b   | a × b                 ] [RTw a b   | float × 5<float>     ]) == some [(0, RData.vector (RNat.nat 5)), (1, RData.scalar)]
#assert (unifies [RTw a b   | float × a             ] [RTw a b   | b × 3<float>         ]) == some [(1, RData.vector (RNat.nat 3)), (0, RData.scalar)]
#assert (unifies [RTw a b   | a × b                 ] [RTw a b   | 5<float> × float     ]) == some [(0, RData.scalar), (1, RData.vector (RNat.nat 5))]
#assert (unifies [RTw a b   | 5<float> × float      ] [RTw a b   | a × b                ]) == some [(0, RData.scalar), (1, RData.vector (RNat.nat 5))]
#assert (unifies [RTw a b   | a → a                 ] [RTw a b   | a → b                ]) == some [(1, RData.mvar 0 "b")]
#assert (unifies [RTw a b c | a → b                 ] [RTw a b c | c → c                ]) == some [(1, RData.mvar 0 "c"), (2, RData.mvar 0 "c")]
#assert (unifies [RTw a b c | a × b                 ] [RTw a b c | c                    ]) == some [(0, RData.pair (RData.mvar 2 "a") (RData.mvar 1 "b"))]
#assert (unifies [RTw a b c | a × b → a             ] [RTw a b c | c → float            ]) == some [(2, RData.scalar), (0, RData.pair RData.scalar (RData.mvar 1 "b"))]
#assert (unifies [RTw a b c | c → float             ] [RTw a b c | a × b → a            ]) == some [(2, RData.scalar), (0, RData.pair RData.scalar (RData.mvar 1 "b"))]
#assert (unifies [RTw a b c | a × b                 ] [RTw a b c | b × c                ]) == some [(1, RData.mvar 0 "c"), (2, RData.mvar 0 "c")]
#assert (unifies [RTw       | 2 . float             ] [RTw       | 3 . float            ]) == none
#assert (unifies [RTw       | float                 ] [RTw       | 3<float>             ]) == none
#assert (unifies [RTw       | idx[1]                ] [RTw       | idx[2]               ]) == none
#assert (unifies [RTw a     | float → float         ] [RTw a     | a                    ]) == none
#assert (unifies [RTw a     | a                     ] [RTw a     | a → float            ]) == none
#assert (unifies [RTw a     | a → float             ] [RTw a     | a                    ]) == none
#assert (unifies [RTw a     | a                     ] [RTw a     | a × float            ]) == none
#assert (unifies [RTw a     | a × float             ] [RTw a     | a                    ]) == none
#assert (unifies [RTw a b   | a                     ] [RTw a b   | a → b                ]) == none
#assert (unifies [RTw a b c | a × b → a             ] [RTw a b c | c → c                ]) == none
#assert (unifies [RTw a b c | c → c                 ] [RTw a b c | a × b → a            ]) == none
-- TODO
-- #assert (unifies [RTw a     | idx[a]                ] [RTw a     | idx[5]               ]) == some [(0, RData.nat 5)]
-- #assert (unifies [RTw a b   | a . b                 ] [RTw a b   | 3 . float            ]) == some [(1, RData.nat 3), (1, RData.scalar)]
-- #assert (unifies [RTw a b   | a . a                 ] [RTw a b   | 3 . b                ]) == some [(0, RData.nat 3), (1, RData.mvar 0 "a")]
-- #assert (unifies [RTw a b   | idx[a]                ] [RTw a b   | idx[b]               ]) == some [(0, RData.mvar 1 "b")]

