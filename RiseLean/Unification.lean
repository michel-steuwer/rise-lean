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


def RData.occurs (v : Nat) : RData → Bool
  | .mvar id _ => id == v
  | .bvar .. => false
  | .array _ d => d.occurs v
  | .pair l r => l.occurs v || r.occurs v
  | .index .. => false
  | .scalar => false
  | .vector .. => false

def Substitution.occurs (s : Substitution) (id : Nat) : Bool :=
  s.any (λ (_, t) => t.occurs id)

def Substitution.subst (s : Substitution) (id : Nat) (t : RData) : Substitution :=
  s.map (λ (i, tt) => (i, tt.subst [(id, t)]))
  
def Substitution.check (s : Substitution) : Bool :=
  !s.any (λ (i, t) => t.occurs i)

mutual
partial def mergeSubstitutions (s1 s2 : Substitution) : Option Substitution :=
  s2.foldlM (fun acc (id2, d2) =>
    if acc.occurs id2 then
      let n := (acc.subst id2 d2)
      -- dbg_trace n
      if !n.check then
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
    if id1 == id2 then some []
    else some [(id1, r)]
  | .mvar id _, d => if d.occurs id then none else some [(id, d)]
  | d, .mvar id _ => if d.occurs id then none else some [(id, d)]
  -- TODO : name probably doesnt have to match?
  | .bvar n1 un1, .bvar n2 un2 =>
    if n1 == n2 && un1 == un2 then some [] else none

  | .array k1 d1, .array k2 d2 =>
  -- TODO : RNat unification.
    if k1 == k2 then RData.unify d1 d2
    else none

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


-- tests. note that both params to unify must have the same mvar context.
open RType
#assert (unify [RTw a     | a                ] [RTw a     | float                ]) == some [(0, RData.scalar)]
#assert (unify [RTw a     | float            ] [RTw a     | a                    ]) == some [(0, RData.scalar)]
#assert (unify [RTw a     | a                ] [RTw a     | a                    ]) == some []
#assert (unify [RTw a     | 3 . a            ] [RTw a     | 3 . float            ]) == some [(0, RData.scalar)]
#assert (unify [RTw a     | float → a        ] [RTw a     | float → 3<float>     ]) == some [(0, RData.vector (RNat.nat 3))]
#assert (unify [RTw a     | 4 . a            ] [RTw a     | 4 . 5<float>         ]) == some [(0, RData.vector (RNat.nat 5))]
#assert (unify [RTw a b   | a                ] [RTw a b   | b                    ]) == some [(1, RData.mvar 0 "b")]
#assert (unify [RTw a b   | a × b            ] [RTw a b   | float × 5<float>     ]) == some [(0, RData.vector (RNat.nat 5)), (1, RData.scalar)]
#assert (unify [RTw a b   | float × a        ] [RTw a b   | b × 3<float>         ]) == some [(1, RData.vector (RNat.nat 3)), (0, RData.scalar)]
#assert (unify [RTw a b   | a × b            ] [RTw a b   | 5<float> × float     ]) == some [(0, RData.scalar), (1, RData.vector (RNat.nat 5))]
#assert (unify [RTw a b   | a → a            ] [RTw a b   | a → b                ]) == some [(1, RData.mvar 0 "b")]
#assert (unify [RTw a b c | a → b            ] [RTw a b c | c → c                ]) == some [(1, RData.mvar 0 "c"), (2, RData.mvar 0 "c")]
#assert (unify [RTw a b c | a × b            ] [RTw a b c | c                    ]) == some [(0, RData.pair (RData.mvar 2 "a") (RData.mvar 1 "b"))]
#assert (unify [RTw a b c | a × b → a        ] [RTw a b c | c → float            ]) == some [(2, RData.scalar), (0, RData.pair RData.scalar (RData.mvar 1 "b"))]
#assert (unify [RTw a b c | c → float        ] [RTw a b c | a × b → a            ]) == some [(2, RData.scalar), (0, RData.pair RData.scalar (RData.mvar 1 "b"))]
#assert (unify [RTw a b c | a × b            ] [RTw a b c | b × c                ]) == some [(1, RData.mvar 0 "c"), (2, RData.mvar 0 "c")]

#assert (unify [RTw       | 2 . float        ] [RTw       | 3 . float            ]) == none
#assert (unify [RTw       | float            ] [RTw       | 3<float>             ]) == none
#assert (unify [RTw       | idx[1]           ] [RTw       | idx[2]               ]) == none
#assert (unify [RTw a     | float → float    ] [RTw a     | a                    ]) == none
#assert (unify [RTw a     | a                ] [RTw a     | a → float            ]) == none
#assert (unify [RTw a     | a → float        ] [RTw a     | a                    ]) == none
#assert (unify [RTw a     | a                ] [RTw a     | a × float            ]) == none
#assert (unify [RTw a     | a × float        ] [RTw a     | a                    ]) == none
#assert (unify [RTw a b   | a                ] [RTw a b   | a → b                ]) == none
#assert (unify [RTw a b c | a × b → a        ] [RTw a b c | c → c                ]) == none
#assert (unify [RTw a b c | c → c            ] [RTw a b c | a × b → a            ]) == none

-- TODO
-- #assert (unify [RTw a b | a . b]                 [RTw | 3 . float]                  ) == some [(1, RData.nat 3), (1, RData.scalar)]
-- #assert (unify [RTw a b | a . a]                 [RTw a b | 3 . b]                  ) == some [(0, RData.nat 3), (1, RData.mvar 0 "a")]
-- #assert (unify [RTw a | idx[a]]                  [RTw | idx[5]]                     ) == some [(0, RData.nat 5)]
-- #assert (unify [RTw a b | idx[a]]                [RTw a b | idx[b]]                 ) == some [(0, RData.mvar 1 "b")]

