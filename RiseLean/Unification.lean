import RiseLean.DataType
import RiseLean.TestSyntax

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

def mergeSubstitutions (s1 s2 : Substitution) : Option Substitution :=
  s2.foldlM (fun acc (id2, d2) =>
    match acc.find? (fun (id1, _) => id1 == id2) with
    | some (_, d1) => if d1 == d2 || (d1.ismvar && d2.ismvar) then some acc else none
    -- | some .. => some acc
    | none => some <| (id2, d2) :: acc
  ) s1

-- TODO : RNat unification.

def RData.unify (l : RData) (r : RData) : Option Substitution :=
  match l, r with
  | .mvar id1 _, .mvar id2 _ =>
    if id1 == id2 then some []
    else some [(id1, r), (id2, l)]
  | .mvar id _, d => some [(id, d)]
  | d, .mvar id _ => some [(id, d)]

  -- name probably doesnt have to match?
  | .bvar n1 un1, .bvar n2 un2 =>
    if n1 == n2 && un1 == un2 then some [] else none

  | .array k1 d1, .array k2 d2 =>
  -- TODO : RNat unification.
    if k1 == k2 then unify d1 d2
    else none

  | .pair l1 r1, .pair l2 r2 =>
    match unify l1 l2, unify r1 r2 with
    | some s1, some s2 => mergeSubstitutions s1 s2
    | _, _ => none

  | .index k1, .index k2 =>
  -- TODO : RNat unification.
    if k1 == k2 then some [] else none

  | .scalar, .scalar => some []

  | .vector k1, .vector k2 =>
    if k1 == k2 then some [] else none

  | _, _ => none
 
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
open RType RData
example : unify [RTw a | a]                       [RTw a | float]                    = some [(0, .scalar)] := rfl
example : unify [RTw a | float]                   [RTw a | a]                        = some [(0, .scalar)] := rfl
example : unify [RTw a | a]                       [RTw a | a]                        = some [] := rfl
example : unify [RTw a b | a]                     [RTw a b | b]                      = some [(1, .mvar 0 "b"), (0, .mvar 1 "a")] := rfl
example : unify [RTw a | 3 . a]                   [RTw | 3 . float]                  = some [(0, .scalar)] := rfl
example : unify [RTw a b | a × b]                 [RTw | float × 5<float>]           = some [(0, .vector (RNat.nat 5)), (1, .scalar)] := rfl
example : unify [RTw a b | float × a]             [RTw a b | b × 3<float>]           = some [(1, .vector (RNat.nat 3)), (0, .scalar)] := rfl
example : unify [RTw a b | a × b]                 [RTw | 5<float> × float]           = some [(0, .scalar), (1, .vector (RNat.nat 5))] := rfl

example : unify [RTw a | float → a]               [RTw | float → 3<float>]           = some [(0, .vector (.nat 3))] := rfl
example : unify [RTw a b | a → a]                 [RTw a b | a → b]                  = some [(0, .mvar 1 "a"), (1, .mvar 0 "b")] := rfl
example : unify [RTw a b c | a → b]               [RTw a b c | c → c]                = some [(1, RData.mvar 0 "c"), (2, RData.mvar 0 "c"), (0, RData.mvar 2 "a")] := rfl

-- some [(2, RData.mvar 0 "c"), (0, RData.mvar 2 "a")]
-- some [(1, RData.mvar 0 "c"), (0, RData.mvar 1 "b")]


example : unify [RTw a b c | a × b]               [RTw a b c | c]                    = some [(0, .pair (.mvar 2 "a") (.mvar 1 "b"))] := rfl
example : unify [RTw a b c| a × b → a]            [RTw a b c | c → float]            = some [(2, .scalar), (0, .pair (.mvar 2 "a") (.mvar 1 "b"))] := rfl



example : unify [RTw a b c| a × b → a]            [RTw a b c | c → c]                = none := rfl
example : unify [RTw | 2 . float]                 [RTw | 3 . float]                  = none := rfl
example : unify [RTw | float]                     [RTw | 3<float>]                   = none := rfl
example : unify [RTw | idx[1]]                    [RTw | idx[2]]                     = none := rfl
example : unify [RTw | float → float]             [RTw a | a]                        = none := rfl
