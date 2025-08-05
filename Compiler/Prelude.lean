-- This implementation follows "The Compiler Forest"
-- by Mihai Budiu, Joel Galenson, and Gordon D. Plotkin

-- A compiler is a function translating a program in language S into
-- a program in language T
abbrev Compiler S T := S -> T

-- A partial compiler is a “piece” of a compiler:
-- partial compilers need “help” from one or more child compilers to produce
-- a complete result.
--
-- Partial compilers can be composed with each other:
--   pc1 composeWithPC pc2
-- resulting in new partial compilers.
--
-- Partial compilers can also be composed with compilers:
--   pc composeWith c
-- resulting in a complete compiler.
--
abbrev PartialCompiler (S T S' T' : Type) := S -> (S' × (T' -> T))

def PartialCompiler.mk (reduction: S -> S') (generation : (S × T') -> T): PartialCompiler S T S' T' :=
  fun s : S =>
    let s' : S' := reduction s
    (s', fun t' : T' => generation (s, t'))

def PartialCompiler.compose (pc: PartialCompiler S T S' T')
                            (c: Compiler S' T') : Compiler S T :=
  fun s : S =>
    let (s', g) := pc s
    g (c s')

def PartialCompiler.composePC (pc: PartialCompiler S T S' T')
                              (pc': PartialCompiler S' T' S'' T'')
                                : PartialCompiler S T S'' T'' :=
  fun s : S =>
    let (s', g) := pc s
    let (s'', g') := pc' s'
    (s'', g ∘ g')

def Compiler.tensor (c1 : Compiler S1 T1)
                    (c2: Compiler S2 T2) : Compiler (S1 × S2) (T1 × T2) :=
  fun (s1, s2) => (c1 s1, c2 s2)

def PartialCompiler.tensor (pc1: PartialCompiler S1 T1 S1' T1')
                           (pc2: PartialCompiler S2 T2 S2' T2')
                            : PartialCompiler (S1 × S2) (T1 × T2) (S1' × S2') (T1' × T2') :=
  fun (s1, s2) =>
    let (s1', g1) := pc1 s1
    let (s2', g2) := pc2 s2
    ( (s1', s2'),
      fun (t1, t2) =>
        let (t2', t1') := (g2 t2, g1 t1)
        (t1', t2') )
