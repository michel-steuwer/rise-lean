import RiseLean
import Lean
open Lean Elab Meta

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
-- example program
--   // Matrix Matrix Multiplication in RISE
--   val dot = fun(as, fun(bs,
--     zip(as)(bs) |> map(fun(ab, mult(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )
--   val mm = fun(a : M.K.float, fun(b : K.N.float,
--     a |> map(fun(arow, // iterating over M
--       transpose(b) |> map(fun(bcol, // iterating over N
--       dot(arow)(bcol) )))) ) ) // iterating over K

-- RISE
--
-- Syntax of Expressions and Types:
--   e ::= fun(x, e) | e (e) | x | l | P             (Abstraction, Application, Identifier, Literal, Primitives)
--   κ ::= nat | data                                (Natural Number Kind, Datatype Kind)
--   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
--   n ::= 0 | n + n | n · n | ...                   (Natural Number Literals, Binary Operations)
--   δ ::= n.δ | δ × δ | idx [n] | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
--
-- High-Level Primitives:
--                 id : (δ : data) → δ → δ
--   add | mult | ... : (δ : data) → δ → δ → δ
--                fst : (δ1 δ2 : data) → δ1 × δ2 → δ1
--                snd : (δ1 δ2 : data) → δ1 × δ2 → δ2
--                map : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n.δ1 → n.δ2
--             reduce : (n : nat) → (δ : data) → (δ → δ → δ) → δ → n.δ → δ
--                zip : (n : nat) → (δ1 δ2 : data) → n.δ1 → n.δ2 → n.(δ1 × δ2)
--              split : (n m : nat) → (δ : data) → nm.δ → n.m.δ
--               join : (n m : nat) → (δ : data) → n.m.δ → nm.δ
--          transpose : (n m : nat) → (δ : data) → n.m.δ → m.n.δ
--           generate : (n : nat) → (δ : data) → (idx [n] → δ) → n.δ
--
-- Low-Level Primitives:
--   map{Seq|SeqUnroll|Par} : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n.δ1 → n.δ2
--    reduce{Seq|SeqUnroll} : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--                    toMem : (δ1 δ2 : data) → δ1 → (δ1 → δ2) → δ2
--                   mapVec : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n<δ1> → n<δ2>
--                 asVector : (n m : nat) → (δ : data) → nm.δ → n.m<δ>
--                 asScalar : (n m : nat) → (δ : data) → n.m<δ> → nm.δ

--   δ ::= n.δ | δ × δ | idx [n] | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
inductive RiseData
  | array
  | pair
  | index
  | scalar
  | vector

-- High-Level Primitives:
inductive RiseHighLevelPrimitive
--         id : (δ : data) → δ → δ
  |        id : RiseData → RiseData → RiseHighLevelPrimitive
--        add : (δ : data) → δ → δ → δ
  |       add : RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--       mult : (δ : data) → δ → δ → δ
  |      mult : RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--       todo : (δ : data) → δ → δ → δ
  |      todo : RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--        fst : (δ1 δ2 : data) → δ1 × δ2 → δ1
  |       fst : RiseData → RiseData → RiseHighLevelPrimitive
--        snd : (δ1 δ2 : data) → δ1 × δ2 → δ2
  |       snd : RiseData → RiseData → RiseHighLevelPrimitive
--        map : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n.δ1 → n.δ2
  |       map : (RiseData → RiseData) → RiseData → RiseData  → RiseHighLevelPrimitive
--     reduce : (n : nat) → (δ : data) → (δ → δ → δ) → δ → n.δ → δ
  |    reduce : (RiseData → RiseData → RiseData) → RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--        zip : (n : nat) → (δ1 δ2 : data) → n.δ1 → n.δ2 → n.(δ1 × δ2)
  |       zip : RiseData → RiseData → RiseData → RiseHighLevelPrimitive
--      split : (n m : nat) → (δ : data) → nm.δ → n.m.δ
  |     split : RiseData → RiseData → RiseHighLevelPrimitive
--       join : (n m : nat) → (δ : data) → n.m.δ → nm.δ
  |      join : RiseData → RiseData → RiseHighLevelPrimitive
--  transpose : (n m : nat) → (δ : data) → n.m.δ → m.n.δ
  | transpose : RiseData → RiseData → RiseHighLevelPrimitive
--   generate : (n : nat) → (δ : data) → (idx [n] → δ) → n.δ
  |  generate : (RiseData → RiseData) → RiseData → RiseHighLevelPrimitive

-- Low-Level Primitives:
inductive RiseLowLevelPrimitive
--           mapSeq : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n.δ1 → n.δ2
  |          mapSeq : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
--     mapSeqUnroll : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n.δ1 → n.δ2
  |    mapSeqUnroll : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
--           mapPar : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n.δ1 → n.δ2
  |          mapPar : (RiseData → RiseData) → RiseData → RiseData → RiseLowLevelPrimitive
--        reduceSeq : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
  |       reduceSeq : (RiseData → RiseData → RiseData) → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--  reduceSeqUnroll : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
  | reduceSeqUnroll : (RiseData → RiseData → RiseData) → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--            toMem : (δ1 δ2 : data) → δ1 → (δ1 → δ2) → δ2
  |           toMem : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--           mapVec : (n : nat) → (δ1 δ2 : data) → (δ1 → δ2) → n<δ1> → n<δ2>
  |          mapVec : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--         asVector : (n m : nat) → (δ : data) → nm.δ → n.m<δ>
  |        asVector : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive
--         asScalar : (n m : nat) → (δ : data) → n.m<δ> → nm.δ
  |        asScalar : RiseData → RiseData → RiseData → RiseData → RiseLowLevelPrimitive

inductive RisePrimitive
  | RiseHighLevelPrimitive
  | RiseLowLevelPrimitive



inductive RiseLit
  | nat : Nat → RiseLit

inductive RiseIndex
  | index : Nat → RiseIndex

-- inductive RiseIdent
--   | var : String → RiseIdent

declare_syntax_cat rise_lit
syntax num       : rise_lit

def elabRiseLit : Syntax → MetaM Expr
  -- `mkAppM` creates an `Expr.app`, given the function `Name` and the args
  -- `mkNatLit` creates an `Expr` from a `Nat`
  | `(rise_lit| $n:num) => mkAppM ``RiseLit.nat  #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

elab "test_elabRiseLit " l:rise_lit : term => elabRiseLit l

#reduce test_elabRiseLit 4     -- RiseLit.nat 4


--   e ::= fun(x, e) | e (e) | x | l | P             (Abstraction, Application, Identifier, Literal, Primitives)
inductive RiseExpr
  | abst  : String → RiseExpr → RiseExpr
  | app   : RiseExpr → RiseExpr → RiseExpr
  | ident : String → RiseExpr
  | lit   : RiseLit → RiseExpr
  | prim  : RisePrimitive → RiseExpr


declare_syntax_cat                         rise_expr
syntax rise_lit                          : rise_expr
syntax ident                             : rise_expr
syntax "fun" "(" ident "," rise_expr ")" : rise_expr
syntax rise_expr "(" rise_expr ")"       : rise_expr
syntax rise_expr "|>" rise_expr          : rise_expr

-- todo: primitives?


-- todo: couldn't figure out how to apply this macro before elabRiseExpr,
--       so now RiseExpr.app is kinda doubled
macro_rules
  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => `(rise_expr| $f($e))


partial def elabRiseExpr : Syntax → MetaM Expr
  | `(rise_expr| $l:rise_lit) => do
    let l ← elabRiseLit l
    mkAppM ``RiseExpr.lit #[l]
  | `(rise_expr| $i:ident) => mkAppM ``RiseExpr.ident #[mkStrLit i.getId.toString]
  | `(rise_expr| fun ( $x:ident , $e:rise_expr )) => do
    let e ← elabRiseExpr e
    mkAppM ``RiseExpr.abst #[mkStrLit x.getId.toString, e]
  | `(rise_expr| $e1:rise_expr ( $e2:rise_expr )) => do
      let e1 ← elabRiseExpr e1
      let e2 ← elabRiseExpr e2
      mkAppM ``RiseExpr.app #[e1, e2]
  | `(rise_expr| $e1:rise_expr |> $e2:rise_expr) => do
      let e1 ← elabRiseExpr e1
      let e2 ← elabRiseExpr e2
      mkAppM ``RiseExpr.app #[e2, e1]
  | _ => throwUnsupportedSyntax

elab "test_elabRiseExpr " e:rise_expr : term => elabRiseExpr e

open RiseExpr

#reduce test_elabRiseExpr a

#reduce test_elabRiseExpr fun(a,b(c(5))) -- hello



elab "[Rise|" p:rise_expr "]" : term => elabRiseExpr p

#reduce [Rise|

fun(as, fun(bs,
     zip(as)(bs) |> map(fun(ab, mult(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )

]

declare_syntax_cat rise_program
syntax "val" ident "=" rise_expr : rise_program
syntax rise_program rise_program : rise_program

-- RiseExpr.bin RiseBinOp.add (RiseExpr.var "a") (RiseExpr.lit (RiseLit.nat 5))

--#reduce test_elabRiseExpr 1 + true
-- RiseExpr.bin RiseBinOp.add (RiseExpr.lit (RiseLit.nat 1)) (RiseExpr.lit (RiseLit.bool true))
--
--
