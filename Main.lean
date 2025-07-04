import RiseLean
import Lean
open Lean Elab Meta
open Lean.Elab.Term

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
--                 asScalar : (n m : nat) → (δ : scalar) → n.m<δ, actually scalar> → nm.δ

--   δ ::= n.δ | δ × δ | "idx [" n "]" | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
--vector 2,4,8,16
-- e.g. 16vfloat, 16_float
-- idx, range 0 to n excluding

-- https://github.com/rise-lang/shine/blob/main/src/main/scala/rise/core/types/ExprType.scala
-- https://github.com/rise-lang/shine/blob/main/src/main/scala/rise/core/Expr.scala
-- example code benchmarks


inductive RiseData
  | array  : Nat → RiseData → RiseData
  | pair   : RiseData → RiseData → RiseData
  | index  : Nat → RiseData
  | scalar : RiseData
  | vector : Nat → RiseData

declare_syntax_cat rise_data
syntax:50 num "·" rise_data:50       : rise_data -- todo: not num, but nat expr, potentially with identifiers; also: doesn't work without spaces. workaround?
syntax:50 "float" :          rise_data
syntax:10 rise_data "×" rise_data : rise_data
syntax "idx" "[" num "]" :rise_data -- todo: not num, see above
syntax "(" rise_data ")" : rise_data

partial def elabRiseData : Syntax → MetaM Expr
  | `(rise_data| $n:num · $d:rise_data) => do
    let d ← elabRiseData d
    mkAppM ``RiseData.array  #[mkNatLit n.getNat, d]
  | `(rise_data| float) => mkAppM ``RiseData.scalar #[]
  | `(rise_data| $l:rise_data × $r:rise_data) => do
    let l ← elabRiseData l
    let r ← elabRiseData r
    mkAppM ``RiseData.pair  #[l, r]
  | `(rise_data| ($d:rise_data)) => elabRiseData d
  | _ => throwUnsupportedSyntax

elab "test_elabRiseData " l:rise_data : term => elabRiseData l

#reduce test_elabRiseData 4·5·float

#reduce test_elabRiseData 1·2·float × 3·4·float
#reduce test_elabRiseData (1·2·float) × (3·4·float)


inductive RiseLit
  | nat : Nat → RiseLit

inductive RiseIndex
  | index : Nat → RiseIndex

-- inductive RiseIdent
--   | var : String → RiseIdent

declare_syntax_cat rise_lit
syntax num       : rise_lit

def elabRiseLit : Syntax → MetaM Expr
  | `(rise_lit| $n:num) => mkAppM ``RiseLit.nat  #[mkNatLit n.getNat]
  | _ => throwUnsupportedSyntax

elab "test_elabRiseLit " l:rise_lit : term => elabRiseLit l

#reduce test_elabRiseLit 4     -- RiseLit.nat 4


--   e ::= fun(x, e) | e (e) | x | l | P             (Abstraction, Application, Identifier, Literal, Primitives)
inductive RiseExpr
-- todo: use lean identifier? check binders again
  | abst  : String → RiseExpr → RiseExpr

  | app   : RiseExpr → RiseExpr → RiseExpr
  | ident : String → RiseExpr
  | lit   : RiseLit → RiseExpr
 -- | prim  : RisePrimitive → RiseExpr


declare_syntax_cat                         rise_expr
syntax rise_lit                          : rise_expr
syntax ident                             : rise_expr
syntax "fun" "(" ident "," rise_expr ")" : rise_expr
syntax rise_expr "(" rise_expr ")"       : rise_expr -- application
syntax rise_expr "|>" rise_expr          : rise_expr -- sugar for application
syntax rise_expr ">>" rise_expr          : rise_expr -- sugar for application
syntax rise_expr "<<" rise_expr          : rise_expr -- sugar for application
-- todo: primitives?

partial def elabRiseExpr : Syntax → TermElabM Expr
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
  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f($e))
    elabRiseExpr s
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
