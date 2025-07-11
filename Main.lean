import RiseLean
import Lean
open Lean Elab Meta Command
--open Lean.Elab.Term

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

syntax "[RiseT|" rise_data "]" : term

macro_rules
  | `([RiseT| float]) => `(RiseData.scalar)
  | `([RiseT| $n:num · $d:rise_data]) => `(RiseData.array $n [RiseT| $d])
  | `([RiseT| $l:rise_data × $r:rise_data]) => `(RiseData.pair [RiseT| $l] [RiseT| $r])
  | `([RiseT| ($d:rise_data)]) => `([RiseT| $d])

open PrettyPrinter Delaborator SubExpr
set_option pp.rawOnError true
@[app_unexpander RiseData.array]
def unexpandRiseDataArray : Unexpander
  | `($(_) $n $r) => `($n · $r)
  | _ => throw ()

@[app_unexpander RiseData.scalar]
def unexpandRiseDataScalar : Unexpander
  | `($(_)) => `(rise_data| float)

@[app_unexpander RiseData.pair]
def unexpandRiseDataPair : Unexpander
  | `($(_) $l $r) => `(($l) × ($r))
  | _ => throw ()

#reduce [RiseT| 4·5·float]
#reduce [RiseT| 1·2·float × 3·4·float]
#check [RiseT| (1·2·float) × (3·4·float)]


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


--   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
inductive RiseType where
  | any : RiseType
  | data : RiseData → RiseType
  | fn : RiseType → RiseType → RiseType

--   e ::= fun(x, e) | e (e) | x | l | P             (Abstraction, Application, Identifier, Literal, Primitives)
inductive RiseExpr' (rep : RiseType → Type) : RiseType → Type
  | abst  : (rep dom → RiseExpr' rep ran) → RiseExpr' rep (.fn dom ran)
  | app   : RiseExpr' rep (.fn dom ran) → RiseExpr' rep dom → RiseExpr' rep ran
  | ident : rep ty → RiseExpr' rep ty
  | lit   : Nat → RiseExpr' rep ty
  | muh : RiseExpr' rep ty
 -- | prim  : RisePrimitive → RiseExpr

def RiseExpr (ty : RiseType) := {rep : RiseType → Type} → RiseExpr' rep ty

def e : RiseExpr (.any) := (RiseExpr'.lit $ 1)



declare_syntax_cat                         rise_expr
syntax "muh" :rise_expr
-- syntax rise_lit                          : rise_expr
syntax num : rise_expr
syntax ident                             : rise_expr
syntax "fun" "(" ident "," rise_expr ")" : rise_expr
syntax rise_expr "(" rise_expr ")"       : rise_expr -- application
syntax rise_expr "|>" rise_expr          : rise_expr -- sugar for application
syntax rise_expr ">>" rise_expr          : rise_expr -- sugar for application
syntax rise_expr "<<" rise_expr          : rise_expr -- sugar for application
-- todo: primitives?



-- set_option trace.Meta.

partial def elabRiseExpr : Syntax → TermElabM Expr
  -- | `(rise_expr| $l:rise_lit) => do
  --   -- let l ← elabRiseLit l
  --   mkAppM ``RiseExpr'.lit #[l]
  | `(rise_expr| $l:num) => do
    -- let l ← elabRiseLit l
  let t ← mkAppM ``RiseType.any #[] -- ???
  let x ← mkAppM ``RiseExpr'.lit #[mkNatLit l.getNat]
  ---return Expr.inferImplicit x 2 true
  return x
  | `(rise_expr| muh) => do
    mkAppM ``RiseExpr'.muh #[]
  | `(rise_expr| $i:ident) => do
    let t ← mkAppM ``RiseType.any #[] -- ???
    let i ← Term.elabTerm i t
    mkAppM ``RiseExpr'.ident #[i]
  | `(rise_expr| fun ( $x:ident , $b:rise_expr )) => do
    let type ← mkFreshTypeMVar
    withLocalDeclD x.getId type fun fvar => do
      let b ← elabRiseExpr b
      let abst ← mkLambdaFVars #[fvar] b
      mkAppM ``RiseExpr'.abst #[abst]
  | `(rise_expr| $e1:rise_expr ( $e2:rise_expr )) => do
      let e1 ← elabRiseExpr e1
      let e2 ← elabRiseExpr e2
      mkAppM ``RiseExpr'.app #[e1, e2]
  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f($e))
    elabRiseExpr s
  | _ => throwUnsupportedSyntax

elab "test_elabRiseExpr " e:rise_expr : term => elabRiseExpr e

-- open RiseExpr


set_option pp.explicit true


#reduce test_elabRiseExpr muh

#reduce test_elabRiseExpr 1

#reduce test_elabRiseExpr fun(a, a)


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
