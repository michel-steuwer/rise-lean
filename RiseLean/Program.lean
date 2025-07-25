import RiseLean.Type
import RiseLean.Expr
import Lean
open Lean Elab Meta

declare_syntax_cat  rise_decl
syntax "def" ident ":" rise_type  : rise_decl
syntax rise_decl rise_decl        : rise_decl
syntax "import" "core"            : rise_decl

declare_syntax_cat  rise_program
syntax (rise_decl)? rise_expr : rise_program



partial def elabRDeclAndRExpr (tctx : RTypingCtx) (kctx : RKindingCtx) (mctx : MVarCtx) (e: Syntax) : Option Syntax → TermElabM Expr
  | some d_stx =>
    match d_stx with
    | `(rise_decl| def $x:ident : $t:rise_type $decl:rise_decl ) => do
      let t ← elabToRType kctx mctx t
      Lean.logInfo m!"found {x.getId} : {t}"
      elabRDeclAndRExpr (tctx.push (x.getId, t)) kctx mctx e (some decl)
    | `(rise_decl| def $x:ident : $t:rise_type ) => do
      let t ← elabToRType kctx mctx t
      Lean.logInfo m!"found {x.getId} : {t}"
      elabRDeclAndRExpr (tctx.push (x.getId, t)) kctx mctx e none
    | _ => throwUnsupportedSyntax
  | none => elabRExpr tctx kctx mctx e

partial def elabRProgram (tctx : RTypingCtx) (kctx : RKindingCtx) (mctx : MVarCtx) : Syntax → TermElabM Expr
  | `(rise_program| $d:rise_decl $e:rise_expr ) => do
    elabRDeclAndRExpr tctx kctx mctx e (some d)
  | `(rise_program| $e:rise_expr ) => do
    elabRDeclAndRExpr tctx kctx mctx e none
  | _ => throwUnsupportedSyntax

elab "[Rise|" p:rise_program "]" : term => do
  let p ← liftMacroM <| expandMacros p
  elabRProgram #[] #[] #[] p

set_option hygiene false in
macro_rules
  | `(rise_decl| import core) => `(rise_decl|
    def map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n . δ1 → n . δ2
    def reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n . δ → δ
    def add : {δ : data} → δ → δ → δ
    def mult : {δ : data} → δ → δ → δ
    def fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
    def snd : {δ1 δ2 : data} → δ1 × δ2 → δ1
    def zip : {n : nat} → {δ1 δ2 : data} → n . δ1 → n . δ2 → n . (δ1 × δ2)
  )

#check [Rise|
def map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n . δ1 → n . δ2
def reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n . δ → δ
def add : {δ : data} → δ → δ → δ
def mult : {δ : data} → δ → δ → δ
def fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
def snd : {δ1 δ2 : data} → δ1 × δ2 → δ1
def zip : {n : nat} → {δ1 δ2 : data} → n . δ1 → n . δ2 → n . (δ1 × δ2)

fun as => fun bs =>
     zip as bs |> map (fun ab => mult (fst ab) (snd ab)) |> reduce add 0
]

#check [Rise|
import core

fun as => fun bs =>
     zip as bs |> map (fun ab => mult (fst ab) (snd ab)) |> reduce add 0
]

#check [Rise|
def map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n . δ1 → n . δ2
def reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n . δ → δ
def add : {δ : data} → δ → δ → δ
def mult : {δ : data} → δ → δ → δ
def fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
def snd : {δ1 δ2 : data} → δ1 × δ2 → δ1
def zip : {n : nat} → {δ1 δ2 : data} → n . δ1 → n . δ2 → n . (δ1 × δ2)

fun(k : nat) => fun(a : k . float) => reduce add 0 a
]
