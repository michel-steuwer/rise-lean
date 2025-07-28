import RiseLean.Type

import RiseLean.Expr
import RiseLean.Check
import Lean
open Lean Elab Meta


structure RResult where
  expr : RExpr
  type : Except String RType


instance : ToString RResult where
  toString x := s!"expr:\n{repr x.expr}\n\ntype:\n{x.type}"

instance [ToExpr α] : ToExpr (Except String α) where
  toExpr
  | .error s => mkApp3 (Expr.const ``Except.error [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α) (toExpr s)
  | .ok a => mkApp3 (Expr.const ``Except.ok [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α) (toExpr a)
  toTypeExpr := mkApp2 (Expr.const ``Except [levelZero, levelZero]) (toTypeExpr String) (toTypeExpr α)  

instance : ToExpr RResult where
  toExpr r := 
    let exprExpr := toExpr r.expr
    let typeExpr := toExpr r.type
    mkAppN (mkConst ``RResult.mk) #[exprExpr, typeExpr]
  toTypeExpr := mkConst ``RResult

declare_syntax_cat  rise_decl
syntax "def" ident ":" rise_type  : rise_decl
syntax rise_decl rise_decl        : rise_decl
syntax "import" "core"            : rise_decl

-- TODO : a rise program could have more than one expr
declare_syntax_cat  rise_program
syntax (rise_decl)? rise_expr : rise_program

partial def elabRDeclAndRExpr (tctx : TCtx) (kctx : KCtx) (mctx : MVCtx) (e: Syntax) : Option Syntax → TermElabM Expr
  | some d_stx =>
    match d_stx with
    | `(rise_decl| def $x:ident : $t:rise_type $decl:rise_decl ) => do
      let t ← elabToRType kctx mctx t
      -- Lean.logInfo m!"found {x.getId} : {t}"
      elabRDeclAndRExpr (tctx.push (x.getId, t)) kctx mctx e (some decl)
    | `(rise_decl| def $x:ident : $t:rise_type ) => do
      let t ← elabToRType kctx mctx t
      -- Lean.logInfo m!"found {x.getId} : {t}"
      elabRDeclAndRExpr (tctx.push (x.getId, t)) kctx mctx e none
    | _ => throwUnsupportedSyntax
  | none => do
      let e <- elabToRExpr tctx kctx mctx e
      let t := inferAux mctx kctx tctx [] e
      -- return toExpr (RResult.mk e t)
      match t with
      | .error s => return toExpr (RResult.mk e <| .error s)
      | .ok t => return toExpr (RResult.mk e <| .ok t.1)

partial def elabRProgram (tctx : TCtx) (kctx : KCtx) (mctx : MVCtx) : Syntax → TermElabM Expr
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
    def transpose : {n m : nat} → {δ : data} → n . m . δ → m . n . δ
  )

elab "[RiseC|" p:rise_expr "]" : term => do
  let p ← `(rise_program| import core $p:rise_expr)
  let p ← liftMacroM <| expandMacros p
  elabRProgram #[] #[] #[] p

-------------------------------------------------------------------------

syntax "#pp " term : command
macro_rules
| `(#pp $e) => `(#eval IO.print <| toString $e)


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

#check [RiseC|
  fun as => fun bs =>
       zip as bs |> map (fun ab => mult (fst ab) (snd ab)) |> reduce add 0
]

#pp [RiseC|
  fun(k : nat) => fun(a : k . float) => reduce add 0 a
]

#pp [RiseC|
  fun(a : 3 . float) => reduce add 0 a
]

-- wrong: need to propagate unification results up
#pp [RiseC|
  fun a => reduce add 0 a
]

#pp [RiseC|
  fun a => reduce add 0
]

#pp [RiseC|
  map (fun ab : float × float => mult (fst ab) (snd ab))
]

#pp [RiseC| add 0 5]
#pp [RiseC| reduce add 0]
#pp [RiseC| map transpose]
