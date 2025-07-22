import Lean
import RiseLean.DataType
import RiseLean.Primitives

-- RISE
--
-- Syntax of Expressions and Types:
--   e ::= fun(x, e) | e (e) | x | l | P             (Abstraction, Application, Identifier, Literal, Primitives)
--   κ ::= nat | data                                (Natural Number Kind, Datatype Kind)
--   τ ::= δ | τ → τ | (x : κ) → τ                   (Data Type, Function Type, Dependent Function Type)
--   n ::= 0 | n + n | n · n | ...                   (Natural Number Literals, Binary Operations)
--   δ ::= n.δ | δ × δ | idx [n] | float | n<float>  (Array Type, Pair Type, Index Type, Scalar Type, Vector Type)
--

-- example program
--   // Matrix Matrix Multiplication in RISE
--   val dot = fun(as, fun(bs,
--     zip(as)(bs) |> map(fun(ab, mult(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )
--   val mm = fun(a : M.K.float, fun(b : K.N.float,
--     a |> map(fun(arow, // iterating over M
--       transpose(b) |> map(fun(bcol, // iterating over N
--       dot(arow)(bcol) )))) ) ) // iterating over K


-- High-Level Primitives:
--         id : {δ : data} → δ → δ
--        add : {δ : data} → δ → δ → δ
--       mult : {δ : data} → δ → δ → δ
--       todo : {δ : data} → δ → δ → δ
--        fst : {δ1 δ2 : data} → δ1 × δ2 → δ1
--        snd : {δ1 δ2 : data} → δ1 × δ2 → δ2
--        map : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--     reduce : {n : nat} → {δ : data} → (δ → δ → δ) → δ → n.δ → δ
--        zip : {n : nat} → {δ1 δ2 : data} → n.δ1 → n.δ2 → n.(δ1 × δ2)
--      split : (n : nat) → {m : nat} → {δ : data} → nm.δ → n.m.δ
--       join : {n m : nat} → {δ : data} → n.m.δ → nm.δ
--  transpose : {n m : nat} → {δ : data} → n.m.δ → m.n.δ
--   generate : {n : nat} → {δ : data} → (idx [n] → δ) → n.δ

-- Low-Level Primitives:
--           mapSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--     mapSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--           mapPar : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2) → n.δ1 → n.δ2
--        reduceSeq : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--  reduceSeqUnroll : {n : nat} → {δ1 δ2 : data} → (δ1 → δ2 → δ1) → δ1 → n.δ2 → δ1
--            toMem : {δ1 δ2 : data} → δ1 → {δ1 → δ2} → δ2 -- TODO: very different type in shine repo
--           mapVec : {n : nat} → {δ1 δ2 : data} → {δ1 → δ2} → n<δ1> → n<δ2> -- TODO: doesn't exist in shine repo
--         asVector : (n : nat) → {m : nat} → {δ : data} → nm.δ → m.n<δ>
--         asScalar : {n m : nat} → {δ : data} → n.m<δ> → nm.δ

open Lean Elab Meta


inductive RExpr where
  | bvar (deBruijnIndex : Nat) (userName : String)
  -- | const (declName : Name) (us : List VLevel)
  -- | prim (name : String)
  | lit (val : Nat)
  | prim (val : RHighLevelPrimitive)
  | app (fn arg : RExpr)

  | lam (body : RExpr) (binderKind : Option RType)
  | ulam (body : RExpr) (binderType : Option RKind)
deriving Repr

abbrev RTypingCtx := Array (Name × Option RType)

-- def dot : RExpr := .lam (.app (.app (.prim "reduce") (.prim "add")) (.lit 0))
-- def s : RExpr := .lam <| .lam (.app (.app
--                                       (.prim "plus")
--                                       (.bvar 0 "a"))
--                                     (.bvar 1 "b"))


declare_syntax_cat                         rise_expr
-- syntax rise_lit                          : rise_expr
syntax num : rise_expr
syntax ident                             : rise_expr
syntax "fun" "(" ident (":" rise_type)? "," rise_expr ")" : rise_expr
syntax "fun" "(" ident (":" rise_kind) "," rise_expr ")" : rise_expr
syntax rise_expr "(" rise_expr ")"       : rise_expr -- application
syntax rise_expr "|>" rise_expr          : rise_expr -- sugar for application


-- a ToExpr instance would be nice to have!

partial def elabRExpr (tctx : RTypingCtx) (kctx : RKindingCtx) (mctx : MVarCtx) : Syntax → TermElabM Expr
  | `(rise_expr| $l:num) => do
    let x ← mkAppM ``RExpr.lit #[mkNatLit l.getNat]
    return x

  | `(rise_expr| $i:ident) => do
    match i.getId.toString with
    | "id" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.id]
    | "add" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.add]
    | "map" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.map]
    | "reduce" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.reduce]
    | "mult" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.mult]
    | "snd" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.snd]
    | "fst" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.fst]
    | "zip" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.zip]
    | "transpose" => mkAppM ``RExpr.prim #[mkConst ``RHighLevelPrimitive.transpose]
    -- etc... could probably be automated by reflecting on primitive type
    | _ => match tctx.reverse.findIdx? (λ (name, _) => name == i.getId) with
      | some index =>
        mkAppM ``RExpr.bvar #[mkNatLit <| index, mkStrLit i.getId.toString]
      -- could give a hint here if we find the identifier in the kinding context.
      | none => throwErrorAt i s!"unknown identifier {mkConst i.getId}"

  | `(rise_expr| fun ( $x:ident , $b:rise_expr )) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) kctx mctx b
    let none := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
    mkAppM ``RExpr.lam #[b, none]

  | `(rise_expr| fun ( $x:ident : $t:rise_type, $b:rise_expr )) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) kctx mctx b
    -- let syntaxTerm : TSyntax `term ← `([RiseT| $t])
    -- let t ← Term.elabTerm syntaxTerm (some (mkConst ``RType))
    let t ← elabRType kctx mctx t
    let some := mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RType, t]
    mkAppM ``RExpr.lam #[b, some]

  | `(rise_expr| fun ( $x:ident : $t:rise_kind, $b:rise_expr )) => do
    let syntaxTerm : TSyntax `term ← `([RiseK| $t])
    let t ← Term.elabTerm syntaxTerm none --(mkConst ``RKind) --(some (mkConst ``RType))
    let b ← elabRExpr tctx (kctx.push (x.getId, t)) mctx b
    let some := mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RKind, t]
    -- let none := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
    mkAppM ``RExpr.ulam #[b, some]

  | `(rise_expr| $e1:rise_expr ( $e2:rise_expr )) => do
      let e1 ← elabRExpr tctx kctx mctx e1
      let e2 ← elabRExpr tctx kctx mctx e2
      mkAppM ``RExpr.app #[e1, e2]

  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f($e))
    elabRExpr tctx kctx mctx s

  | _ => throwUnsupportedSyntax

elab "[Rise|" l:rise_expr "]" : term => do
  -- let tctx : RTypingCtx := #[
  --   ("map", none),
  --   ("reduce", none),
  --   ("zip", none),
  --   ("add", none),
  --   ("mult", none),
  --   ("fst", none),
  --   ("snd", none)
  -- ].map (fun (n, t) => (n.toName, t))

  let tctx : RTypingCtx := #[]
  let kctx : RKindingCtx := #[]
  let mctx : MVarCtx := #[]

  let term ← elabRExpr tctx kctx mctx l
  return term

--set_option pp.explicit true
#check [Rise| fun(as, as)]

-- TODO keep prim ident names as ident
#check [Rise| fun(map, map)]

#check [Rise| fun(as, fun(bs, as(bs)))]
#check [Rise| fun(as, fun(bs, as(bs (fun(c, c)))))]
#check [Rise| fun(as, as (fun(as, as)))]
-- #check [Rise| map(reduce(zip(filter)))]

#check [Rise|

fun(as, fun(bs,
     zip(as)(bs) |> map(fun(ab, mult(fst(ab))(snd(ab)))) |> reduce(add)(0) ) )

]

#check [Rise| fun(x : float, x)]

#check [Rise| fun(x : nat, 3)]

-- trying to use x at term level. it's not legal,
-- because x is only in the kinding context
-- #check [Rise| fun(x : nat, x)]

#check [Rise| fun(x : 5 . float, x)]

#check [Rise| fun(x : nat , 3)]

#check [Rise| fun(n : nat, fun(x : n . float, x))]

#check [Rise| fun(k : nat, fun(a : k . float, reduce(add)(0)(a)))]
