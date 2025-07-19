import Lean
import RiseLean.DataType
import RiseLean.Primitives

open Lean Elab Meta


inductive RExpr where
  | bvar (deBruijnIndex : Nat) (userName : String)
  -- | const (declName : Name) (us : List VLevel)
  -- | prim (name : String)
  | lit (val : Nat)
  | app (fn arg : RExpr)

  | lam (body : RExpr) (binderKind : Option RType)
  | ulam (body : RExpr) (binderType : Option RKind)

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


partial def elabRExpr (tctx : RTypingCtx) (kctx : RKindingCtx): Syntax → TermElabM Expr
  | `(rise_expr| $l:num) => do
    let x ← mkAppM ``RExpr.lit #[mkNatLit l.getNat]
    return x

  | `(rise_expr| $i:ident) => do
    match tctx.reverse.findIdx? (λ (name, _) => name == i.getId) with
    | some index =>
      mkAppM ``RExpr.bvar #[mkNatLit <| index, mkStrLit i.getId.toString]
    -- could give a hint here if we find the identifier in the kinding context.
    | none => throwErrorAt i s!"unknown identifier {mkConst i.getId}"

  | `(rise_expr| fun ( $x:ident , $b:rise_expr )) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) kctx b
    let none := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
    mkAppM ``RExpr.lam #[b, none]

  | `(rise_expr| fun ( $x:ident : $t:rise_type, $b:rise_expr )) => do
    let b ← elabRExpr (tctx.push (x.getId, none)) kctx b
    -- let syntaxTerm : TSyntax `term ← `([RiseT| $t])
    -- let t ← Term.elabTerm syntaxTerm (some (mkConst ``RType))
    let t ← elabRType kctx t
    let some := mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RType, t]
    mkAppM ``RExpr.lam #[b, some]

  | `(rise_expr| fun ( $x:ident : $t:rise_kind, $b:rise_expr )) => do
    let syntaxTerm : TSyntax `term ← `([RiseK| $t])
    let t ← Term.elabTerm syntaxTerm none --(mkConst ``RKind) --(some (mkConst ``RType))
    let b ← elabRExpr tctx (kctx.push (x.getId, t)) b
    let some := mkAppN (mkConst ``Option.some [levelZero]) #[mkConst ``RKind, t]
    -- let none := mkApp (mkConst ``Option.none [levelZero]) (mkConst ``RType)
    mkAppM ``RExpr.ulam #[b, some]

  | `(rise_expr| $e1:rise_expr ( $e2:rise_expr )) => do
      let e1 ← elabRExpr tctx kctx e1
      let e2 ← elabRExpr tctx kctx e2
      mkAppM ``RExpr.app #[e1, e2]

  | `(rise_expr| $e:rise_expr |> $f:rise_expr) => do
    let s ← `(rise_expr| $f($e))
    elabRExpr tctx kctx s

  | _ => throwUnsupportedSyntax

elab "[Rise|" l:rise_expr "]" : term => do
  let tctx : RTypingCtx := #[
    ("map", none),
    ("reduce", none),
    ("zip", none),
    ("add", none),
    ("mult", none),
    ("fst", none),
    ("snd", none)
  ].map (fun (n, t) => (n.toName, t))

  let kctx : RKindingCtx := #[]

  let term ← elabRExpr tctx kctx l
  return term

--set_option pp.explicit true
#check [Rise| fun(as, as)]
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


-- elab "getRHLPrimitiveConstructors" : command => do
--   let env ← getEnv
--   let indName := `RHLPrimitive
--   -- match env.find? indName with
--   -- logInfo m!"{env.find? indName}"
--   let x := (env.find? indName)
--   dbg_trace s!"{x}"

#check 1


def infer (e: RExpr) : RType := sorry
