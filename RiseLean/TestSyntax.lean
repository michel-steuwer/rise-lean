import Lean
import RiseLean.DataType
open Lean Elab Meta Command Term

/--
  Utility elaborator for Rise Types - adds metavariables to context.
  "[Rise Type with <identifiers> | <rise_type>]"

  TODO (if necessary): make a difference between variables and metavariables.
  TODO (if necessary): currently all metavars are just data
-/
elab "[RTw" mvars:ident* "|" t:rise_type "]" : term => do
  let l ← liftMacroM <| expandMacros t
  let kctx : RKindingCtx := #[]
  let mctx_list ← mvars.toList.mapM (fun var => do
    let name := var.getId
    let kind_expr ← `(RKind.data)
    let kind_elab ← elabTerm kind_expr none
    return (name, kind_elab)
  )
  let mctx := mctx_list.toArray
  elabRType kctx mctx l

