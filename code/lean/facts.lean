import Lean
import KZ73.Solution

/-! For ci.yml: the axioms of the theorems of config.json, then for the badges their hypotheses (the binders
whose type is a proposition) and the number of axioms they use. Run with `lake env lean code/lean/facts.lean`. -/

#print axioms KeithZanello.conjectureB_false
#print axioms KeithZanello.theorem1

open Lean Meta in
#eval show MetaM Unit from do
  let mut hyps := 0
  let mut axs : Array Name := #[]
  for n in [``KeithZanello.conjectureB_false, ``KeithZanello.theorem1] do
    let c ← getConstInfo n
    hyps := hyps + (← forallTelescope c.type fun xs _ =>
      xs.foldlM (fun k x => do return if ← isProp (← inferType x) then k + 1 else k) 0)
    for a in ← collectAxioms n do
      unless axs.contains a do axs := axs.push a
  IO.println s!"hypotheses {hyps}"
  IO.println s!"axioms {axs.size}"
  IO.println s!"sorryAx {axs.contains ``sorryAx}"
