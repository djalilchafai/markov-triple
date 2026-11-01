import MarkovTriple
/-! Hostile axiom audit: every non-private, non-auxiliary constant declared in
`MarkovTriple.Divergences.*` (theorems, defs, instances, ...). Not imported by the root.
Run: `lake env lean MarkovTriple/Audit/DivergencesAxioms.lean`. -/
open Lean Elab Command Meta

private def okAx : List Name := [`propext, `Classical.choice, `Quot.sound]

elab "#audit_divergences" : command => do
  let env ← getEnv
  let mut total : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut nthm : Nat := 0
  let mut ndef : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`MarkovTriple.Divergences).isPrefixOf m do continue
    if n.isInternal || isPrivateName n || n.isInternalDetail then continue
    if (← liftCoreM (isProjectionFn n)) then continue
    total := total + 1
    match ci with
    | .thmInfo _ => nthm := nthm + 1
    | .defnInfo _ => ndef := ndef + 1
    | _ => bad := bad.push (n, #[`NOT_THM_OR_DEF])
    let axs ← liftCoreM (collectAxioms n)
    let extra := axs.filter (fun a => a ∉ okAx)
    if !extra.isEmpty then bad := bad.push (n, extra)
  logInfo m!"checked {total} constants ({nthm} theorems, {ndef} defs); offenders: {bad.toList}"
#audit_divergences
