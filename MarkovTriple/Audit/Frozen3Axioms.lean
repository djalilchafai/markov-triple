import MarkovTriple
/-! Round-3 hostile axiom walk: every non-internal constant of every `MarkovTriple.*` module
(and the root-level `MarkovTriple`/`FullMarkovTriple` structures, which live in `MarkovTriple.Frozen.*`).
Reports: raw `axiom`/`opaque`/`unsafe`/`partial` declarations, and any axiom outside the 3 allowed.
Not imported by the root. Run: `lake env lean MarkovTriple/Audit/Frozen3Axioms.lean`. -/
open Lean Elab Command Meta

private def okAx3 : List Name := [`propext, `Classical.choice, `Quot.sound]

elab "#audit_all" : command => do
  let env ← getEnv
  let mut total : Nat := 0
  let mut nthm : Nat := 0
  let mut ndef : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut odd : Array (Name × String) := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`MarkovTriple).isPrefixOf m do continue
    if m == `MarkovTriple.Audit.Frozen3Axioms then continue
    if n.isInternal || isPrivateName n || n.isInternalDetail then continue
    total := total + 1
    match ci with
    | .thmInfo _ => nthm := nthm + 1
    | .defnInfo d =>
      ndef := ndef + 1
      if d.safety != .safe then odd := odd.push (n, "unsafe/partial")
    | .axiomInfo _ => odd := odd.push (n, "AXIOM")
    | .opaqueInfo _ => odd := odd.push (n, "OPAQUE")
    | _ => pure ()
    let axs ← liftCoreM (collectAxioms n)
    let extra := axs.filter (fun a => a ∉ okAx3)
    if !extra.isEmpty then bad := bad.push (n, extra)
  logInfo m!"checked {total} constants ({nthm} thm, {ndef} defs); axiom offenders: {bad.toList}; odd decls: {odd.toList}"
#audit_all
