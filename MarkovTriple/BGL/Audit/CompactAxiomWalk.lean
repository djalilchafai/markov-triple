import MarkovTriple.BGL.Theory.Compact.Consequences

/-! Axiom walk over every non-internal constant defined in `MarkovTriple.BGL.Theory.Compact.*`
(NOT imported by root).  Run: `lake env lean MarkovTriple/BGL/Audit/CompactAxiomWalk.lean`. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Nat := 0
  let mut sorries : Nat := 0
  for (nm, ci) in env.constants.map₁.toList do
    if nm.isInternal then continue
    let some idx := env.getModuleIdxFor? nm | continue
    let mod := env.header.moduleNames[idx.toNat]!
    if (`MarkovTriple.BGL.Theory.Compact).isPrefixOf mod then
      n := n + 1
      let axs ← liftCoreM (Lean.collectAxioms nm)
      let extra := axs.toList.filter (fun a => !ok.contains a)
      if !extra.isEmpty then
        bad := bad + 1
        logInfo m!"AXIOM {nm}: {extra}"
      if ci.value?.any (fun e => Lean.Expr.hasSorry e) then
        sorries := sorries + 1
        logInfo m!"SORRY {nm}"
  logInfo m!"walked {n} constants, {bad} with extra axioms, {sorries} with sorry"
