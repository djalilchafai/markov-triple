import MarkovTriple.BGL.Instances.OU.LSIMain
import MarkovTriple.BGL.Theory.Convergence
import MarkovTriple.BGL.Theory.GradientBound

/-! Round-9: axiom walk over MarkovTriple.BGL.Instances.OU.LSI* and MarkovTriple.BGL.Theory.*
and Frozen.  NOT imported by root. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Nat := 0
  let mut sorries : Nat := 0
  for (nm, ci) in env.constants.map₁.toList do
    if (`MarkovTriple.BGL).isPrefixOf nm && !nm.isInternal then
      n := n + 1
      let axs ← liftCoreM (Lean.collectAxioms nm)
      let extra := axs.toList.filter (fun a => !ok.contains a)
      if !extra.isEmpty then
        bad := bad + 1
        logInfo m!"AXIOM {nm}: {extra}"
      let v : Option Lean.Expr := ci.value?
      if v.any (fun e => Lean.Expr.hasSorry e) then
        sorries := sorries + 1
        logInfo m!"SORRY {nm}"
      if ci matches .axiomInfo _ || ci matches .opaqueInfo _ then
        logInfo m!"AXIOM/OPAQUE DECL {nm}"
  logInfo m!"walked {n} constants, {bad} with extra axioms, {sorries} with sorry"
