import MarkovTriple.BGL.Semigroup.Characterization
import MarkovTriple.BGL.Semigroup.Conservative
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Markov
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Calculus.Density
import MarkovTriple.BGL.Calculus.Identities
import MarkovTriple.BGL.Calculus.LSIExtend
import MarkovTriple.BGL.Instances.Circle.Triple
import MarkovTriple.BGL.Instances.OU.Full
import MarkovTriple.BGL.Theory.ALevel
import MarkovTriple.BGL.Theory.Convergence
import MarkovTriple.BGL.Theory.ESAOne
import MarkovTriple.BGL.Theory.Gamma2Integral
import MarkovTriple.BGL.Theory.GammaCalculus
import MarkovTriple.BGL.Theory.GradientBound
import MarkovTriple.BGL.Theory.LogSobolev
import MarkovTriple.BGL.Theory.LogSobolevMain
import MarkovTriple.BGL.Theory.Poincare
import MarkovTriple.BGL.Theory.Tests

/-! Stage-3 axiom walk (NOT imported by root). Modules restricted to the audited set. -/
open Lean Elab Command

run_cmd do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let pre : List Name := [`MarkovTriple.BGL.Semigroup, `MarkovTriple.BGL.Calculus,
    `MarkovTriple.BGL.Theory, `MarkovTriple.BGL.Instances.Circle, `MarkovTriple.BGL.Instances.OU,
    `MarkovTriple.BGL.Audit, `MarkovTriple.BGL.Frozen, `MarkovTriple.BGL.Sanity]
  let skip : List Name := [`MarkovTriple.BGL.Theory.Compact, `MarkovTriple.BGL.Instances.OU.LSI]
  let mut n : Nat := 0
  let mut bad : Nat := 0
  let mut sorries : Nat := 0
  let mut kinds : Nat := 0
  for (nm, ci) in env.constants.map₁.toList do
    if nm.isInternal then continue
    match env.getModuleIdxFor? nm with
    | none => continue
    | some idx =>
      let mn := env.header.moduleNames[idx.toNat]!
      if pre.any (·.isPrefixOf mn) && !skip.any (·.isPrefixOf mn) then
        n := n + 1
        if ci.isUnsafe || ci.isPartial then
          kinds := kinds + 1
          logInfo m!"UNSAFE/PARTIAL {nm}"
        if let .axiomInfo _ := ci then
          logInfo m!"AXIOMDECL {nm}"
        let axs ← liftCoreM (Lean.collectAxioms nm)
        let extra := axs.toList.filter (fun a => !ok.contains a)
        if !extra.isEmpty then
          bad := bad + 1
          logInfo m!"AXIOM {nm}: {extra}"
        if ci.value?.any (fun e => Lean.Expr.hasSorry e) then
          sorries := sorries + 1
          logInfo m!"SORRY {nm}"
  logInfo m!"walked {n} constants, {bad} with extra axioms, {sorries} sorry, {kinds} unsafe/partial"
