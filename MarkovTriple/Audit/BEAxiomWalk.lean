import MarkovTriple.FunctionalInequalities.BECircle
import MarkovTriple.FunctionalInequalities.BELSI
import MarkovTriple.FunctionalInequalities.FormDomain
import MarkovTriple.FunctionalInequalities.EntropyIntegrable
import MarkovTriple.FunctionalInequalities.GapFromSquare
import Lean
open Lean Elab Command

/-- Axiom walk (round 6): every non-internal constant of every module
`MarkovTriple.FunctionalInequalities.*` (and `Frozen.*`); also flags `partial`/`unsafe`/opaque/axiom
declarations.  Not imported by the root. -/
def walkFI : CommandElabM Unit := do
  let env ← getEnv
  let mut bad : Nat := 0
  let mut total : Nat := 0
  let mut weird : Nat := 0
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some mi := env.getModuleIdxFor? n | continue
    let mn := env.header.moduleNames[mi.toNat]!
    unless (`MarkovTriple.FunctionalInequalities).isPrefixOf mn || (`MarkovTriple.Frozen).isPrefixOf mn do continue
    total := total + 1
    match ci with
    | .axiomInfo _ | .opaqueInfo _ => weird := weird + 1; logInfo m!"WEIRD {n}"
    | _ => pure ()
    if ci.isUnsafe || ci.isPartial then weird := weird + 1; logInfo m!"UNSAFE/PARTIAL {n}"
    let ax ← liftCoreM <| (collectAxioms n)
    let ax' := ax.filter (fun a => !([`propext, `Classical.choice, `Quot.sound].contains a))
    if !ax'.isEmpty then
      bad := bad + 1
      logInfo m!"BAD {n} : {ax'}"
  logInfo m!"checked {total} constants, {bad} with nonstandard axioms, {weird} weird"

run_cmd walkFI
