import MarkovTriple.FunctionalInequalities.Poincare
import MarkovTriple.Hilbert.SubMarkov
import Lean
open Lean Elab Command

/-- Targeted environment walk: every non-internal constant declared in the listed modules
(including auxiliary lemmas, instances, defs); report any axiom beyond the 3 standard ones. -/
def walkMods (mods : List Name) : CommandElabM Unit := do
  let env ← getEnv
  let mut bad : Nat := 0
  let mut total : Nat := 0
  for (n, _) in env.constants.toList do
    if n.isInternal then continue
    let some mi := env.getModuleIdxFor? n | continue
    let mn := env.header.moduleNames[mi.toNat]!
    unless mods.contains mn do continue
    total := total + 1
    let ax ← liftCoreM <| (collectAxioms n)
    let ax' := ax.filter (fun a => !([`propext, `Classical.choice, `Quot.sound].contains a))
    if !ax'.isEmpty then
      bad := bad + 1
      logInfo m!"BAD {n} : {ax'}"
  logInfo m!"checked {total} constants, {bad} with nonstandard axioms"

run_cmd walkMods [`MarkovTriple.FunctionalInequalities.Poincare,
  `MarkovTriple.FunctionalInequalities.GapFromSquare, `MarkovTriple.FunctionalInequalities.TripleSquare,
  `MarkovTriple.Hilbert.SubMarkov]
