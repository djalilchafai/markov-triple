import MarkovTriple.Sanity.OU.BEStable
import Lean

/-! # Round-7 audit of `ou_lsi` (not imported by the root). -/

open Lean Elab Command MeasureTheory ProbabilityTheory
open MarkovTriple.Sanity.OU

namespace MarkovTriple.Audit.LSI

/-- Fully concrete: the standard Gaussian log-Sobolev inequality for `C_c^∞(ℝ)`, with the frozen
`Ent` and plain `deriv`, `gaussianReal 0 1`. -/
theorem gaussian_lsi_unfolded :
    IsProbabilityMeasure (gaussianReal 0 1) ∧
    ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      MarkovTriple.Ent (gaussianReal 0 1) (fun x => f x ^ 2) ≤
        2 * ∫ x, deriv f x ^ 2 ∂(gaussianReal 0 1) := by
  have h := ou_lsi
  refine ⟨h.1, fun f hf hc => ?_⟩
  have := h.2 f ⟨hf, hc⟩
  simpa [MarkovTriple.energy, ouFull, ouTriple, Go, one_div, sq] using this

/-- Sanity: statement is not vacuous -- it is applied to a concrete nonzero bump with `Ent > 0`
is checked numerically elsewhere; here: A₀ contains a nonzero function. -/
example : ∃ f ∈ ouFull.A₀, f ≠ 0 := by
  obtain ⟨b⟩ : Nonempty (ContDiffBump (0:ℝ)) := ⟨⟨1, 2, one_pos, one_lt_two⟩⟩
  refine ⟨b, ⟨b.contDiff, b.hasCompactSupport⟩, fun h => ?_⟩
  have := congrFun h 0
  have h1 : (b : ℝ → ℝ) 0 = 1 := b.one_of_mem_closedBall (by simp [b.rIn_pos.le])
  rw [h1] at this
  simp at this

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let ok : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let mut total : Nat := 0
  let mut bad : Array (Name × Array Name) := #[]
  let mut flagged : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`MarkovTriple.Sanity.OU).isPrefixOf mod ||
        ((`MarkovTriple.FunctionalInequalities).isPrefixOf mod &&
          (mod.toString.splitOn "FunctionalInequalities.BE").length > 1) ||
        mod == `MarkovTriple.Frozen.LSI do continue
    total := total + 1
    if ci.isUnsafe || ci.isPartial then flagged := flagged.push n
    if let .opaqueInfo _ := ci then flagged := flagged.push n
    if let .axiomInfo _ := ci then flagged := flagged.push n
    let axs ← collectAxioms n
    let extra := axs.filter (· ∉ ok)
    unless extra.isEmpty do bad := bad.push (n, extra)
  logInfo m!"walked {total}; nonstd-axiom: {bad.size}; flagged: {flagged.size} {bad} {flagged}"

#print axioms gaussian_lsi_unfolded
#print axioms MarkovTriple.Sanity.OU.ou_lsi
end MarkovTriple.Audit.LSI
