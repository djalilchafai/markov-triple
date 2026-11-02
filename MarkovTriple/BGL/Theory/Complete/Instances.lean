import Mathlib
import MarkovTriple.BGL.Theory.Complete.Real
import MarkovTriple.BGL.Instances.OU.LSIMain
import MarkovTriple.BGL.Instances.Lebesgue.Full
import MarkovTriple.BGL.Theory.Conservation.Finite

/-!
# Completeness of Lebesgue and OU, and a non-compact application of Thm 3.3.23

* `lebesgueDiffusion_isComplete`, `ouDiff_isComplete` (BGL Def. 3.3.9) with genuine cutoffs
  `ζ_k = χ(x/(M(k+1)))` (for OU `1 ∉ 𝒜₀ = C_c^∞`, although `γ` is finite).
* `ouFull_conservative_of_complete`: for the OU triple (non-compact, `𝒜 ≠ 𝒜₀`), S11 *re-derived* from
  completeness + the weak gradient bound (`ExtendedAlgebra.conservative_of_complete`), without using the
  field `conservative`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL

theorem lebesgueDiffusion_isComplete : Lebesgue.lebesgueDiffusion.IsComplete :=
  Complete.isComplete_of_real _ (fun _ hf hc => Lebesgue.mem_A₀.2 ⟨hf, hc⟩)
    (fun _ _ => Filter.Eventually.of_forall fun _ => rfl)

theorem ouDiff_isComplete : Instances.OU.ouDiff.IsComplete :=
  Complete.isComplete_of_real _ (fun _ hf hc => ⟨hf, hc⟩)
    (fun _ _ => Filter.Eventually.of_forall fun _ => rfl)

/-- OU: Thm 3.3.23 (first claim) applied to a non-compact triple: completeness + the (proved) weak gradient
bound give `P_t u_n → 1` a.e. for every exhaustion sequence. -/
theorem ouFull_conservative_of_complete {u : ℕ → ℝ → ℝ}
    (hu : IsExhaustion Instances.OU.ouFull.μ Instances.OU.ouFull.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂Instances.OU.ouFull.μ, Tendsto (fun m => (Instances.OU.ouFull.toDiffusionTriple.exhP hu t m :
      ℝ → ℝ) x) atTop (𝓝 1) :=
  Instances.OU.ouFull.conservative_of_complete (ρ := 1) Instances.OU.ouFull_CD
    Instances.OU.ouFull_GradientInterpolation ouDiff_isComplete hu t

end MarkovTriple.BGL

#print axioms MarkovTriple.BGL.lebesgueDiffusion_isComplete
#print axioms MarkovTriple.BGL.ouDiff_isComplete
#print axioms MarkovTriple.BGL.ouFull_conservative_of_complete
