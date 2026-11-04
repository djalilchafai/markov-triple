import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAPI
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDerivAux5

/-!
# Strong `L²`-derivative of the heat flow on `ℝ^d` (Round 24, stream A, part H-b)

Port of `IsTest.hasDerivAt_heatL2`
(`Instances/Lebesgue/Heat.lean`, `rho`, Taylor remainder, Gaussian integration by parts) to `ℝ^d`.
`∂ₐ heatRd a φ = a · heatRd a (Δφ)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ : (Fin d → ℝ) → ℝ}

theorem hasDerivAt_heatL2 (hφ : φ ∈ A₀ d) (a : ℝ) :
    HasDerivAt (fun b : ℝ => heatL2 φ b) (a • heatL2 (Lf φ) a) a := by
  obtain ⟨C₂, hC₂⟩ := exists_C₂ hφ
  obtain ⟨R, hR0, hR⟩ := exists_support hφ
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ t : ℝ, t ≠ 0 → |t| ≤ 1 →
      ‖t⁻¹ • (heatL2 φ (a + t) - heatL2 φ a) - a • heatL2 (Lf φ) a‖ ≤ c * |t| :=
    ⟨_, fun t h0 h1 => norm_quot_le hφ a hC₂ hR0 hR h0 h1⟩
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (g := fun t : ℝ => c * |t|) ?_
  · filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) one_pos)] with t ht0 ht1
    have ht1' : |t| ≤ 1 := by simpa using le_of_lt (by simpa using ht1)
    have := hc t (Set.mem_compl_singleton_iff.1 ht0) ht1'
    simpa using this
  · have := (continuous_abs.const_mul c).tendsto (0 : ℝ)
    simpa using this.mono_left nhdsWithin_le_nhds

end MarkovTriple.BGL.LebesgueRd
