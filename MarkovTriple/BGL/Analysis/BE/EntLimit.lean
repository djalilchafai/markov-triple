import Mathlib
import MarkovTriple.BGL.Frozen.Ent

/-!
# `Ent(ε + g) → Ent(g)` as `ε → 0⁺` for `g ∈ L²` (probability measure)

Ported from the legacy `FunctionalInequalities/BELSI.lean` / `EntropyIntegrable.lean`; stated
with the BGL entropy `MarkovTriple.BGL.Ent` (identical definition to the legacy one).
Used by `BGL/Theory/LogSobolev*.lean` (the `ε → 0` step of the Bakry-Emery argument).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple

/-- `|x log x| ≤ 1 + x²`. -/
lemma abs_mul_log_le (x : ℝ) : |x * Real.log x| ≤ 1 + x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hax : 0 < |x| := abs_pos.2 hx
  have hl : Real.log x = Real.log |x| := (Real.log_abs x).symm
  rw [abs_mul, hl]
  by_cases h1 : 1 ≤ |x|
  · have h0 : 0 ≤ Real.log |x| := Real.log_nonneg h1
    rw [abs_of_nonneg h0]
    have := Real.log_le_sub_one_of_pos hax
    have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [sq_nonneg |x|]
  · push Not at h1
    have h0 : Real.log |x| ≤ 0 := Real.log_nonpos hax.le h1.le
    rw [abs_of_nonpos h0]
    have h2 : Real.log (|x|⁻¹) ≤ |x|⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hax)
    rw [Real.log_inv] at h2
    have h3 : |x| * -Real.log |x| ≤ |x| * (|x|⁻¹ - 1) := mul_le_mul_of_nonneg_left h2 hax.le
    have h4 : |x| * (|x|⁻¹ - 1) = 1 - |x| := by field_simp
    nlinarith [sq_nonneg x, abs_nonneg x]

end MarkovTriple

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E]

/-- `Ent(ε + g) → Ent(g)` as `ε → 0⁺` for `g ∈ L²` (probability measure). -/
theorem tendsto_Ent_add (μ : Measure E) [IsProbabilityMeasure μ] {g : E → ℝ} (hg : MemLp g 2 μ) :
    Tendsto (fun ε : ℝ => MarkovTriple.BGL.Ent μ (fun x => ε + g x)) (𝓝[>] 0)
      (𝓝 (MarkovTriple.BGL.Ent μ g)) := by
  have hgi : Integrable g μ := hg.integrable one_le_two
  have h1 : Tendsto (fun ε : ℝ => ∫ x, (ε + g x) * Real.log (ε + g x) ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, g x * Real.log (g x) ∂μ)) := by
    have hbd : Integrable (fun x => 1 + (1 + |g x|) ^ 2) μ :=
      (integrable_const (1 : ℝ)).add (by
        have := (hg.norm.add (memLp_const (1 : ℝ))).integrable_sq
        refine this.congr (Filter.Eventually.of_forall fun x => ?_)
        simp [add_comm])
    refine tendsto_integral_filter_of_dominated_convergence (fun x => 1 + (1 + |g x|) ^ 2)
      ?_ ?_ hbd ?_
    · refine Filter.Eventually.of_forall fun ε => ?_
      exact (Real.continuous_mul_log.comp (continuous_const.add continuous_id)).comp_aestronglyMeasurable
        hg.aestronglyMeasurable
    · have : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT one_pos
      filter_upwards [this] with ε hε
      refine Filter.Eventually.of_forall fun x => ?_
      have h := abs_mul_log_le (ε + g x)
      rw [Real.norm_eq_abs]
      refine h.trans ?_
      have : (ε + g x) ^ 2 ≤ (1 + |g x|) ^ 2 := by
        have h2 : |ε + g x| ≤ 1 + |g x| := by
          calc |ε + g x| ≤ |ε| + |g x| := abs_add_le _ _
            _ ≤ 1 + |g x| := by rw [abs_of_pos hε.1]; linarith [hε.2]
        calc (ε + g x) ^ 2 = |ε + g x| ^ 2 := (sq_abs _).symm
          _ ≤ (1 + |g x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h2 2
      linarith
    · refine Filter.Eventually.of_forall fun x => ?_
      have : Tendsto (fun ε : ℝ => (ε + g x) * Real.log (ε + g x)) (𝓝 0)
          (𝓝 (g x * Real.log (g x))) := by
        have hc : Continuous (fun ε : ℝ => (ε + g x) * Real.log (ε + g x)) :=
          Real.continuous_mul_log.comp (continuous_id.add continuous_const)
        simpa using hc.tendsto 0
      exact this.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => (∫ x, (ε + g x) ∂μ) * Real.log (∫ x, (ε + g x) ∂μ)) (𝓝[>] 0)
      (𝓝 ((∫ x, g x ∂μ) * Real.log (∫ x, g x ∂μ))) := by
    have e : ∀ ε : ℝ, ∫ x, (ε + g x) ∂μ = ε + ∫ x, g x ∂μ := fun ε => by
      rw [integral_add (integrable_const ε) hgi]; simp
    simp_rw [e]
    have hc : Continuous (fun ε : ℝ => (ε + ∫ x, g x ∂μ) * Real.log (ε + ∫ x, g x ∂μ)) :=
      Real.continuous_mul_log.comp (continuous_id.add continuous_const)
    have := hc.tendsto 0
    simp only [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact h1.sub h2

end MarkovTriple.BE
