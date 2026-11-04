import Mathlib
import MarkovTriple.BGL.Instances.Interval.Diffusion
import MarkovTriple.BGL.Frozen.Complete

/-!
# The interval triple is NOT complete (I3)

BGL Def. 3.3.9 needs `ζ_k ∈ 𝒜₀`, `ζ_k → 1` a.e., `Γ(ζ_k) ≤ 1/(k+1)²`.  On `(0,1)` every `ζ ∈ 𝒜₀` vanishes
near `0`, so `|ζ(x)| ≤ x · sup |ζ'|`; hence `ζ_k(x) ≤ x/(k+1) → 0`, contradicting `ζ_k(x) → 1`.
See `STATEMENTS_R21_Interval.md`.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.Interval

/-- if `ζ ∈ 𝒜₀` and `Γ(ζ) ≤ c²` a.e. on `(0,1)` (`c ≥ 0`), then `|ζ(x)| ≤ c x` for `x ∈ (0,1)`. -/
lemma abs_le_of_Γ {ζ : ℝ → ℝ} (hζ : ζ ∈ ivA₀) {c : ℝ} (hc : 0 ≤ c)
    (hΓ : ivDiff.Γ ζ ζ ≤ᵐ[ivμ] fun _ => c ^ 2) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    |ζ x| ≤ c * x := by
  have h1 : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo (0 : ℝ) 1 → ivDiff.Γ ζ ζ t ≤ c ^ 2 :=
    (ae_restrict_iff' measurableSet_Ioo).1 hΓ
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) x, HasDerivAt ζ (deriv ζ t) t := fun t _ =>
    (ivA₀_smooth hζ).hasDerivAt t
  have hint : IntervalIntegrable (deriv ζ) volume 0 x :=
    (ivA₀_smooth hζ).deriv'.continuous.intervalIntegrable _ _
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  have h0 : ζ 0 = 0 := zero_off hζ (fun h => lt_irrefl _ h.1)
  rw [h0, sub_zero] at hftc
  have hle : ‖∫ t in (0 : ℝ)..x, deriv ζ t‖ ≤ ∫ t in (0 : ℝ)..x, c := by
    refine intervalIntegral.norm_integral_le_of_norm_le hx.1.le ?_ intervalIntegrable_const
    filter_upwards [h1] with t ht htI
    have htm : t ∈ Ioo (0 : ℝ) 1 := ⟨htI.1, htI.2.trans_lt hx.2⟩
    have := ht htm
    simp only [Lebesgue.Gf] at this
    rw [Real.norm_eq_abs]
    have h2 : (deriv ζ t) ^ 2 ≤ c ^ 2 := by nlinarith
    exact (sq_le_sq.1 h2).trans_eq (abs_of_nonneg hc)
  rw [← hftc]
  simpa [Real.norm_eq_abs, mul_comm] using hle

/-- **I3**: the interval triple is not complete (BGL Def. 3.3.9). -/
theorem iv_not_complete : ¬ ivDiff.IsComplete := by
  rintro ⟨ζ, hmem, -, -, hlim, hΓ⟩
  have hne : ivμ ≠ 0 := IsProbabilityMeasure.ne_zero _
  have : (ae ivμ).NeBot := ae_neBot.2 hne
  obtain ⟨x, hxlim, hx⟩ := (hlim.and (ae_restrict_mem measurableSet_Ioo)).exists
  have hb : ∀ k : ℕ, ζ k x ≤ x * (1 / ((k : ℝ) + 1)) := fun k => by
    have := abs_le_of_Γ (hmem k) (c := 1 / ((k : ℝ) + 1)) (by positivity) (hΓ k) hx
    nlinarith [le_abs_self (ζ k x)]
  have hzero : Tendsto (fun k : ℕ => x * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul x
  have := le_of_tendsto_of_tendsto hxlim hzero (Filter.Eventually.of_forall hb)
  linarith

end MarkovTriple.BGL.Instances.Interval
