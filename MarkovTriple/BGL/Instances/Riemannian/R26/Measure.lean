import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R26.Atlas1

/-!
# The Riemannian volume glued from the charts: partition of unity

Chartwise volume `w dt` (`w = g^{-1/2}`); change of variables `t ↦ x(t)` onto an arc of length one gives
`∫ F(pt t) w(t) dt = ∫_𝕋 F dμ₀`; with the partition of unity `ρ_N = cos²(πx) = (1 + cos 2πx)/2`,
`ρ_S = sin²(πx) = (1 − cos 2πx)/2` (`ρ_N` vanishes at `x = 1/2`, the point missed by the north chart; `ρ_S` at `x = 0`)
the glued integral `∫ ρ_N F w_N dt + ∫ ρ_S F w_S dt` equals `∫ F dμ₀`.
-/

open MarkovTriple.Sanity.Circle MeasureTheory Set
open scoped Real

namespace MarkovTriple.BGL.Instances.Riemannian.R26

/-- change of variables for a chart whose lift has range an arc `(a, a+1)` -/
theorem integral_chart (c : Chart1) (a : ℝ) (hr : Set.range c.x = Ioo a (a + 1)) (F : 𝕋 → ℝ) :
    ∫ t, F (c.pt t) * c.w t = ∫ p, F p ∂μ₀ := by
  have hmono : StrictMono c.x := strictMono_of_deriv_pos c.dpos
  have h := integral_image_eq_integral_abs_deriv_smul (s := Set.univ) (f := c.x) (f' := deriv c.x)
    MeasurableSet.univ (fun x _ => (c.hasDerivAt_x x).hasDerivWithinAt) hmono.injective.injOn
    (fun y : ℝ => F (y : 𝕋))
  rw [Set.image_univ, hr, Measure.restrict_univ] at h
  have e1 : ∫ t, F (c.pt t) * c.w t = ∫ t, |deriv c.x t| • F (c.x t : 𝕋) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Chart1.pt, Chart1.w, smul_eq_mul, abs_of_pos (c.dpos t)]; ring
  rw [e1, ← h, ← integral_Ioc_eq_integral_Ioo]
  have := AddCircle.integral_preimage (1 : ℝ) a F
  rw [this, AddCircle.integral_haarAddCircle]
  simp

lemma north_range : Set.range northChart.x = Ioo (-1 / 2) (-1 / 2 + 1) := by
  have hπ : 0 < π := Real.pi_pos
  ext y
  simp only [mem_range, mem_Ioo]
  show (∃ t, Real.arctan t / π = y) ↔ _
  constructor
  · rintro ⟨t, rfl⟩
    have h1 := Real.neg_pi_div_two_lt_arctan t
    have h2 := Real.arctan_lt_pi_div_two t
    constructor
    · rw [lt_div_iff₀ hπ]; linarith
    · rw [div_lt_iff₀ hπ]; linarith
  · rintro ⟨h1, h2⟩
    have : y * π ∈ Set.range Real.arctan := by
      rw [Real.range_arctan]
      constructor <;> nlinarith
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [ht]; field_simp⟩

lemma south_range : Set.range southChart.x = Ioo 0 (0 + 1) := by
  have hπ : 0 < π := Real.pi_pos
  ext y
  simp only [mem_range, mem_Ioo]
  show (∃ t, Real.arctan t / π + 1 / 2 = y) ↔ _
  constructor
  · rintro ⟨t, rfl⟩
    have h1 := Real.neg_pi_div_two_lt_arctan t
    have h2 := Real.arctan_lt_pi_div_two t
    constructor
    · have : -(1 / 2) < Real.arctan t / π := by rw [lt_div_iff₀ hπ]; linarith
      linarith
    · have : Real.arctan t / π < 1 / 2 := by rw [div_lt_iff₀ hπ]; linarith
      linarith
  · rintro ⟨h1, h2⟩
    have : (y - 1 / 2) * π ∈ Set.range Real.arctan := by
      rw [Real.range_arctan]
      constructor <;> nlinarith
    obtain ⟨t, ht⟩ := this
    exact ⟨t, by rw [ht]; field_simp; ring⟩

theorem integral_north (F : 𝕋 → ℝ) (_hF : Continuous F) :
    ∫ t, F (northChart.pt t) * northChart.w t = ∫ p, F p ∂μ₀ :=
  integral_chart northChart _ north_range F

theorem integral_south (F : 𝕋 → ℝ) (_hF : Continuous F) :
    ∫ t, F (southChart.pt t) * southChart.w t = ∫ p, F p ∂μ₀ :=
  integral_chart southChart _ south_range F

/-- partition of unity `ρ_N = cos²(πx)` -/
noncomputable def ρN (p : 𝕋) : ℝ := (1 + cC p) / 2
/-- partition of unity `ρ_S = sin²(πx)` -/
noncomputable def ρS (p : 𝕋) : ℝ := (1 - cC p) / 2

lemma ρN_add_ρS (p : 𝕋) : ρN p + ρS p = 1 := by unfold ρN ρS; ring

lemma continuous_ρN : Continuous ρN := (continuous_const.add cC.continuous).div_const 2
lemma continuous_ρS : Continuous ρS := (continuous_const.sub cC.continuous).div_const 2

/-- the atlas-glued integral (partition of unity applied to the chartwise volumes) -/
noncomputable def atlasIntegral (F : 𝕋 → ℝ) : ℝ :=
  (∫ t, ρN (northChart.pt t) * F (northChart.pt t) * northChart.w t) +
  ∫ t, ρS (southChart.pt t) * F (southChart.pt t) * southChart.w t

theorem atlasIntegral_eq (F : 𝕋 → ℝ) (hF : Continuous F) : atlasIntegral F = ∫ p, F p ∂μ₀ := by
  unfold atlasIntegral
  have h1 := integral_north (fun p => ρN p * F p) (continuous_ρN.mul hF)
  have h2 := integral_south (fun p => ρS p * F p) (continuous_ρS.mul hF)
  have i1 : Integrable (fun p => ρN p * F p) μ₀ := integrable_of_cont (continuous_ρN.mul hF)
  have i2 : Integrable (fun p => ρS p * F p) μ₀ := integrable_of_cont (continuous_ρS.mul hF)
  rw [h1, h2, ← integral_add i1 i2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  show ρN p * F p + ρS p * F p = F p
  rw [← add_mul, ρN_add_ρS, one_mul]

/-- the chartwise volume of the north chart is the Cauchy density `dt/(π(1+t²))`: it charges `ℝ` with total mass `1` -/
theorem north_total : ∫ t, northChart.w t = 1 := by
  have := integral_north (fun _ => 1) continuous_const
  simpa using this

end MarkovTriple.BGL.Instances.Riemannian.R26
