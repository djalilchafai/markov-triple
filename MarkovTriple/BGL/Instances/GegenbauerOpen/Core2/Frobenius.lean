import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Diffusion

/-!
# R29-Q1: parametric Frobenius / `L²` exponent count for the Gegenbauer operators `L_lam`

See `STATEMENTS_R29_Q.md`.  Only the action of one factor `L_lam` on `t^r` (`t = 1-x`) and the `L²(ρ_lam)` criterion at the
endpoint are proved; nothing about `Core2`.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Q

open MarkovTriple.BGL.Instances.GegenbauerOpen

/-- `L_lam f = (1-x²) f'' - (2 lam + 1) x f'`. -/
noncomputable def gL (lam : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (1 - x ^ 2) * deriv (deriv f) x - (2 * lam + 1) * x * deriv f x

/-- weight density `(1-x²)^(lam - 1/2)`. -/
noncomputable def gρ (lam : ℝ) (x : ℝ) : ℝ := (1 - x ^ 2) ^ (lam - 1 / 2)

theorem gL_three_halves (f : ℝ → ℝ) : gL (3 / 2) f = goL f := by
  funext x
  simp only [gL, goL]
  ring

theorem gL_pow (lam r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    gL lam (fun y => (1 - y) ^ r) x
      = r * (1 - x) ^ (r - 1) * ((r - 1) * (1 + x) + (2 * lam + 1) * x) := by
  have hpos : 0 < 1 - x := by linarith [hx.2]
  have hd : ∀ y : ℝ, 0 < 1 - y →
      HasDerivAt (fun y : ℝ => (1 - y) ^ r) (-(r * (1 - y) ^ (r - 1))) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have := (h1.rpow_const (p := r) (Or.inl hy.ne'))
    convert this using 1
    ring
  have hd' : ∀ y : ℝ, 0 < 1 - y →
      HasDerivAt (fun y : ℝ => -(r * (1 - y) ^ (r - 1))) (r * (r - 1) * (1 - y) ^ (r - 2)) y := by
    intro y hy
    have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have := (h1.rpow_const (p := r - 1) (Or.inl hy.ne')).const_mul r |>.neg
    convert this using 1
    ring_nf
  have hev : deriv (fun y : ℝ => (1 - y) ^ r) =ᶠ[𝓝 x] fun y => -(r * (1 - y) ^ (r - 1)) := by
    have : ∀ᶠ y in 𝓝 x, 0 < 1 - y :=
      (continuous_const.sub continuous_id).continuousAt.eventually (lt_mem_nhds hpos) |>.mono
        fun y hy => hy
    filter_upwards [this] with y hy using (hd y hy).deriv
  simp only [gL]
  rw [hev.deriv_eq, (hd x hpos).deriv, (hd' x hpos).deriv]
  have e : (1 - x) ^ (r - 2) = (1 - x) ^ (r - 1) / (1 - x) := by
    rw [show r - 2 = (r - 1) - 1 by ring, Real.rpow_sub hpos, Real.rpow_one]
  rw [e]
  have h1x : (1 - x) ≠ 0 := hpos.ne'
  field_simp
  ring

theorem gL_pow_indicial (lam r : ℝ) :
    (r - 1) * (1 + 1) + (2 * lam + 1) * 1 = 2 * r + 2 * lam - 1 := by ring

/-- reflection `x ↦ 1 - x` on `(0,1)`. -/
lemma integrableOn_reflect (g : ℝ → ℝ) :
    IntegrableOn (fun x => g (1 - x)) (Ioo (0 : ℝ) 1) ↔ IntegrableOn g (Ioo (0 : ℝ) 1) := by
  have hmp : MeasurePreserving (fun x : ℝ => 1 - x) volume volume := (volume : Measure ℝ).measurePreserving_sub_left 1
  have hpre : (fun x : ℝ => 1 - x) ⁻¹' Ioo (0 : ℝ) 1 = Ioo 0 1 := by
    ext x; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have := hmp.integrableOn_comp_preimage (MeasurableEquiv.subLeft (1 : ℝ)).measurableEmbedding
    (f := g) (s := Ioo (0 : ℝ) 1)
  rw [hpre] at this
  exact this

lemma integrableOn_rpow_one_sub_iff (s : ℝ) :
    IntegrableOn (fun x : ℝ => (1 - x) ^ s) (Ioo (0 : ℝ) 1) ↔ -1 < s := by
  rw [integrableOn_reflect (fun t => t ^ s), intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]

theorem pow_sq_integrable_iff (lam r : ℝ) :
    IntegrableOn (fun x => ((1 - x) ^ r) ^ 2 * gρ lam x) (Ioo (0 : ℝ) 1) ↔
      0 < 2 * r + lam + 1 / 2 := by
  set μ := lam - 1 / 2 with hμ
  have key : ∀ x ∈ Ioo (0 : ℝ) 1,
      ((1 - x) ^ r) ^ 2 * gρ lam x = (1 - x) ^ (2 * r + μ) * (1 + x) ^ μ := by
    intro x hx
    have h1 : 0 < 1 - x := by linarith [hx.2]
    have h2 : 0 < 1 + x := by linarith [hx.1]
    simp only [gρ]
    rw [show 1 - x ^ 2 = (1 - x) * (1 + x) by ring, Real.mul_rpow h1.le h2.le,
      ← hμ, Real.rpow_add h1, ← Real.rpow_mul_natCast h1.le]
    push_cast
    ring_nf
  have hmeas : Measurable fun x : ℝ => (1 + x) ^ μ := by fun_prop
  have hmeas2 : Measurable fun x : ℝ => (1 - x) ^ (2 * r + μ) := by fun_prop
  have hbd : ∃ m M : ℝ, 0 < m ∧ ∀ x ∈ Ioo (0 : ℝ) 1, m ≤ (1 + x) ^ μ ∧ (1 + x) ^ μ ≤ M := by
    refine ⟨min 1 (2 ^ μ), max 1 (2 ^ μ), lt_min one_pos (Real.rpow_pos_of_pos two_pos _), ?_⟩
    intro x hx
    have h2 : (1 : ℝ) < 1 + x := by linarith [hx.1]
    have h3 : 1 + x < 2 := by linarith [hx.2]
    rcases le_total 0 μ with h | h
    · have a1 : (1 : ℝ) ≤ (1 + x) ^ μ := Real.one_le_rpow h2.le h
      have a2 : (1 + x) ^ μ ≤ 2 ^ μ := Real.rpow_le_rpow (by linarith) h3.le h
      exact ⟨(min_le_left _ _).trans a1, a2.trans (le_max_right _ _)⟩
    · have a1 : (1 + x) ^ μ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos h2.le h
      have a2 : 2 ^ μ ≤ (1 + x) ^ μ := Real.rpow_le_rpow_of_nonpos (by linarith) h3.le h
      exact ⟨(min_le_right _ _).trans a2, a1.trans (le_max_left _ _)⟩
  obtain ⟨m, M, hm, hbd⟩ := hbd
  rw [integrableOn_congr_fun key measurableSet_Ioo]
  have hiff := integrableOn_rpow_one_sub_iff (2 * r + μ)
  have e : (2 * r + μ > -1) ↔ 0 < 2 * r + lam + 1 / 2 := by
    rw [hμ]; constructor <;> intro h <;> linarith
  rw [gt_iff_lt] at e
  rw [← e, ← hiff]
  have hnn : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ (1 - x) ^ (2 * r + μ) := fun x hx =>
    Real.rpow_nonneg (by linarith [hx.2]) _
  constructor
  · intro hI
    refine (hI.const_mul (1 / m)).mono' hmeas2.aestronglyMeasurable ?_ 
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have := hnn x hx
    have hb := hbd x hx
    rw [Real.norm_eq_abs, abs_of_nonneg this]
    rw [one_div, inv_mul_eq_div, le_div_iff₀ hm]
    nlinarith [hb.1]
  · intro hI
    refine (hI.const_mul M).mono' (hmeas2.mul hmeas).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
    have := hnn x hx
    have hb := hbd x hx
    have hb0 : 0 ≤ (1 + x) ^ μ := hm.le.trans hb.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg this hb0)]
    nlinarith [hb.2]

theorem exponent_regular_L2 {lam : ℝ} (h : -1 / 2 < lam) :
    0 < 2 * 0 + lam + 1 / 2 ∧ 0 < 2 * 1 + lam + 1 / 2 := by
  constructor <;> linarith

theorem exponent_half_sub_lam_L2_iff (lam : ℝ) :
    0 < 2 * (1 / 2 - lam) + lam + 1 / 2 ↔ lam < 3 / 2 := by
  constructor <;> intro h <;> linarith

theorem exponent_three_half_sub_lam_L2_iff (lam : ℝ) :
    0 < 2 * (3 / 2 - lam) + lam + 1 / 2 ↔ lam < 7 / 2 := by
  constructor <;> intro h <;> linarith

end MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Q
