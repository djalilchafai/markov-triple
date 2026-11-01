import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Basic

/-!
# Two ODE facts on `ℝ` (no semigroup)

* `exists_antiderivative`: a test function with integral `0` has a test-function antiderivative;
* `exists_resolvent_solution`: for a test function `ψ` the equation `v - v'' = ψ` has a smooth solution
  with `v, v', v'' ∈ L²` (explicitly `v = ½ e^{-|·|} * ψ`, by variation of constants).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

lemma exists_support_bound {f : ℝ → ℝ} (hf : f ∈ A₀) : ∃ R : ℝ, 0 < R ∧ ∀ y, R ≤ |y| → f y = 0 := by
  obtain ⟨R, hR⟩ := (cs hf).isCompact.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun y hy => ?_⟩
  by_contra hne
  have : y ∈ tsupport f := subset_tsupport _ (Function.mem_support.2 hne)
  have h2 := hR this
  simp only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h2
  linarith [le_abs_self R]

lemma sm_of_hasDerivAt {F G : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (G x) x) (hG : Sm G) : Sm F := by
  refine contDiff_infty_iff_deriv.2 ⟨fun x => (hF x).differentiableAt, ?_⟩
  have : deriv F = G := funext fun x => (hF x).deriv
  rw [this]; exact hG

theorem exists_antiderivative {θ : ℝ → ℝ} (hθ : θ ∈ A₀) (h0 : ∫ x, θ x = 0) :
    ∃ φ ∈ A₀, deriv φ = θ := by
  obtain ⟨R, hR, hRθ⟩ := exists_support_bound hθ
  have hθc : Continuous θ := (smooth hθ).continuous
  set φ : ℝ → ℝ := fun x => ∫ y in (-R)..x, θ y with hφ
  have hd : ∀ x, HasDerivAt φ (θ x) x := fun x =>
    (hθc.integral_hasStrictDerivAt (-R) x).hasDerivAt
  have hsm : Sm φ := sm_of_hasDerivAt hd (smooth hθ)
  have hder : deriv φ = θ := funext fun x => (hd x).deriv
  refine ⟨φ, mem_A₀.2 ⟨hsm, ?_⟩, hder⟩
  refine HasCompactSupport.intro (K := Set.Icc (-R) R) isCompact_Icc fun x hx => ?_
  rcases lt_or_ge x (-R) with h | h
  · simp only [hφ]
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_congr
      (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
    · simp
    · rw [Set.uIcc_of_le h.le] at hy
      exact hRθ y (by rw [abs_of_nonpos (by linarith [hy.2])]; linarith [hy.2])
  · have hx' : R < x := by
      by_contra hle
      exact hx ⟨h, not_lt.1 hle⟩
    simp only [hφ]
    rw [intervalIntegral.integral_of_le (by linarith)]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-R) x) (fun y hy => ?_)] at h0
    · exact h0
    · simp only [Set.mem_Ioc, not_and_or, not_lt, not_le] at hy
      rcases hy with hy | hy
      · exact hRθ y (by rw [abs_of_nonpos (by linarith)]; linarith)
      · exact hRθ y (by rw [abs_of_nonneg (by linarith)]; linarith)

/-- Decay: a continuous function equal to `c e^{-x}` for `x ≥ R` and `c' e^{x}` for `x ≤ -R` is
in `L²`. -/
lemma memLp_of_exp_tails {g : ℝ → ℝ} (hg : Continuous g) {R c c' : ℝ} (hR : 0 < R)
    (h1 : ∀ x, R ≤ x → g x = c * Real.exp (-x)) (h2 : ∀ x, x ≤ -R → g x = c' * Real.exp x) :
    MemLp g 2 volume := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn hg.continuousOn
  have hexp : ∀ x : ℝ, 0 ≤ x → 1 + x ^ 2 ≤ 2 * Real.exp x := by
    intro x hx
    have := Real.quadratic_le_exp_of_nonneg hx
    nlinarith
  have hbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |g x| * (1 + x ^ 2) ≤ C := by
    refine ⟨max ((1 + R ^ 2) * max B 0) (max (2 * |c|) (2 * |c'|)), le_max_of_le_right (by positivity), fun x => ?_⟩
    by_cases hx1 : R ≤ x
    · rw [h1 x hx1, abs_mul, Real.abs_exp, mul_assoc]
      refine le_max_of_le_right (le_max_of_le_left ?_)
      have h3 := hexp x (by linarith)
      have : Real.exp (-x) * (1 + x ^ 2) ≤ 2 := by
        calc Real.exp (-x) * (1 + x ^ 2) ≤ Real.exp (-x) * (2 * Real.exp x) :=
              mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
          _ = 2 := by rw [← mul_assoc, mul_comm _ 2, mul_assoc, ← Real.exp_add]; simp
      nlinarith [abs_nonneg c, Real.exp_pos (-x)]
    · by_cases hx2 : x ≤ -R
      · rw [h2 x hx2, abs_mul, Real.abs_exp]
        refine le_max_of_le_right (le_max_of_le_right ?_)
        have h3 := hexp (-x) (by linarith)
        have : Real.exp x * (1 + x ^ 2) ≤ 2 := by
          calc Real.exp x * (1 + x ^ 2) ≤ Real.exp x * (2 * Real.exp (-x)) := by
                refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
                simpa using h3
            _ = 2 := by rw [← mul_assoc, mul_comm _ 2, mul_assoc, ← Real.exp_add]; simp
        nlinarith [abs_nonneg c', Real.exp_pos x]
      · push Not at hx1 hx2
        refine le_max_of_le_left ?_
        have hxm : x ∈ Set.Icc (-R) R := ⟨hx2.le, hx1.le⟩
        have h4 := hB x hxm
        have hx3 : x ^ 2 ≤ R ^ 2 := by nlinarith [hxm.1, hxm.2]
        rw [Real.norm_eq_abs] at h4
        calc |g x| * (1 + x ^ 2) ≤ (max B 0) * (1 + R ^ 2) := by
              refine mul_le_mul (h4.trans (le_max_left _ _)) (by linarith) (by positivity)
                (le_max_right _ _)
          _ = (1 + R ^ 2) * max B 0 := mul_comm _ _
  obtain ⟨C, hC0, hC⟩ := hbound
  rw [memLp_two_iff_integrable_sq hg.aestronglyMeasurable]
  have hint : Integrable (fun x : ℝ => C ^ 2 * (1 + x ^ 2)⁻¹) :=
    (integrable_inv_one_add_sq).const_mul _
  refine Integrable.mono' hint ((hg.pow 2).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have h5 : |g x| ≤ C / (1 + x ^ 2) := by rw [le_div_iff₀ hpos]; exact hC x
  have h6 : (g x) ^ 2 = |g x| ^ 2 := (sq_abs _).symm
  rw [h6]
  calc |g x| ^ 2 ≤ (C / (1 + x ^ 2)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h5 2
    _ = C ^ 2 * (1 + x ^ 2)⁻¹ * (1 + x ^ 2)⁻¹ := by field_simp
    _ ≤ C ^ 2 * (1 + x ^ 2)⁻¹ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact inv_le_one_of_one_le₀ (by nlinarith [sq_nonneg x])
    _ = C ^ 2 * (1 + x ^ 2)⁻¹ := mul_one _

/-- **Solution of `v - v'' = ψ` in `L²`.** -/
theorem exists_resolvent_solution {ψ : ℝ → ℝ} (hψ : ψ ∈ A₀) :
    ∃ v : ℝ → ℝ, Sm v ∧ MemLp v 2 volume ∧ MemLp (deriv v) 2 volume ∧
      MemLp (deriv (deriv v)) 2 volume ∧ ∀ x, v x - deriv (deriv v) x = ψ x := by
  obtain ⟨R, hR, hRψ⟩ := exists_support_bound hψ
  have hψc : Continuous ψ := (smooth hψ).continuous
  have hψs : Sm ψ := smooth hψ
  set fa : ℝ → ℝ := fun y => Real.exp y * ψ y with hfa
  set fb : ℝ → ℝ := fun y => Real.exp (-y) * ψ y with hfb
  have hfac : Continuous fa := Real.continuous_exp.mul hψc
  have hfbc : Continuous fb := (Real.continuous_exp.comp continuous_neg).mul hψc
  have hfas : Sm fa := Real.contDiff_exp.mul hψs
  have hfbs : Sm fb := (Real.contDiff_exp.comp contDiff_neg).mul hψs
  set a : ℝ → ℝ := fun x => ∫ y in (-R)..x, fa y with ha
  set b : ℝ → ℝ := fun x => ∫ y in x..R, fb y with hb
  have hda : ∀ x, HasDerivAt a (fa x) x := fun x =>
    (hfac.integral_hasStrictDerivAt (-R) x).hasDerivAt
  have hdb : ∀ x, HasDerivAt b (-fb x) x := by
    intro x
    have h : ∀ x, b x = -∫ y in R..x, fb y := fun x => by
      simp only [hb]; rw [intervalIntegral.integral_symm]
    have := ((hfbc.integral_hasStrictDerivAt R x).hasDerivAt).neg
    exact this.congr_of_eventuallyEq (Filter.Eventually.of_forall h)
  have has : Sm a := sm_of_hasDerivAt hda hfas
  have hbs : Sm b := sm_of_hasDerivAt (fun x => (hdb x)) hfbs.neg
  -- tails
  have ha1 : ∀ x, x ≤ -R → a x = 0 := by
    intro x hx
    simp only [ha]
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_congr
      (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
    · simp
    · rw [Set.uIcc_of_le hx] at hy
      simp only [hfa]
      rw [hRψ y (by rw [abs_of_nonpos (by linarith [hy.2])]; linarith [hy.2])]; simp
  have ha2 : ∀ x, R ≤ x → a x = a R := by
    intro x hx
    have hadj := intervalIntegral.integral_add_adjacent_intervals (a := -R) (b := R) (c := x)
      (hfac.intervalIntegrable (μ := volume) _ _) (hfac.intervalIntegrable (μ := volume) _ _)
    have h0 : ∫ y in R..x, fa y = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
      · simp
      · rw [Set.uIcc_of_le hx] at hy
        simp only [hfa]
        rw [hRψ y (by rw [abs_of_nonneg (by linarith [hy.1])]; linarith [hy.1])]; simp
    simp only [ha]
    linarith
  have hb1 : ∀ x, R ≤ x → b x = 0 := by
    intro x hx
    simp only [hb]
    rw [intervalIntegral.integral_symm, intervalIntegral.integral_congr
      (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
    · simp
    · rw [Set.uIcc_of_le hx] at hy
      simp only [hfb]
      rw [hRψ y (by rw [abs_of_nonneg (by linarith [hy.1])]; linarith [hy.1])]; simp
  have hb2 : ∀ x, x ≤ -R → b x = b (-R) := by
    intro x hx
    have hadj := intervalIntegral.integral_add_adjacent_intervals (a := x) (b := -R) (c := R)
      (hfbc.intervalIntegrable (μ := volume) _ _) (hfbc.intervalIntegrable (μ := volume) _ _)
    have h0 : ∫ y in x..(-R), fb y = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) (fun y hy => ?_)]
      · simp
      · rw [Set.uIcc_of_le hx] at hy
        simp only [hfb]
        rw [hRψ y (by rw [abs_of_nonpos (by linarith [hy.2])]; linarith [hy.2])]; simp
    simp only [hb]
    linarith
  -- the solution
  set v : ℝ → ℝ := fun x => (Real.exp (-x) * a x + Real.exp x * b x) / 2 with hv
  set v1 : ℝ → ℝ := fun x => (-(Real.exp (-x) * a x) + Real.exp x * b x) / 2 with hv1
  have hexpneg : ∀ x, HasDerivAt (fun x : ℝ => Real.exp (-x)) (-Real.exp (-x)) x := fun x => by
    simpa using (hasDerivAt_neg x).exp
  have hdv : ∀ x, HasDerivAt v (v1 x) x := by
    intro x
    have h1 := ((hexpneg x).mul (hda x)).add ((Real.hasDerivAt_exp x).mul (hdb x))
    have h2 := h1.div_const 2
    refine h2.congr_deriv ?_
    simp only [hv1, hfa, hfb]
    have e1 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have e2 : Real.exp x * Real.exp (-x) = 1 := by rw [mul_comm]; exact e1
    have : -Real.exp (-x) * a x + Real.exp (-x) * (Real.exp x * ψ x) +
        (Real.exp x * b x + Real.exp x * -(Real.exp (-x) * ψ x)) =
        -(Real.exp (-x) * a x) + Real.exp x * b x := by
      have : Real.exp (-x) * (Real.exp x * ψ x) = ψ x := by rw [← mul_assoc, e1, one_mul]
      have h' : Real.exp x * -(Real.exp (-x) * ψ x) = -ψ x := by
        rw [mul_neg, ← mul_assoc, e2, one_mul]
      rw [this, h']; ring
    rw [this]
  have hdv1 : ∀ x, HasDerivAt v1 (v x - ψ x) x := by
    intro x
    have h1 := (((hexpneg x).mul (hda x)).neg).add ((Real.hasDerivAt_exp x).mul (hdb x))
    have h2 := h1.div_const 2
    refine h2.congr_deriv ?_
    simp only [hv, hfa, hfb]
    have e1 : Real.exp (-x) * Real.exp x = 1 := by rw [← Real.exp_add]; simp
    have e2 : Real.exp x * Real.exp (-x) = 1 := by rw [mul_comm]; exact e1
    have h3 : Real.exp (-x) * (Real.exp x * ψ x) = ψ x := by rw [← mul_assoc, e1, one_mul]
    have h' : Real.exp x * -(Real.exp (-x) * ψ x) = -ψ x := by
      rw [mul_neg, ← mul_assoc, e2, one_mul]
    have : -(-Real.exp (-x) * a x + Real.exp (-x) * (Real.exp x * ψ x)) +
        (Real.exp x * b x + Real.exp x * -(Real.exp (-x) * ψ x)) =
        (Real.exp (-x) * a x + Real.exp x * b x) - 2 * ψ x := by
      rw [h3, h']; ring
    rw [this]; ring
  have hderv : deriv v = v1 := funext fun x => (hdv x).deriv
  have hderv1 : deriv v1 = fun x => v x - ψ x := funext fun x => (hdv1 x).deriv
  have hvs : Sm v := by
    have : Sm (fun x => (Real.exp (-x) * a x + Real.exp x * b x) / 2) :=
      (((Real.contDiff_exp.comp contDiff_neg).mul has).add (Real.contDiff_exp.mul hbs)).div_const 2
    exact this
  have hvc : Continuous v := hvs.continuous
  have hv1c : Continuous v1 := (sm_of_hasDerivAt hdv1 (hvs.sub hψs)).continuous
  refine ⟨v, hvs, ?_, ?_, ?_, ?_⟩
  · refine memLp_of_exp_tails hvc hR (c := a R / 2) (c' := b (-R) / 2) (fun x hx => ?_) (fun x hx => ?_)
    · simp only [hv]; rw [ha2 x hx, hb1 x hx]; ring
    · simp only [hv]; rw [ha1 x hx, hb2 x hx]; ring
  · rw [hderv]
    refine memLp_of_exp_tails hv1c hR (c := -(a R) / 2) (c' := b (-R) / 2) (fun x hx => ?_) (fun x hx => ?_)
    · simp only [hv1]; rw [ha2 x hx, hb1 x hx]; ring
    · simp only [hv1]; rw [ha1 x hx, hb2 x hx]; ring
  · rw [hderv, hderv1]
    refine memLp_of_exp_tails (hvc.sub hψc) hR (c := a R / 2) (c' := b (-R) / 2) (fun x hx => ?_) (fun x hx => ?_)
    · simp only [hv]; rw [ha2 x hx, hb1 x hx, hRψ x (by rw [abs_of_nonneg (by linarith)]; exact hx)]; ring
    · simp only [hv]; rw [ha1 x hx, hb2 x hx, hRψ x (by rw [abs_of_nonpos (by linarith)]; linarith)]; ring
  · intro x
    rw [hderv, hderv1]; ring

end MarkovTriple.BGL.Lebesgue
