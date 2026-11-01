import Mathlib
import MarkovTriple.FunctionalInequalities.BEL2

/-! # Bakry–Émery (Phase 4b): differentiating `r ↦ ∫ Θ(a_r)` for an `L²`-valued curve `a` -/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal
open MarkovTriple.Hilbert (oneL2)

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

lemma sq_isLittleO_sub (s : ℝ) : (fun r : ℝ => (r - s) ^ 2) =o[𝓝 s] fun r => r - s := by
  have h1 : (fun x : ℝ => x ^ 2) =o[𝓝 0] (fun x : ℝ => x) :=
    Asymptotics.isLittleO_pow_id (by norm_num)
  have h2 : Tendsto (fun r : ℝ => r - s) (𝓝 s) (𝓝 0) := by
    have hc : Continuous fun r : ℝ => r - s := by fun_prop
    simpa using hc.tendsto s
  exact h1.comp_tendsto h2

lemma integrable_comp_L2 {Θ : ℝ → ℝ} (hΘ : Continuous Θ) {K₀ : ℝ} (h0 : ∀ x, |Θ x| ≤ K₀)
    (v : Lp ℝ 2 μ) : Integrable (fun x => Θ ((v : E → ℝ) x)) μ :=
  Integrable.mono' (integrable_const K₀)
    (hΘ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v))
    (Filter.Eventually.of_forall fun x => by simpa using h0 _)

lemma integrable_deriv_mul {Θ' : ℝ → ℝ} (hΘ : Continuous Θ') {K₁ : ℝ} (h1 : ∀ x, |Θ' x| ≤ K₁)
    (v w : Lp ℝ 2 μ) : Integrable (fun x => Θ' ((v : E → ℝ) x) * (w : E → ℝ) x) μ := by
  have hw : Integrable (fun x => (w : E → ℝ) x) μ := (Lp.memLp w).integrable one_le_two
  refine Integrable.mono' (hw.abs.const_mul K₁)
    ((hΘ.comp_aestronglyMeasurable (Lp.aestronglyMeasurable v)).mul (Lp.aestronglyMeasurable w))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (h1 _) (abs_nonneg _)

theorem hasDerivAt_int_comp {Θ : ℝ → ℝ} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) {K₀ K₁ K₂ : ℝ}
    (h0 : ∀ x, |Θ x| ≤ K₀) (h1 : ∀ x, |deriv Θ x| ≤ K₁)
    (h2 : ∀ x, |deriv (deriv Θ) x| ≤ K₂)
    {a : ℝ → Lp ℝ 2 μ} {a' : Lp ℝ 2 μ} {s : ℝ} (ha : HasDerivAt a a' s) :
    HasDerivAt (fun r => ∫ x, Θ ((a r : E → ℝ) x) ∂μ)
      (∫ x, deriv Θ ((a s : E → ℝ) x) * (a' : E → ℝ) x ∂μ) s := by
  have hK₁ : 0 ≤ K₁ := (abs_nonneg _).trans (h1 0)
  have hK₂ : 0 ≤ K₂ := (abs_nonneg _).trans (h2 0)
  have hΘc : Continuous Θ := hΘ.continuous
  have hΘ'c : Continuous (deriv Θ) := (contDiff_deriv_top hΘ).continuous
  rw [hasDerivAt_iff_isLittleO]
  set c₀ : ℝ := ‖oneL2 μ‖ with hc₀
  have hd : (fun r => a r - a s - (r - s) • a') =o[𝓝 s] fun r => r - s :=
    hasDerivAt_iff_isLittleO.1 ha
  have hbig : (fun r => a r - a s) =O[𝓝 s] fun r => r - s := ha.isBigO_sub
  -- pointwise bound
  have key : ∀ r : ℝ, ‖(∫ x, Θ ((a r : E → ℝ) x) ∂μ) - (∫ x, Θ ((a s : E → ℝ) x) ∂μ) -
      (r - s) • (∫ x, deriv Θ ((a s : E → ℝ) x) * (a' : E → ℝ) x ∂μ)‖ ≤
      K₂ * ‖a r - a s‖ ^ 2 + K₁ * c₀ * ‖a r - a s - (r - s) • a'‖ := by
    intro r
    set u : Lp ℝ 2 μ := a r - a s with hu
    set d : Lp ℝ 2 μ := a r - a s - (r - s) • a' with hd'
    have hu' : (u : E → ℝ) =ᵐ[μ] fun x => (a r : E → ℝ) x - (a s : E → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (a r) (a s)] with x hx
      rw [hu, hx]; rfl
    have hd'' : (d : E → ℝ) =ᵐ[μ] fun x =>
        (a r : E → ℝ) x - (a s : E → ℝ) x - (r - s) * (a' : E → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (a r - a s) ((r - s) • a'), Lp.coeFn_sub (a r) (a s),
        Lp.coeFn_smul (r - s) a'] with x h1 h2 h3
      rw [hd', h1]
      simp only [Pi.sub_apply] at h2 ⊢
      rw [h2, h3]; simp
    -- the decomposition
    have iA : Integrable (fun x => Θ ((a r : E → ℝ) x) - Θ ((a s : E → ℝ) x) -
        deriv Θ ((a s : E → ℝ) x) * ((a r : E → ℝ) x - (a s : E → ℝ) x)) μ := by
      refine ((integrable_comp_L2 hΘc h0 (a r)).sub (integrable_comp_L2 hΘc h0 (a s))).sub ?_
      exact (integrable_deriv_mul hΘ'c h1 (a s) u).congr
        (by filter_upwards [hu'] with x hx; rw [hx])
    have iB : Integrable (fun x => deriv Θ ((a s : E → ℝ) x) * (d : E → ℝ) x) μ :=
      integrable_deriv_mul hΘ'c h1 (a s) d
    have iD : Integrable (fun x => deriv Θ ((a s : E → ℝ) x) * (a' : E → ℝ) x) μ :=
      integrable_deriv_mul hΘ'c h1 (a s) a'
    have eq1 : (∫ x, Θ ((a r : E → ℝ) x) ∂μ) - (∫ x, Θ ((a s : E → ℝ) x) ∂μ) -
        (r - s) • (∫ x, deriv Θ ((a s : E → ℝ) x) * (a' : E → ℝ) x ∂μ) =
        (∫ x, (Θ ((a r : E → ℝ) x) - Θ ((a s : E → ℝ) x) -
          deriv Θ ((a s : E → ℝ) x) * ((a r : E → ℝ) x - (a s : E → ℝ) x)) ∂μ) +
        ∫ x, deriv Θ ((a s : E → ℝ) x) * (d : E → ℝ) x ∂μ := by
      have iΘr := integrable_comp_L2 hΘc h0 (a r)
      have iΘs := integrable_comp_L2 hΘc h0 (a s)
      have e1 : (∫ x, Θ ((a r : E → ℝ) x) ∂μ) - (∫ x, Θ ((a s : E → ℝ) x) ∂μ) -
          (r - s) • (∫ x, deriv Θ ((a s : E → ℝ) x) * (a' : E → ℝ) x ∂μ) =
          ∫ x, (Θ ((a r : E → ℝ) x) - Θ ((a s : E → ℝ) x) -
            (r - s) * (deriv Θ ((a s : E → ℝ) x) * (a' : E → ℝ) x)) ∂μ := by
        have iΘd : Integrable (fun x => Θ ((a r : E → ℝ) x) - Θ ((a s : E → ℝ) x)) μ :=
          iΘr.sub iΘs
        have iDc : Integrable (fun x => (r - s) * (deriv Θ ((a s : E → ℝ) x) *
            (a' : E → ℝ) x)) μ := iD.const_mul _
        rw [integral_sub iΘd iDc, integral_sub iΘr iΘs, integral_const_mul, smul_eq_mul]
      rw [e1, ← integral_add iA iB]
      refine integral_congr_ae ?_
      filter_upwards [hd''] with x hx
      rw [hx]; ring
    rw [eq1]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · -- Taylor
      have hb : ∀ᵐ x ∂μ, ‖Θ ((a r : E → ℝ) x) - Θ ((a s : E → ℝ) x) -
          deriv Θ ((a s : E → ℝ) x) * ((a r : E → ℝ) x - (a s : E → ℝ) x)‖ ≤
          K₂ * ((u : E → ℝ) x) ^ 2 := by
        filter_upwards [hu'] with x hx
        rw [hx, Real.norm_eq_abs]
        exact taylor2 hΘ h2 _ _
      refine (norm_integral_le_of_norm_le ((integrable_sq_L2 u).const_mul K₂) hb).trans ?_
      rw [integral_const_mul, int_sq_L2]
    · have := abs_int_two_le (φ := fun x => deriv Θ ((a s : E → ℝ) x)) hK₁
        (Filter.Eventually.of_forall fun x => h1 _) d
      rw [Real.norm_eq_abs]
      calc _ ≤ K₁ * (‖d‖ * c₀) := this
        _ = K₁ * c₀ * ‖d‖ := by ring
  -- asymptotics
  have h2o : (fun r => ‖a r - a s‖ ^ 2) =o[𝓝 s] fun r => r - s := by
    have := (hbig.norm_left.pow 2)
    exact this.trans_isLittleO (sq_isLittleO_sub s)
  have hdo : (fun r => ‖a r - a s - (r - s) • a'‖) =o[𝓝 s] fun r => r - s := hd.norm_left
  have hg : (fun r => K₂ * ‖a r - a s‖ ^ 2 + K₁ * c₀ * ‖a r - a s - (r - s) • a'‖)
      =o[𝓝 s] fun r => r - s :=
    (h2o.const_mul_left K₂).add (hdo.const_mul_left (K₁ * c₀))
  refine IsBigO.trans_isLittleO ?_ hg
  refine IsBigO.of_bound 1 (Filter.Eventually.of_forall fun r => ?_)
  refine (key r).trans ?_
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

end MarkovTriple.BE
