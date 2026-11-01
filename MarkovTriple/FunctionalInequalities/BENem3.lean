import Mathlib
import MarkovTriple.FunctionalInequalities.BENem2

/-! # Bakry–Émery (Phase 4b): continuity of the Nemytskii functionals along `L²`-curves -/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal
open MarkovTriple.Hilbert (oneL2)

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- global Lipschitz bound from a bound on the derivative -/
lemma abs_sub_le_of_deriv {Θ : ℝ → ℝ} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) {K : ℝ}
    (h1 : ∀ x, |deriv Θ x| ≤ K) (x y : ℝ) : |Θ y - Θ x| ≤ K * |y - x| := by
  have hd : Differentiable ℝ Θ := hΘ.differentiable (by simp)
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := Θ) (s := Set.univ) (C := K)
    (fun z _ => hd z) (fun z _ => by simpa using h1 z) convex_univ (Set.mem_univ x)
    (Set.mem_univ y)
  simpa using this

lemma abs_int_comp_sub_le {Θ : ℝ → ℝ} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) {K₀ K₁ : ℝ}
    (h0 : ∀ x, |Θ x| ≤ K₀) (h1 : ∀ x, |deriv Θ x| ≤ K₁) (v w : Lp ℝ 2 μ) :
    |(∫ x, Θ ((v : E → ℝ) x) ∂μ) - ∫ x, Θ ((w : E → ℝ) x) ∂μ| ≤
      K₁ * (‖v - w‖ * ‖oneL2 μ‖) := by
  have hK₁ : 0 ≤ K₁ := (abs_nonneg _).trans (h1 0)
  have hΘc : Continuous Θ := hΘ.continuous
  set u : Lp ℝ 2 μ := v - w with hu
  have hu' : (u : E → ℝ) =ᵐ[μ] fun x => (v : E → ℝ) x - (w : E → ℝ) x := by
    filter_upwards [Lp.coeFn_sub v w] with x hx
    rw [hu, hx]; rfl
  rw [← integral_sub (integrable_comp_L2 hΘc h0 v) (integrable_comp_L2 hΘc h0 w)]
  have hint : Integrable (fun x => (u : E → ℝ) x) μ := (Lp.memLp u).integrable one_le_two
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (hint.abs.const_mul K₁) ?_).trans ?_
  · filter_upwards [hu'] with x hx
    rw [hx, Real.norm_eq_abs]
    simpa [abs_sub_comm] using abs_sub_le_of_deriv hΘ h1 ((w : E → ℝ) x) ((v : E → ℝ) x)
  · rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ hK₁
    have h2 := abs_int_two_le (φ := fun _ => (1 : ℝ)) (C := 1) zero_le_one
      (Filter.Eventually.of_forall fun x => by simp) (|u|)
    have e : ∫ x, |(u : E → ℝ) x| ∂μ = ∫ x, (1 : ℝ) * (|u| : Lp ℝ 2 μ) x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_abs u] with x hx
      rw [hx]; simp
    rw [e]
    refine (le_abs_self _).trans (h2.trans ?_)
    rw [norm_abs_L2]; simp

theorem continuousAt_int_comp {Θ : ℝ → ℝ} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) {K₀ K₁ : ℝ}
    (h0 : ∀ x, |Θ x| ≤ K₀) (h1 : ∀ x, |deriv Θ x| ≤ K₁)
    {a : ℝ → Lp ℝ 2 μ} {s : ℝ} (ha : ContinuousAt a s) :
    ContinuousAt (fun r => ∫ x, Θ ((a r : E → ℝ) x) ∂μ) s := by
  have hbound := fun r => abs_int_comp_sub_le hΘ h0 h1 (a r) (a s)
  have hc : Tendsto (fun r => ‖a r - a s‖) (𝓝 s) (𝓝 0) := by
    have := ((ha.sub (continuousAt_const (y := a s))).norm).tendsto
    simpa using this
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (a := fun r => K₁ * (‖a r - a s‖ * ‖oneL2 μ‖)) (fun r => ?_) ?_
  · exact (Real.norm_eq_abs _).le.trans (hbound r)
  · have := (hc.mul_const ‖oneL2 μ‖).const_mul K₁
    simpa using this

theorem continuousAt_int_comp_mul {Λ : ℝ → ℝ} (hΛ : ContDiff ℝ (⊤ : ℕ∞) Λ) {K₀ K₁ : ℝ}
    (h0 : ∀ x, |Λ x| ≤ K₀) (h1 : ∀ x, |deriv Λ x| ≤ K₁)
    {a b : ℝ → Lp ℝ 2 μ} {s : ℝ} (ha : ContinuousAt a s) (hb : ContinuousAt b s) :
    ContinuousAt (fun r => ∫ x, Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x ∂μ) s := by
  have hK₀ : 0 ≤ K₀ := (abs_nonneg _).trans (h0 0)
  have hK₁ : 0 ≤ K₁ := (abs_nonneg _).trans (h1 0)
  have hΛc : Continuous Λ := hΛ.continuous
  have hbound : ∀ r, |(∫ x, Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x ∂μ) -
      ∫ x, Λ ((a s : E → ℝ) x) * (b s : E → ℝ) x ∂μ| ≤
      K₁ * (‖a r - a s‖ * (‖b s‖ + ‖b r - b s‖)) + K₀ * (‖b r - b s‖ * ‖oneL2 μ‖) := by
    intro r
    set u : Lp ℝ 2 μ := a r - a s with hu
    set p : Lp ℝ 2 μ := b r - b s with hp
    have hu' : (u : E → ℝ) =ᵐ[μ] fun x => (a r : E → ℝ) x - (a s : E → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (a r) (a s)] with x hx
      rw [hu, hx]; rfl
    have hp' : (p : E → ℝ) =ᵐ[μ] fun x => (b r : E → ℝ) x - (b s : E → ℝ) x := by
      filter_upwards [Lp.coeFn_sub (b r) (b s)] with x hx
      rw [hp, hx]; rfl
    have iQ1 := integrable_deriv_mul hΛc h0 (a r) (b r)
    have iQ2 := integrable_deriv_mul hΛc h0 (a s) (b s)
    have iT1 : Integrable (fun x => (Λ ((a r : E → ℝ) x) - Λ ((a s : E → ℝ) x)) *
        (b r : E → ℝ) x) μ := by
      have := (integrable_deriv_mul hΛc h0 (a r) (b r)).sub
        (integrable_deriv_mul hΛc h0 (a s) (b r))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]; ring
    have iT2 : Integrable (fun x => Λ ((a s : E → ℝ) x) * (p : E → ℝ) x) μ :=
      integrable_deriv_mul hΛc h0 (a s) p
    have e1 : (∫ x, Λ ((a r : E → ℝ) x) * (b r : E → ℝ) x ∂μ) -
        ∫ x, Λ ((a s : E → ℝ) x) * (b s : E → ℝ) x ∂μ =
        (∫ x, (Λ ((a r : E → ℝ) x) - Λ ((a s : E → ℝ) x)) * (b r : E → ℝ) x ∂μ) +
        ∫ x, Λ ((a s : E → ℝ) x) * (p : E → ℝ) x ∂μ := by
      rw [← integral_sub iQ1 iQ2, ← integral_add iT1 iT2]
      refine integral_congr_ae ?_
      filter_upwards [hp'] with x hx
      rw [hx]; ring
    rw [e1, ← Real.norm_eq_abs]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · have hint : Integrable (fun x => |(u : E → ℝ) x| * |(b r : E → ℝ) x|) μ :=
        integrable_abs_mul u (b r)
      refine (norm_integral_le_of_norm_le (hint.const_mul K₁) ?_).trans ?_
      · filter_upwards [hu'] with x hx
        rw [Real.norm_eq_abs, abs_mul, hx, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right
          (abs_sub_le_of_deriv hΛ h1 ((a s : E → ℝ) x) ((a r : E → ℝ) x)) (abs_nonneg _)
      · rw [integral_const_mul]
        have hbr : ‖b r‖ ≤ ‖b s‖ + ‖b r - b s‖ := by
          have := norm_le_norm_add_norm_sub' (b r) (b s)
          linarith [norm_sub_rev (b r) (b s)]
        calc K₁ * ∫ x, |(u : E → ℝ) x| * |(b r : E → ℝ) x| ∂μ
            ≤ K₁ * (‖u‖ * ‖b r‖) := mul_le_mul_of_nonneg_left (int_abs_mul_le u (b r)) hK₁
          _ ≤ K₁ * (‖a r - a s‖ * (‖b s‖ + ‖b r - b s‖)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbr (norm_nonneg _)) hK₁
    · have := abs_int_two_le (φ := fun x => Λ ((a s : E → ℝ) x)) hK₀
        (Filter.Eventually.of_forall fun x => h0 _) p
      rw [Real.norm_eq_abs]
      exact this
  have hc : Tendsto (fun r => ‖a r - a s‖) (𝓝 s) (𝓝 0) := by
    have := ((ha.sub (continuousAt_const (y := a s))).norm).tendsto
    simpa using this
  have hc' : Tendsto (fun r => ‖b r - b s‖) (𝓝 s) (𝓝 0) := by
    have := ((hb.sub (continuousAt_const (y := b s))).norm).tendsto
    simpa using this
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm (a := fun r => K₁ * (‖a r - a s‖ * (‖b s‖ + ‖b r - b s‖)) +
    K₀ * (‖b r - b s‖ * ‖oneL2 μ‖)) (fun r => ?_) ?_
  · exact (Real.norm_eq_abs _).le.trans (hbound r)
  · have h1' := (hc.mul ((tendsto_const_nhds (x := ‖b s‖)).add hc')).const_mul K₁
    have h2' := (hc'.mul_const ‖oneL2 μ‖).const_mul K₀
    have := h1'.add h2'
    simpa using this

end MarkovTriple.BE
