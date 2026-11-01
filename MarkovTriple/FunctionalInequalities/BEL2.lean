import Mathlib
import MarkovTriple.FunctionalInequalities.BEBdd
import MarkovTriple.FunctionalInequalities.BEChain
import MarkovTriple.FunctionalInequalities.FormDomain

/-! # Bakry–Émery (Phase 4b): `L²`-valued calculus for Nemytskii functionals

For `Θ : ℝ → ℝ` smooth with bounded derivatives and a curve `a : ℝ → L²(μ)` (finite `μ`) which is
differentiable at `s`, the real function `r ↦ ∫ Θ(a_r) dμ` is differentiable at `s` with derivative
`∫ Θ'(a_s) a'`.  (`hasDerivAt_int_comp`.)  The second-order companion, for
`r ↦ ∫ Θ'(a_r) b_r` with `b_r` uniformly bounded, is `hasDerivAt_int_comp_mul`. -/

open MeasureTheory Filter Topology Asymptotics
open scoped ENNReal
open MarkovTriple.Hilbert (oneL2)

namespace MarkovTriple.BE

lemma contDiff_deriv_top {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv φ) := contDiff_deriv' hφ

/-- Taylor remainder of order 1 with a global bound on `Θ''`. -/
lemma taylor2 {Θ : ℝ → ℝ} (hΘ : ContDiff ℝ (⊤ : ℕ∞) Θ) {K : ℝ}
    (hK : ∀ x, |deriv (deriv Θ) x| ≤ K) (x y : ℝ) :
    |Θ y - Θ x - deriv Θ x * (y - x)| ≤ K * (y - x) ^ 2 := by
  have hd : Differentiable ℝ Θ := hΘ.differentiable (by simp)
  have hd1 : ContDiff ℝ (⊤ : ℕ∞) (deriv Θ) := contDiff_deriv_top hΘ
  have hd1d : Differentiable ℝ (deriv Θ) := hd1.differentiable (by simp)
  have hlip : ∀ t, ‖deriv Θ t - deriv Θ x‖ ≤ K * ‖t - x‖ := fun t =>
    Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv Θ) (s := Set.univ) (C := K)
      (fun z _ => hd1d z) (fun z _ => by simpa using hK z) convex_univ (Set.mem_univ _)
      (Set.mem_univ _)
  have hftc : ∫ t in x..y, deriv Θ t = Θ y - Θ x :=
    intervalIntegral.integral_deriv_eq_sub' Θ rfl (fun z _ => (hd z))
      hd1.continuous.continuousOn
  have hint : IntervalIntegrable (deriv Θ) MeasureTheory.volume x y :=
    hd1.continuous.intervalIntegrable _ _
  have hsub : ∫ t in x..y, (deriv Θ t - deriv Θ x) = Θ y - Θ x - deriv Θ x * (y - x) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hftc]
    simp
    ring
  rw [← hsub]
  have hb : ∀ t ∈ Set.uIoc x y, ‖deriv Θ t - deriv Θ x‖ ≤ K * |y - x| := by
    intro t ht
    refine (hlip t).trans ?_
    have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK x)
    refine mul_le_mul_of_nonneg_left ?_ hK0
    rw [Real.norm_eq_abs]
    rcases le_total x y with h | h
    · rw [Set.uIoc_of_le h] at ht
      rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (by linarith)]
      linarith [ht.2]
    · rw [Set.uIoc_of_ge h] at ht
      rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (by linarith)]
      linarith [ht.1]
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs] at this
  calc _ ≤ K * |y - x| * |y - x| := this
    _ = K * (y - x) ^ 2 := by rw [mul_assoc, ← sq, sq_abs]

section CS

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

lemma norm_abs_L2 (u : Lp ℝ 2 μ) : ‖|u|‖ = ‖u‖ := by
  have h : inner ℝ |u| |u| = inner ℝ u u := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_abs u] with x hx
    rw [hx]
    simp
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg |u|, norm_nonneg u, sq_nonneg (‖|u|‖ - ‖u‖), sq_nonneg (‖|u|‖ + ‖u‖)]

lemma integrable_abs_mul (u v : Lp ℝ 2 μ) :
    Integrable (fun x => |(u : E → ℝ) x| * |(v : E → ℝ) x|) μ := by
  have := ((Lp.memLp u).integrable_mul (Lp.memLp v)).abs
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp [abs_mul]

lemma int_abs_mul_le (u v : Lp ℝ 2 μ) :
    ∫ x, |(u : E → ℝ) x| * |(v : E → ℝ) x| ∂μ ≤ ‖u‖ * ‖v‖ := by
  have h := real_inner_le_norm (|u|) (|v|)
  rw [norm_abs_L2, norm_abs_L2] at h
  refine le_trans (le_of_eq ?_) h
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_abs u, Lp.coeFn_abs v] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

lemma int_sq_L2 (u : Lp ℝ 2 μ) : ∫ x, ((u : E → ℝ) x) ^ 2 ∂μ = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [sq]

lemma integrable_sq_L2 (u : Lp ℝ 2 μ) : Integrable (fun x => ((u : E → ℝ) x) ^ 2) μ := by
  have := (Lp.memLp u).integrable_sq
  exact this

lemma abs_int_three_le {φ : E → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, |φ x| ≤ C)
    (u v : Lp ℝ 2 μ) :
    |∫ x, φ x * ((u : E → ℝ) x * (v : E → ℝ) x) ∂μ| ≤ C * (‖u‖ * ‖v‖) := by
  have h1 : ‖∫ x, φ x * ((u : E → ℝ) x * (v : E → ℝ) x) ∂μ‖ ≤
      ∫ x, C * (|(u : E → ℝ) x| * |(v : E → ℝ) x|) ∂μ := by
    refine norm_integral_le_of_norm_le ((integrable_abs_mul u v).const_mul C) ?_
    filter_upwards [hC] with x hx
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (by positivity)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (int_abs_mul_le u v) hC0

variable [IsFiniteMeasure μ]

lemma abs_int_two_le {φ : E → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂μ, |φ x| ≤ C)
    (u : Lp ℝ 2 μ) :
    |∫ x, φ x * (u : E → ℝ) x ∂μ| ≤ C * (‖u‖ * ‖oneL2 μ‖) := by
  have h := abs_int_three_le hC0 hC u (oneL2 μ)
  have h1 : ((oneL2 μ : Lp ℝ 2 μ) : E → ℝ) =ᵐ[μ] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  have e : ∫ x, φ x * ((u : E → ℝ) x * ((oneL2 μ : Lp ℝ 2 μ) : E → ℝ) x) ∂μ =
      ∫ x, φ x * (u : E → ℝ) x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [h1] with x hx
    rw [hx]; ring
  rwa [e] at h

end CS

end MarkovTriple.BE
