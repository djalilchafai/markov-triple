import Mathlib

/-!
# Bounds for smooth compactly supported functions of one variable
(bound, Lipschitz constant, quadratic Taylor remainder)
-/

open Set

namespace MarkovTriple.BGL.Compact

lemma lip_of_deriv {f : ℝ → ℝ} {K : ℝ} (hd : Differentiable ℝ f) (hb : ∀ x, |deriv f x| ≤ K) :
    ∀ x y, |f y - f x| ≤ K * |y - x| := by
  intro x y
  have := (convex_univ (𝕜 := ℝ) (E := ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun z _ => (hd z)) (fun z _ => by simpa [Real.norm_eq_abs] using hb z) (mem_univ x) (mem_univ y)
  simpa [Real.norm_eq_abs] using this

lemma taylor_of_deriv {F : ℝ → ℝ} {K2 : ℝ} (hd : Differentiable ℝ F)
    (hd2 : Differentiable ℝ (deriv F)) (hb2 : ∀ x, |deriv (deriv F) x| ≤ K2) :
    ∀ x y, |F y - F x - deriv F x * (y - x)| ≤ K2 * (y - x) ^ 2 := by
  intro x y
  have hlip := lip_of_deriv hd2 hb2
  set D : ℝ → ℝ := fun z => F z - F x - deriv F x * (z - x) with hD
  have hDd : ∀ z, HasDerivAt D (deriv F z - deriv F x) z := by
    intro z
    have h1 := (hd z).hasDerivAt
    have h2 : HasDerivAt (fun z => deriv F x * (z - x)) (deriv F x) z :=
      ((hasDerivAt_id z).sub_const x).const_mul _ |>.congr_deriv (by simp)
    exact (h1.sub_const (F x)).sub h2
  have key := (convex_uIcc x y).norm_image_sub_le_of_norm_deriv_le (f := D) (C := K2 * |y - x|)
    (fun z _ => (hDd z).differentiableAt)
    (fun z hz => by
      rw [(hDd z).deriv, Real.norm_eq_abs]
      calc |deriv F z - deriv F x| ≤ K2 * |z - x| := hlip x z
        _ ≤ K2 * |y - x| := by
          have : |z - x| ≤ |y - x| := Set.abs_sub_left_of_mem_uIcc hz
          have hK2 : 0 ≤ K2 := (abs_nonneg _).trans (hb2 0)
          exact mul_le_mul_of_nonneg_left this hK2)
    left_mem_uIcc right_mem_uIcc
  simp only [hD, sub_self, mul_zero, sub_zero, Real.norm_eq_abs] at key
  calc |F y - F x - deriv F x * (y - x)| ≤ K2 * |y - x| * |y - x| := key
    _ = K2 * (y - x) ^ 2 := by rw [mul_assoc, ← sq_abs (y - x), sq]

lemma smooth_bounds {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hc : HasCompactSupport F) :
    ∃ K0 K1 K2 : ℝ, 0 ≤ K0 ∧ 0 ≤ K1 ∧ 0 ≤ K2 ∧ (∀ y, |F y| ≤ K0) ∧
      (∀ y, |deriv F y| ≤ K1) ∧ (∀ y, |deriv (deriv F) y| ≤ K2) := by
  have hF1 : ContDiff ℝ (⊤ : ℕ∞) (deriv F) := by
    have := (contDiff_infty_iff_deriv.1 hF).2
    exact this
  have hF2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv F)) :=
    (contDiff_infty_iff_deriv.1 hF1).2
  obtain ⟨K0, h0⟩ := hF.continuous.bounded_above_of_compact_support hc
  obtain ⟨K1, h1⟩ := hF1.continuous.bounded_above_of_compact_support hc.deriv
  obtain ⟨K2, h2⟩ := hF2.continuous.bounded_above_of_compact_support hc.deriv.deriv
  refine ⟨|K0|, |K1|, |K2|, abs_nonneg _, abs_nonneg _, abs_nonneg _, fun y => ?_, fun y => ?_,
    fun y => ?_⟩
  · exact (by simpa [Real.norm_eq_abs] using h0 y : |F y| ≤ K0).trans (le_abs_self _)
  · exact (by simpa [Real.norm_eq_abs] using h1 y : |deriv F y| ≤ K1).trans (le_abs_self _)
  · exact (by simpa [Real.norm_eq_abs] using h2 y : |deriv (deriv F) y| ≤ K2).trans (le_abs_self _)

end MarkovTriple.BGL.Compact
