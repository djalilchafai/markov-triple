import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDerivAux2

/-!
# Gaussian moments and `L¹` estimate of the remainder (Round 24, stream A, part H-b)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

lemma integrable_abs_pow_gam (k : ℕ) (i : Fin d) :
    Integrable (fun z : Fin d → ℝ => |z i| ^ k) (gam d) :=
  ((measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).integrable_comp
    (g := fun x : ℝ => |x| ^ k) (by fun_prop)).2
    (MarkovTriple.BGL.Lebesgue.integrable_abs_pow_gauss k)

lemma integrable_norm_pow_gam (k : ℕ) : Integrable (fun z : Fin d → ℝ => ‖z‖ ^ k) (gam d) := by
  by_cases hk : k = 0
  · subst hk; simp
  refine Integrable.mono' (integrable_finsetSum Finset.univ fun i _ => integrable_abs_pow_gam k i)
    (continuous_norm.pow k).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  rcases isEmpty_or_nonempty (Fin d) with he | hne
  · rw [Subsingleton.elim z 0]; simp [hk]
  · obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun j => ‖z j‖) Finset.univ_nonempty
    have : ‖z‖ ≤ ‖z i‖ := (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => hi j (Finset.mem_univ _)
    calc ‖z‖ ^ k ≤ ‖z i‖ ^ k := pow_le_pow_left₀ (norm_nonneg _) this k
      _ = |z i| ^ k := by rw [Real.norm_eq_abs]
      _ ≤ _ := Finset.single_le_sum (f := fun j => |z j| ^ k) (fun j _ => by positivity)
          (Finset.mem_univ i)

lemma integrable_Wd (C₂ R a : ℝ) : Integrable (Wd (d := d) C₂ R a) (gam d) := by
  set P : Polynomial ℝ := Polynomial.C C₂ * Polynomial.X ^ 2 *
    (Polynomial.C (2 * R) + Polynomial.C (2 * (|a| + 1)) * Polynomial.X) ^ d with hP
  have h : Wd (d := d) C₂ R a = fun z => P.eval ‖z‖ := by
    funext z
    simp only [Wd, hP, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add,
      Polynomial.eval_C, Polynomial.eval_X]
    congr 2
    ring
  rw [h]
  simp_rw [Polynomial.eval_eq_sum_range]
  exact integrable_finsetSum _ fun i _ => (integrable_norm_pow_gam i).const_mul _

lemma rhoD_integrable {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) {C₂ : ℝ}
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C₂) (a : ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, R < ‖y‖ → φ y = 0 ∧ fderiv ℝ φ y = 0)
    {h : ℝ} (hh0 : h ≠ 0) (hh : |h| ≤ 1) :
    Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => rhoD φ a h p.1 p.2) (volume.prod (gam d)) := by
  have hc : Continuous φ := (smooth hφ).continuous
  have hfd : Continuous (fderiv ℝ φ) := (smooth hφ).continuous_fderiv (by simp)
  have hcont : Continuous (fun p : (Fin d → ℝ) × (Fin d → ℝ) => rhoD φ a h p.1 p.2) := by
    unfold rhoD
    fun_prop
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  refine ⟨ae_of_all _ fun z => ?_, ?_⟩
  · refine (hcont.comp (by fun_prop : Continuous fun x : Fin d → ℝ => (x, z))).integrable_of_hasCompactSupport ?_
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin d → ℝ) (R + (|a| + 1) * ‖z‖))
      fun x hx => ?_
    rw [mem_closedBall_zero_iff, not_le] at hx
    exact rhoD_eq_zero a hR hh hx
  · refine Integrable.mono' (g := fun z => |h| * Wd C₂ R a z)
      ((integrable_Wd C₂ R a).const_mul _) ?_ (ae_of_all _ fun z => ?_)
    · have hm : AEStronglyMeasurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => ‖rhoD φ a h p.1 p.2‖)
          (volume.prod (gam d)) := hcont.norm.aestronglyMeasurable
      exact hm.prod_swap.integral_prod_right'
    · rw [Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
      simpa using integral_abs_rhoD_le (smooth hφ) hC₂ a hR0 hR hh0 hh z

lemma integral_abs_q_le {φ : (Fin d → ℝ) → ℝ} (hφ : φ ∈ A₀ d) {C₂ : ℝ}
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C₂) (a : ℝ) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, R < ‖y‖ → φ y = 0 ∧ fderiv ℝ φ y = 0) {h : ℝ} (hh0 : h ≠ 0) (hh : |h| ≤ 1) :
    ∫ x, |∫ z, rhoD φ a h x z ∂(gam d)| ≤ |h| * ∫ z, Wd C₂ R a z ∂(gam d) := by
  have hI := rhoD_integrable hφ hC₂ a hR0 hR hh0 hh
  have hB : Integrable (fun z => |h| * Wd C₂ R a z) (gam d) := (integrable_Wd C₂ R a).const_mul _
  calc ∫ x, |∫ z, rhoD φ a h x z ∂(gam d)|
      ≤ ∫ x, ∫ z, ‖rhoD φ a h x z‖ ∂(gam d) := by
        refine integral_mono hI.integral_prod_left.norm hI.norm.integral_prod_left fun x => ?_
        simpa using norm_integral_le_integral_norm (μ := gam d) (fun z => rhoD φ a h x z)
    _ = ∫ z, ∫ x, ‖rhoD φ a h x z‖ ∂volume ∂(gam d) :=
        integral_integral_swap (f := fun x z => ‖rhoD φ a h x z‖) hI.norm
    _ ≤ ∫ z, |h| * Wd C₂ R a z ∂(gam d) := by
        refine integral_mono hI.integral_norm_prod_right hB fun z => ?_
        simpa using integral_abs_rhoD_le (smooth hφ) hC₂ a hR0 hR hh0 hh z
    _ = _ := integral_const_mul _ _

end MarkovTriple.BGL.LebesgueRd
