import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDerivAux4

/-!
# `L²` estimate of the difference quotient (Round 24, stream A, part H-b)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ : (Fin d → ℝ) → ℝ}

lemma exists_C₂ (hφ : φ ∈ A₀ d) : ∃ C₂ : ℝ, ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C₂ := by
  have hφ' : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) :=
    (smooth hφ).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  have hc : Continuous (fderiv ℝ (fderiv ℝ φ)) := hφ'.continuous_fderiv (by simp)
  have hcs : HasCompactSupport (fderiv ℝ (fderiv ℝ φ)) := by
    have h1 : HasCompactSupport (fderiv ℝ φ) := (cs hφ).fderiv (𝕜 := ℝ)
    exact h1.fderiv (𝕜 := ℝ)
  have hn : Continuous (fun y => ‖fderiv ℝ (fderiv ℝ φ) y‖) :=
    Continuous.norm (E := (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) hc
  have hns : HasCompactSupport (fun y => ‖fderiv ℝ (fderiv ℝ φ) y‖) :=
    HasCompactSupport.norm (E := (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) →L[ℝ] ℝ) hcs
  obtain ⟨C, hC⟩ := Continuous.bounded_above_of_compact_support (f := fun y => ‖fderiv ℝ (fderiv ℝ φ) y‖) hn hns
  exact ⟨C, fun y => by
    have := hC y
    exact (Real.norm_of_nonneg (norm_nonneg (fderiv ℝ (fderiv ℝ φ) y))).symm.le.trans this⟩

lemma norm_toLp_le {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) {S T : ℝ} (hS : 0 ≤ S)
    (hSf : ∀ x, |f x| ≤ S) (hfi : Integrable f volume) (hT : ∫ x, |f x| ≤ T) :
    ‖hf.toLp f‖ ≤ √(S * T) := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
    ENNReal.toReal_ofReal (by positivity)]
  have h2 : (2 : ENNReal).toReal = 2 := by simp
  rw [h2, Real.sqrt_eq_rpow, one_div]
  refine Real.rpow_le_rpow (integral_nonneg fun x => by positivity) ?_ (by norm_num)
  have hint : Integrable (fun x => ‖f x‖ ^ (2 : ℝ)) volume := by
    simpa [h2] using hf.integrable_norm_rpow (by norm_num) (by norm_num)
  calc ∫ x, ‖f x‖ ^ (2 : ℝ) ≤ ∫ x, S * |f x| := by
        refine integral_mono hint (hfi.abs.const_mul S) fun x => ?_
        simp only [Real.norm_eq_abs, Real.rpow_two]
        nlinarith [abs_nonneg (f x), hSf x, sq_abs (f x)]
    _ = S * ∫ x, |f x| := integral_const_mul _ _
    _ ≤ S * T := mul_le_mul_of_nonneg_left hT hS

lemma norm_quot_le (hφ : φ ∈ A₀ d) (a : ℝ) {C₂ : ℝ}
    (hC₂ : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ C₂) {R : ℝ} (hR0 : 0 ≤ R)
    (hR : ∀ y, R < ‖y‖ → φ y = 0 ∧ fderiv ℝ φ y = 0) {t : ℝ} (ht0 : t ≠ 0) (ht1 : |t| ≤ 1) :
    ‖t⁻¹ • (heatL2 φ (a + t) - heatL2 φ a) - a • heatL2 (Lf φ) a‖ ≤
      √((C₂ * ∫ z, ‖z‖ ^ 2 ∂(gam d)) * ∫ z, Wd C₂ R a z ∂(gam d)) * |t| := by
  set M2 : ℝ := ∫ z, ‖z‖ ^ 2 ∂(gam d) with hM2
  set T1 : ℝ := ∫ z, Wd C₂ R a z ∂(gam d) with hT1
  have hC0 : 0 ≤ C₂ := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ φ) 0)) (hC₂ 0)
  set q : (Fin d → ℝ) → ℝ := fun x => ∫ z, rhoD φ a t x z ∂(gam d) with hq
  have hqe : ∀ x, q x =
      t⁻¹ * (heatRd (a + t) φ x - heatRd a φ x) - a * heatRd a (Lf φ) x := by
    intro x
    simp only [hq]
    rw [integral_rhoD hφ a x, div_eq_inv_mul]
  have hqi : Integrable q volume := by
    have := (((integrable_heatRd hφ (a + t)).sub (integrable_heatRd hφ a)).const_mul t⁻¹).sub
      ((integrable_heatRd (Lf_mem hφ) a).const_mul a)
    exact this.congr (ae_of_all _ fun x => (hqe x).symm)
  have hqm : MemLp q 2 volume := by
    have := (((memLp_heatRd hφ (a + t)).sub (memLp_heatRd hφ a)).const_mul t⁻¹).sub
      ((memLp_heatRd (Lf_mem hφ) a).const_mul a)
    exact this.ae_eq (ae_of_all _ fun x => (hqe x).symm)
  have hEq : t⁻¹ • (heatL2 φ (a + t) - heatL2 φ a) - a • heatL2 (Lf φ) a = hqm.toLp q := by
    apply Lp.ext
    have h1 := coeFn_heatL2 hφ (a + t)
    have h2 := coeFn_heatL2 hφ a
    have h3 := coeFn_heatL2 (Lf_mem hφ) a
    filter_upwards [Lp.coeFn_sub (t⁻¹ • (heatL2 φ (a + t) - heatL2 φ a)) (a • heatL2 (Lf φ) a),
      Lp.coeFn_smul t⁻¹ (heatL2 φ (a + t) - heatL2 φ a),
      Lp.coeFn_sub (heatL2 φ (a + t)) (heatL2 φ a), Lp.coeFn_smul a (heatL2 (Lf φ) a),
      hqm.coeFn_toLp, h1, h2, h3] with x e1 e2 e3 e4 e5 e6 e7 e8
    rw [e1, Pi.sub_apply, e2, Pi.smul_apply, e3, Pi.sub_apply, e4, Pi.smul_apply, e5, e6, e7, e8,
      hqe x]
    simp [smul_eq_mul]
  rw [hEq]
  have hz2 := integrable_norm_pow_gam (d := d) 2
  have hS : ∀ x, |q x| ≤ (C₂ * M2) * |t| := by
    intro x
    have := norm_integral_le_of_norm_le (μ := gam d)
      (f := fun z => rhoD φ a t x z) (g := fun z => C₂ * |t| * ‖z‖ ^ 2) (hz2.const_mul _)
      (ae_of_all _ fun z => by simpa using rhoD_bound (smooth hφ) hC₂ a ht0 x z)
    rw [integral_const_mul, Real.norm_eq_abs] at this
    calc |q x| ≤ C₂ * |t| * M2 := this
      _ = _ := by ring
  have hS0 : 0 ≤ (C₂ * M2) * |t| :=
    mul_nonneg (mul_nonneg hC0 (integral_nonneg fun z => by positivity)) (abs_nonneg _)
  have hT : ∫ x, |q x| ≤ |t| * T1 := integral_abs_q_le hφ hC₂ a hR0 hR ht0 ht1
  refine (norm_toLp_le hqm hS0 hS hqi hT).trans (le_of_eq ?_)
  calc √((C₂ * M2 * |t|) * (|t| * T1)) = √((C₂ * M2 * T1) * |t| ^ 2) := by congr 1; ring
    _ = _ := by rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

end MarkovTriple.BGL.LebesgueRd
