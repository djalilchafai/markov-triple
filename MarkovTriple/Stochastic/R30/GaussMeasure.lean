import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.GaussFinite
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAux

/-!
# Round 30 (S), part 1: the reference measure of `gaussRdFull d` is the product Gaussian `gam d`

`(gaussData d).toEll.μ = volume.withDensity (ofReal (e^{-|x|²/2} / Z))` with `Z = ∫ e^{-|x|²/2}`; `gam d` has density
`∏ᵢ φ(xᵢ) = (2π)^{-d/2} e^{-|x|²/2}`.  Both are probability measures with proportional densities, so they coincide.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R30

open MarkovTriple.BGL MarkovTriple.BGL.LebesgueRd MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

lemma gdens_eq (x : Fin d → ℝ) :
    gdens x = ((√(2 * Real.pi))⁻¹) ^ d * Real.exp (-(qd x / 2)) := by
  unfold gdens qd
  simp_rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, Finset.sum_div]
  congr 2
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma integral_gdens_eq_one : ∫ x, gdens (d := d) x = 1 := by
  have h := gam_eq_withDensity (d := d)
  have h1 : (gam d) Set.univ = 1 := measure_univ
  rw [h, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal integrable_gdens (ae_of_all _ gdens_nonneg)] at h1
  have := ENNReal.ofReal_eq_one.1 h1
  exact this

theorem gaussData_dens_eq (x : Fin d → ℝ) : (gaussData d).toEll.dens x = gdens x := by
  have hw : ∀ y : Fin d → ℝ, (gaussData d).toEll.w y = Real.exp (-(qd y / 2)) := fun y => rfl
  have hk : 0 < ((√(2 * Real.pi))⁻¹) ^ d := by positivity
  have hZ : (gaussData d).toEll.Z = (((√(2 * Real.pi))⁻¹) ^ d)⁻¹ := by
    have h1 := integral_gdens_eq_one (d := d)
    simp_rw [gdens_eq] at h1
    rw [integral_const_mul] at h1
    have : (gaussData d).toEll.Z = ∫ y : Fin d → ℝ, Real.exp (-(qd y / 2)) := rfl
    rw [this]
    exact (eq_inv_of_mul_eq_one_right h1)
  unfold EllData.dens
  rw [hZ, gdens_eq, hw]
  field_simp

theorem gaussData_μ_eq_gam (d : ℕ) : (gaussData d).toEll.μ = gam d := by
  rw [gam_eq_withDensity]
  unfold EllData.μ
  congr 1
  funext x
  rw [gaussData_dens_eq]

/-- **S1**: the reference measure of the Gaussian full triple on `ℝ^d` is the product Gaussian. -/
theorem gaussRdFull_mu (d : ℕ) : (gaussRdFull d).toDiffusionTriple.μ = gam d :=
  gaussData_μ_eq_gam d

end MarkovTriple.Stochastic.R30
