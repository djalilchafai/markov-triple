import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Polar

/-!
# Gaussian radial weight and normalisation of `σ` (Round 29, stream R)

`∫_{ℝ^n} e^{-|y|²} ext f (y) dy = J_n ∫ f dσ0`, `J_n = Γ(n/2)/2 > 0`; `∫ f dσ = (σ0 univ).toReal⁻¹ ∫ f dσ0`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN.Atlas

variable {n : ℕ}

/-- the radial Gaussian integral `J_n = ∫_0^∞ r^{n-1} e^{-r²} dr` -/
noncomputable def Jn (n : ℕ) : ℝ := ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * Real.exp (-y ^ 2)

lemma Jn_pos (n : ℕ) : 0 < Jn n := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := ((n - 1 : ℕ) : ℝ)) (by norm_num)
    (by have : (0 : ℝ) ≤ ((n - 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  have e : Jn n = 1 / 2 * Real.Gamma ((((n - 1 : ℕ) : ℝ) + 1) / 2) := by
    rw [← h]
    unfold Jn
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    simp only [Real.rpow_natCast, Real.rpow_two]
  rw [e]
  exact mul_pos (by norm_num) (Real.Gamma_pos_of_pos (by positivity))

lemma polar_gauss (hn : 1 ≤ n) (h : Sph n → ℝ) :
    ∫ y : Fin n → ℝ, Real.exp (-(nrm y) ^ 2) * ext h y = (∫ z, h z ∂σ0 n) * Jn n :=
  polar hn (fun r => Real.exp (-r ^ 2)) h

lemma integral_σ (f : Sph n → ℝ) : ∫ z, f z ∂σ n = ((σ0 n Set.univ).toReal)⁻¹ * ∫ z, f z ∂σ0 n := by
  unfold σ
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]

end MarkovTriple.BGL.SphereN.Atlas
