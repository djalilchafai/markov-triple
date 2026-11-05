import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Atlas.Norm
import MarkovTriple.BGL.Instances.SphereN.Atlas.CircleOps

/-!
# The circle measure: `∫_𝕋 f∘κ dμ₀ = ∫ f dσ` on `Sph 2` (Round 29, stream R, R3)

Mathlib's polar coordinates of `ℝ²` (`integral_comp_polarCoord_symm`) against the cone polar decomposition of `σ0` (`polar_gauss`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal Real

namespace MarkovTriple.BGL.SphereN.Atlas

open MarkovTriple.Sanity.Circle

lemma ext_two (f : Sph 2 → ℝ) (y : Fin 2 → ℝ) : ext f y = ext f ![y 0, y 1] := by
  congr 1
  funext i; fin_cases i <;> rfl

lemma nrm_sq_two (y : Fin 2 → ℝ) : nrm y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  rw [nrm_sq]; simp [LebesgueRd.sq, Fin.sum_univ_two]

lemma circle_step_A (f : Sph 2 → ℝ) :
    ∫ y : Fin 2 → ℝ, Real.exp (-(nrm y) ^ 2) * ext f y =
      ∫ p : ℝ × ℝ, Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) * ext f ![p.1, p.2] := by
  have h := (volume_preserving_finTwoArrow ℝ).integral_comp'
    (g := fun p : ℝ × ℝ => Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) * ext f ![p.1, p.2])
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [MeasurableEquiv.finTwoArrow_apply]
  rw [nrm_sq_two, ← ext_two]

lemma circle_step_B (f : Sph 2 → ℝ) :
    ∫ p : ℝ × ℝ, Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) * ext f ![p.1, p.2] =
      Jn 2 * ∫ θ in Ioo (-π) π, ext f ![Real.cos θ, Real.sin θ] := by
  rw [← integral_comp_polarCoord_symm]
  have hmeas : MeasurableSet polarCoord.target := by
    rw [polarCoord_target]; exact measurableSet_Ioi.prod measurableSet_Ioo
  have e : ∫ p in polarCoord.target, p.1 • (Real.exp (-((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2)) *
        ext f ![(polarCoord.symm p).1, (polarCoord.symm p).2]) =
      ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π,
        (p.1 * Real.exp (-p.1 ^ 2)) * ext f ![Real.cos p.2, Real.sin p.2] := by
    rw [polarCoord_target]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p hp => ?_
    obtain ⟨hr, -⟩ := hp
    have hr' : 0 < p.1 := hr
    simp only [polarCoord_symm_apply, smul_eq_mul]
    have h1 : (p.1 * Real.cos p.2) ^ 2 + (p.1 * Real.sin p.2) ^ 2 = p.1 ^ 2 := by
      have := Real.cos_sq_add_sin_sq p.2
      nlinarith [this]
    have h2 : (![p.1 * Real.cos p.2, p.1 * Real.sin p.2] : Fin 2 → ℝ) = p.1 • ![Real.cos p.2, Real.sin p.2] := by
      funext i; fin_cases i <;> simp
    rw [h1, h2, ext_smul f hr']
    ring
  rw [e]
  have := setIntegral_prod_mul (μ := volume) (ν := volume) (fun r : ℝ => r * Real.exp (-r ^ 2))
    (fun θ : ℝ => ext f ![Real.cos θ, Real.sin θ]) (Ioi (0 : ℝ)) (Ioo (-π) π)
  rw [Measure.volume_eq_prod, this]
  unfold Jn
  simp

lemma circle_step_C (f : Sph 2 → ℝ) :
    ∫ θ in Ioo (-π) π, ext f ![Real.cos θ, Real.sin θ] = 2 * π * ∫ x : 𝕋, f (κ x) ∂μ₀ := by
  have hπ : 0 < π := Real.pi_pos
  have h1 : ∫ θ in Ioo (-π) π, ext f ![Real.cos θ, Real.sin θ] =
      ∫ θ in (-π)..π, ext f ![Real.cos θ, Real.sin θ] := by
    rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have h2 := intervalIntegral.integral_comp_mul_left (a := (-1 / 2 : ℝ)) (b := 1 / 2)
    (fun θ : ℝ => ext f ![Real.cos θ, Real.sin θ]) (c := 2 * π) (by positivity)
  have e1 : (2 * π) * (-1 / 2 : ℝ) = -π := by ring
  have e2 : (2 * π) * (1 / 2 : ℝ) = π := by ring
  rw [e1, e2] at h2
  have h3 : ∫ θ in (-π)..π, ext f ![Real.cos θ, Real.sin θ] =
      (2 * π) * ∫ x in (-1 / 2 : ℝ)..1 / 2, ext f ![Real.cos (2 * π * x), Real.sin (2 * π * x)] := by
    rw [h2, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  have h4 : ∀ x : ℝ, ext f ![Real.cos (2 * π * x), Real.sin (2 * π * x)] = f (κ (x : 𝕋)) := fun x => by
    have := congrFun (lift_κ f) x
    exact this.symm
  simp only [h4] at h3
  have h5 := AddCircle.intervalIntegral_preimage (T := (1 : ℝ)) (-1 / 2) (fun x : 𝕋 => f (κ x))
  have h6 : (-1 / 2 : ℝ) + 1 = 1 / 2 := by norm_num
  rw [h6] at h5
  have h7 : ∫ x : 𝕋, f (κ x) ∂μ₀ = ∫ x : 𝕋, f (κ x) := by
    rw [AddCircle.integral_haarAddCircle]; simp
  rw [h1, h3, h7, ← h5]

theorem circle_polar {f : Sph 2 → ℝ} :
    (∫ z, f z ∂σ0 2) = 2 * π * ∫ x : 𝕋, f (κ x) ∂μ₀ := by
  have h := polar_gauss (n := 2) (by norm_num) f
  rw [circle_step_A, circle_step_B, circle_step_C] at h
  have hJ := Jn_pos 2
  have : (∫ z, f z ∂σ0 2) * Jn 2 = (2 * π * ∫ x : 𝕋, f (κ x) ∂μ₀) * Jn 2 := by
    rw [← h]; ring
  exact mul_right_cancel₀ hJ.ne' this

theorem circle_integral {f : Sph 2 → ℝ} (_hf : f ∈ A₀S 2) :
    ∫ x : 𝕋, f (κ x) ∂μ₀ = ∫ z, f z ∂σ 2 := by
  have h1 := circle_polar (f := fun _ : Sph 2 => (1 : ℝ))
  have hmass : (σ0 2 Set.univ).toReal = 2 * π := by
    have : (∫ z : Sph 2, (1 : ℝ) ∂σ0 2) = (σ0 2 Set.univ).toReal := by
      simp [Measure.real]
    rw [← this, h1]
    simp
  rw [integral_σ, hmass, circle_polar (f := f)]
  have : (2 * π) ≠ 0 := by positivity
  field_simp

end MarkovTriple.BGL.SphereN.Atlas
