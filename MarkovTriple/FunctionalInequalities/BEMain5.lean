import Mathlib
import MarkovTriple.FunctionalInequalities.BEMain4
import MarkovTriple.FunctionalInequalities.BENem3

/-! # Bakry–Émery (Phase 4b): continuity of `e`, `q` on `[0,∞)` and the value `q(0)` -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

theorem continuous_eFun [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) {ε M : ℝ}
    (C : Cut ε M) : Continuous (eFun F hφ C) := by
  obtain ⟨K, hK⟩ := exists_bounds C.hΘ C.hΘc
  rw [continuous_iff_continuousAt]
  intro s
  exact continuousAt_int_comp C.hΘ (fun x => (hK x).1) (fun x => (hK x).2.1)
    ((continuous_aflow F hφ ε).continuousAt)

theorem continuous_qFun [IsFiniteMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) {ε M : ℝ}
    (C : Cut ε M) : Continuous (qFun F hφ C) := by
  obtain ⟨K, hK⟩ := exists_bounds C.hΘ C.hΘc
  rw [continuous_iff_continuousAt]
  intro s
  exact continuousAt_int_comp_mul (Λ := deriv C.Θ) (contDiff_deriv_top C.hΘ)
    (fun x => (hK x).2.1) (fun x => (hK x).2.2.1) ((continuous_aflow F hφ ε).continuousAt)
    ((continuous_orb F (F.L_mem φ hφ)).continuousAt)

theorem qFun_zero [IsProbabilityMeasure F.μ] {φ : E → ℝ} (hφ : φ ∈ F.A₀) (h0 : 0 ≤ᵐ[F.μ] φ)
    {M : ℝ} (hM : 0 < M) (hb : ∀ᵐ x ∂F.μ, |φ x| ≤ M) {ε : ℝ} (hε : 0 < ε) (C : Cut ε M) :
    qFun F hφ C 0 = -∫ x, F.Γ φ φ x / (ε + φ x) ∂F.μ := by
  set ψ : ℝ → ℝ := fun y => C.Λ (ε + y) - C.Λ ε with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    (C.hΛ.comp (contDiff_const.add contDiff_id)).sub contDiff_const
  have hψ0 : ψ 0 = 0 := by simp [hψdef]
  have hwA₀ : (fun x => ψ (φ x)) ∈ F.A₀ :=
    F.comp_mem 1 (BE.lift ψ) (contDiff_lift hψ) (by simp [BE.lift, hψ0])
      (fun _ => φ) (fun _ => hφ)
  have hφA : φ ∈ F.A := F.A₀_le φ hφ
  have hLφ := F.L_mem φ hφ
  have hibp := F.ibp_A φ hφA (memLp2 F.toMarkovTriple hφ) (memLp2 F.toMarkovTriple hLφ) _ hwA₀
  have hΓ : F.Γ φ (fun x => ψ (φ x)) = fun x => deriv ψ (φ x) * F.Γ φ φ x := by
    rw [F.Γ_symm_A φ hφA _ (F.A₀_le _ hwA₀)]
    exact Γ_comp F hψ hφA hφA
  have hderiv : ∀ y, deriv ψ y = deriv C.Λ (ε + y) := by
    intro y
    have h1 : HasDerivAt C.Λ (deriv C.Λ (ε + y)) (ε + y) :=
      ((C.hΛ.differentiable (by simp)) _).hasDerivAt
    exact ((h1.comp_const_add ε y).sub_const (C.Λ ε)).deriv
  have hrange : ∀ᵐ x ∂F.μ, ε + φ x ∈ Set.Icc ε (ε + M) := by
    filter_upwards [h0, hb] with x h1 h2
    exact ⟨by simp only [Pi.zero_apply] at h1; linarith, by linarith [(abs_le.1 h2).2]⟩
  have hL0 : ∫ x, F.L φ x ∂F.μ = 0 := F.integral_L hφ
  have iwL : Integrable (fun x => ψ (φ x) * F.L φ x) F.μ :=
    (memLp2 F.toMarkovTriple hwA₀).integrable_mul (memLp2 F.toMarkovTriple hLφ)
  have iL : Integrable (fun x => F.L φ x) F.μ := integrable_of_mem F.toMarkovTriple hLφ
  unfold qFun
  have e1 : ∀ᵐ x ∂F.μ, deriv C.Θ ((aflow F hφ ε 0 : Lp ℝ 2 F.μ) x) *
      (orb F (F.L_mem φ hφ) 0 : Lp ℝ 2 F.μ) x =
      ψ (φ x) * F.L φ x + (C.Λ ε + 1) * F.L φ x := by
    filter_upwards [aflow_coe hφ ε 0, coeFn_cl F hφ, coeFn_cl F hLφ, hrange] with x h1 h2 h3 h4
    rw [h1, orb_zero, h2]
    have h5 : (orb F hLφ 0 : E → ℝ) x = F.L φ x := by rw [orb_zero]; exact h3
    rw [h5, add_comm (φ x) ε, C.deriv_Θ_eq_Λ hε h4]
    simp only [hψdef]; ring
  have e2 : ∀ᵐ x ∂F.μ, deriv ψ (φ x) * F.Γ φ φ x = F.Γ φ φ x / (ε + φ x) := by
    filter_upwards [hrange] with x h4
    rw [hderiv, C.deriv_Λ_eq hε h4, inv_mul_eq_div, div_eq_mul_inv, mul_comm]
  rw [integral_congr_ae e1, integral_add iwL (iL.const_mul _), integral_const_mul, hL0,
    hibp.2, hΓ, integral_congr_ae e2]
  ring

end MarkovTriple.BE
