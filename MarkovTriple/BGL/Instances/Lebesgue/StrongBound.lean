import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.GradBound
import MarkovTriple.BGL.Theory.Strong.Main

/-!
# Lebesgue: the strong gradient bound `√Γ(P_t f) ≤ P_t √Γ(f)` (BGL Thm 3.3.18, `ρ = 0`)

By the explicit heat kernel: `(P_t f)' = P_t f'`, and Jensen for the convex function `y ↦ √(y² + ε²) − ε`
gives the `ε`-form `ψ_ε(Γ(P_t f)) ≤ P_t ψ_ε(Γ f)`; the generic `FullTriple.strong_of_eps` passes to `ε → 0`.
(`StrongInterpolation` itself is not used here; the heat kernel replaces the interpolation argument.)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

/-- Jensen for `y ↦ √(y²+ε²)`: `ψ_ε((Eφ)²) ≤ E ψ_ε(φ²)`. -/
lemma heatM_psi_le {φ : ℝ → ℝ} (hφ : IsTest φ) {ε : ℝ} (hε : 0 < ε) (σ x : ℝ) :
    psiS ε (heatM σ φ x * heatM σ φ x) ≤ heatM σ (fun y => psiS ε (φ y * φ y)) x := by
  obtain ⟨C, hC0, hC⟩ := hφ.bdd
  set m := heatM σ φ x with hm
  set R := Real.sqrt (m * m + ε ^ 2) with hR
  have hpos : 0 < m * m + ε ^ 2 := by nlinarith [mul_self_nonneg m, sq_pos_of_pos hε]
  have hRpos : 0 < R := Real.sqrt_pos.2 hpos
  have hR2 : R ^ 2 = m * m + ε ^ 2 := Real.sq_sqrt hpos.le
  set a := m / R with ha
  set b := ε / R with hb
  have hab : a * a + b * b = 1 := by
    rw [ha, hb]; field_simp; nlinarith [hR2]
  have hmeas : Measurable fun z : ℝ => φ (x - σ * z) := hφ.cont.measurable.comp (by fun_prop)
  have hint1 : Integrable (fun z : ℝ => φ (x - σ * z)) (gaussianReal 0 1) :=
    integrable_comp_gauss hφ.cont hC σ x
  have hbd : ∀ z, |φ (x - σ * z)| ≤ C := fun z => hC _
  have hint2 : Integrable (fun z : ℝ => Real.sqrt (φ (x - σ * z) * φ (x - σ * z) + ε ^ 2))
      (gaussianReal 0 1) := by
    refine Integrable.of_bound (C := Real.sqrt (C * C + ε ^ 2)) ?_ ?_
    · exact (Real.continuous_sqrt.comp ((hφ.cont.comp (by fun_prop)).mul (hφ.cont.comp (by fun_prop))
        |>.add continuous_const)).aestronglyMeasurable
    · refine Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      apply Real.sqrt_le_sqrt
      have := abs_le.1 (hbd z)
      nlinarith
  have hle : ∫ z, (a * φ (x - σ * z) + b * ε) ∂(gaussianReal 0 1) ≤
      ∫ z, Real.sqrt (φ (x - σ * z) * φ (x - σ * z) + ε ^ 2) ∂(gaussianReal 0 1) := by
    refine integral_mono ((hint1.const_mul a).add (integrable_const _)) hint2 fun z => ?_
    have hcs : (a * φ (x - σ * z) + b * ε) ^ 2 ≤ φ (x - σ * z) * φ (x - σ * z) + ε ^ 2 := by
      nlinarith [sq_nonneg (a * ε - b * φ (x - σ * z)), hab]
    exact (le_abs_self _).trans (Real.abs_le_sqrt hcs)
  have hlhs : ∫ z, (a * φ (x - σ * z) + b * ε) ∂(gaussianReal 0 1) = a * m + b * ε := by
    rw [integral_add (hint1.const_mul a) (integrable_const _), integral_const_mul, integral_const]
    simp [hm, heatM]
  have hab2 : a * m + b * ε = R := by
    rw [ha, hb]; field_simp; nlinarith [hR2]
  have hrhs : heatM σ (fun y => psiS ε (φ y * φ y)) x =
      ∫ z, Real.sqrt (φ (x - σ * z) * φ (x - σ * z) + ε ^ 2) ∂(gaussianReal 0 1) - ε := by
    unfold heatM
    have : ∀ z, psiS ε (φ (x - σ * z) * φ (x - σ * z)) =
        Real.sqrt (φ (x - σ * z) * φ (x - σ * z) + ε ^ 2) - ε := fun z =>
      psiS_eq hε (by nlinarith [mul_self_nonneg (φ (x - σ * z)), sq_pos_of_pos hε])
    simp only [this]
    rw [integral_sub hint2 (integrable_const _)]
    simp
  rw [hrhs, psiS_eq hε (by nlinarith [mul_self_nonneg m, sq_pos_of_pos hε])]
  rw [hlhs, hab2] at hle
  linarith

/-- `ε`-form of the strong bound on `(ℝ, Lebesgue)`. -/
theorem lebesgue_strong_eps {ε : ℝ} (hε : 0 < ε) (f : lebesgueFull.A₀) (t : ℝ≥0) :
    (fun x => psiS ε (FullTriple.G lebesgueFull (lebesgueFull.Pt t f) (lebesgueFull.Pt t f) x)) ≤ᵐ[volume]
      fun x => Real.exp (-0 * t) * lebesgueFull.Pt t (FullTriple.psiGamma ε hε f) x := by
  set σ := Real.sqrt (2 * (t : ℝ)) with hσ
  have hf : f.1 ∈ A₀ := f.2
  have hIT : IsTest f.1 := isTest_of hf
  have hPt : lebesgueFull.Pt t f = heatM σ f.1 := by
    have h1 : lebesgueFull.Pt t f =ᵐ[volume] heatM σ f.1 :=
      (lebesgueFull.Pt_ae t f).symm.trans (semigroup_ae_heat hf t)
    exact (Continuous.ae_eq_iff_eq volume (mem_A.1 (lebesgueFull.Pt_mem_A t f)).continuous
      (hIT.heatM_contDiff σ).continuous).1 h1
  have hderiv : deriv (lebesgueFull.Pt t f) = heatM σ (deriv f.1) := by
    rw [hPt]; exact hIT.deriv_heatM σ
  have hΓ : FullTriple.G lebesgueFull (lebesgueFull.Pt t f) (lebesgueFull.Pt t f) =
      fun x => heatM σ (deriv f.1) x * heatM σ (deriv f.1) x := by
    have hs := mem_A.1 (lebesgueFull.Pt_mem_A t f)
    have := ΓA_eq_Gf hs hs
    funext x
    show lebesgueDiffusion.ΓA _ _ x = _
    rw [this]; simp [Gf, hderiv]
  set c := FullTriple.psiGamma ε hε f with hc
  have hcA : c.1 ∈ A₀ := c.2
  have h2 : (lebesgueFull.Pt t c) =ᵐ[volume] heatM σ c.1 :=
    (lebesgueFull.Pt_ae t c).symm.trans (semigroup_ae_heat hcA t)
  have hc1 : c.1 = fun y => psiS ε (deriv f.1 y * deriv f.1 y) := by
    funext y
    show psiS ε (FullTriple.G lebesgueFull f.1 f.1 y) = _
    have := ΓA_eq_Gf (smooth hf) (smooth hf)
    show psiS ε (lebesgueDiffusion.ΓA f.1 f.1 y) = _
    rw [this]; simp [Gf]
  filter_upwards [h2] with x hx
  rw [hx, hΓ, hc1]
  simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
  exact heatM_psi_le (isTest_of (deriv_mem hf)) hε σ x

/-- **Strong gradient bound on `(ℝ, Lebesgue)`** (BGL Thm 3.3.18 with `ρ = 0`, `CD(0,∞)`), unconditional:
`√Γ(P_t f) ≤ P_t(√Γ f)` a.e., `f ∈ C_c^∞`. -/
theorem lebesgue_strong_gradient_bound (f : lebesgueFull.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂volume, Real.sqrt (FullTriple.G lebesgueFull (lebesgueFull.Pt t f) (lebesgueFull.Pt t f) x) ≤
      Real.exp (-0 * t) *
        (lebesgueFull.toDiffusionTriple.semigroup t (lebesgueFull.sqrtΓcls f) :
          Lp ℝ 2 (volume : Measure ℝ)) x :=
  FullTriple.strong_of_eps (ρ := 0) f t fun n => lebesgue_strong_eps (by positivity) f t

end MarkovTriple.BGL.Lebesgue

#print axioms MarkovTriple.BGL.Lebesgue.lebesgue_strong_gradient_bound
