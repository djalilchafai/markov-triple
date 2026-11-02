import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Full
import MarkovTriple.BGL.Theory.Conservation.Estimate
import MarkovTriple.BGL.Theory.Complete.Instances

/-!
# Lebesgue: the weak gradient bound `Γ(P_t f) ≤ P_t Γ(f)` (CD(0,∞)), by the explicit heat kernel

`P_t f = E f(· − √(2t) Z)`, `(P_t f)' = P_t f'`, and `(E φ)² ≤ E φ²` (Jensen).  This gives
`HasGradientBound lebesgueDiffusion A 0` unconditionally and hence a *non-compact application of the
mass-conservation theorem (BGL Thm 3.3.23)* on an infinite-measure space (`lebesgue_conservative_of_complete`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

open MarkovTriple.BGL

/-- Jensen for the Gaussian smoothing of a test function. -/
lemma heatM_sq_le {φ : ℝ → ℝ} (hφ : IsTest φ) (σ x : ℝ) :
    heatM σ φ x * heatM σ φ x ≤ heatM σ (fun y => φ y * φ y) x := by
  obtain ⟨C, hC0, hC⟩ := hφ.bdd
  set Z : ℝ → ℝ := fun z => φ (x - σ * z) with hZ
  have hZm : Measurable Z := hφ.cont.measurable.comp (by fun_prop)
  have hZb : MemLp Z 2 (gaussianReal 0 1) :=
    MemLp.of_bound hZm.aestronglyMeasurable C (Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs, hZ] using hC _)
  have hv := variance_nonneg Z (gaussianReal 0 1)
  rw [variance_eq_sub hZb] at hv
  have e1 : heatM σ φ x = (gaussianReal 0 1)[Z] := rfl
  have e2 : heatM σ (fun y => φ y * φ y) x = (gaussianReal 0 1)[Z ^ 2] := by
    simp only [heatM, Pi.pow_apply, hZ]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  rw [e1, e2]; nlinarith [hv]

theorem lebesgue_hasGradientBound : HasGradientBound lebesgueDiffusion A 0 := by
  intro f c hc t g hg hgt
  set σ := Real.sqrt (2 * (t : ℝ)) with hσ
  have hIT : IsTest f.1 := isTest_of f.2
  have h1 : g =ᵐ[volume] heatM σ f.1 := hgt.symm.trans (semigroup_ae_heat f.2 t)
  have hgc : Continuous g := (mem_A.1 hg).continuous
  have hhc : Continuous (heatM σ f.1) := (hIT.heatM_contDiff σ).continuous
  have hge : g = heatM σ f.1 := (Continuous.ae_eq_iff_eq volume hgc hhc).1 h1
  have hderiv : deriv g = heatM σ (deriv f.1) := by rw [hge]; exact hIT.deriv_heatM σ
  have hΓ : lebesgueDiffusion.ΓA g g = fun x => heatM σ (deriv f.1) x * heatM σ (deriv f.1) x := by
    rw [ΓA_eq_Gf hg hg]; funext x; simp [Gf, hderiv]
  -- `c = f'^2` everywhere
  have hc' : c.1 = fun x => deriv f.1 x * deriv f.1 x := by
    have : c.1 =ᵐ[volume] fun x => deriv f.1 x * deriv f.1 x :=
      hc.trans (Filter.Eventually.of_forall fun x => rfl)
    exact (Continuous.ae_eq_iff_eq volume (smooth c.2).continuous
      (((smooth (deriv_mem f.2)).continuous).mul ((smooth (deriv_mem f.2)).continuous))).1 this
  have h2 : (lebesgueDiffusion.semigroup t (lebesgueDiffusion.cls c) : ℝ → ℝ) =ᵐ[volume]
      heatM σ c.1 := by
    have := semigroup_ae_heat c.2 t
    simpa [hσ] using this
  filter_upwards [h2] with x hx
  rw [hx, hΓ, hc']
  simp only [neg_mul, mul_zero, zero_mul, neg_zero, Real.exp_zero, one_mul]
  exact heatM_sq_le (isTest_of (deriv_mem f.2)) σ x

end MarkovTriple.BGL.Lebesgue

namespace MarkovTriple.BGL

/-- **Thm 3.3.23 (first claim) on `(ℝ, Lebesgue)`**: a non-compact, infinite-measure application.
Completeness (real cutoffs) and the weak gradient bound (heat kernel) give `P_t u_n → 1` a.e. for every
exhaustion sequence, *without using the field `conservative`*. -/
theorem lebesgue_conservative_of_complete {u : ℕ → ℝ → ℝ}
    (hu : IsExhaustion Lebesgue.lebesgueDiffusion.μ Lebesgue.lebesgueDiffusion.A₀ u) (t : ℝ≥0) :
    ∀ᵐ x ∂Lebesgue.lebesgueDiffusion.μ, Tendsto (fun m =>
      (Lebesgue.lebesgueDiffusion.exhP hu t m : ℝ → ℝ) x) atTop (𝓝 1) :=
  Lebesgue.lebesgueFull.extendedAlgebra.conservative_of_complete Lebesgue.lebesgue_hasGradientBound
    lebesgueDiffusion_isComplete hu t

end MarkovTriple.BGL

#print axioms MarkovTriple.BGL.Lebesgue.lebesgue_hasGradientBound
#print axioms MarkovTriple.BGL.lebesgue_conservative_of_complete
