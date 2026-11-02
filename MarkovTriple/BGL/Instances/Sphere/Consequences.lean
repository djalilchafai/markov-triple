import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Curvature
import MarkovTriple.BGL.Theory.Compact.Consequences
import MarkovTriple.BGL.Theory.Poincare

/-!
# Unconditional Lichnerowicz, log-Sobolev, gradient bound, Fisher decay on the zonal sphere `S³`

The first genuinely compact `CompactTriple` with `Γ ≠ 0` and a finite-dimensional curvature-dimension
condition `CD(2,3)` (`ρ > 0`, `n < ∞`), non-Gaussian:

* `sphere_PI`: `Var f ≤ (1/3) ∫ Γ(f)` (`poincare_of_CD_dim`, Lichnerowicz; sharp: `λ₁ = 3`);
* `sphere_LS`: `LS(1/2, 0)` (`compact_logSobolev`, `ρ = 2`);
* `sphere_gradient_bound`: `Γ(P_t f) ≤ e^{-4t} P_t Γ(f)`;
* `sphere_fisher_decay`: `I(s) ≤ e^{-4s} I(0)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL.Instances.Sphere

/-- the underlying space is genuinely compact. -/
theorem sphere_space_compact : CompactSpace Zon := inferInstance

instance : IsProbabilityMeasure sCompact.toFullTriple.μ := (inferInstance : IsProbabilityMeasure μZ)

/-- **Lichnerowicz on the sphere**: `PI((1 - 1/3)/2) = PI(1/3)`, from `CD(2,3)` (unconditional). -/
theorem sphere_PI : sCompact.toDiffusionTriple.PI ((1 - (((3 : ℝ≥0∞))⁻¹).toReal) / 2) :=
  FullTriple.poincare_of_CD_dim sCompact.toFullTriple (by norm_num) (by norm_num) sphere_CD_two_three

theorem sphere_PI' : sCompact.toDiffusionTriple.PI (1 / 3) := by
  have h := sphere_PI
  have e : (1 - (((3 : ℝ≥0∞))⁻¹).toReal) / 2 = 1 / 3 := by
    rw [ENNReal.toReal_inv]; simp; norm_num
  rwa [e] at h

/-- **Logarithmic Sobolev inequality** `LS(1/2, 0)` on the sphere (unconditional). -/
theorem sphere_LS : sCompact.toDiffusionTriple.LS (1 / 2) 0 :=
  compact_logSobolev sCompact (by norm_num) sphere_CD_two_three

/-- **Gradient bound** `Γ(P_t f) ≤ e^{-4t} P_t Γ(f)` (weak form). -/
theorem sphere_gradient_bound (f : sCompact.A₀) (t : ℝ≥0) :
    sCompact.toDiffusionTriple.ΓA (sCompact.Pt t f) (sCompact.Pt t f) ≤ᵐ[sCompact.μ]
      fun x => Real.exp (-2 * 2 * t) * (sCompact.toDiffusionTriple.semigroup t
        (sCompact.toDiffusionTriple.cls ⟨sCompact.toDiffusionTriple.ΓA f.1 f.1,
          sCompact.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 sCompact.μ) x :=
  compact_gradient_bound sCompact sphere_CD_two_three f t

/-- **Decay of the Fisher information** along the heat flow: `I(s) ≤ e^{-4s} I(0)`. -/
theorem sphere_fisher_decay (φ : sCompact.A₀) (h0 : 0 ≤ᵐ[sCompact.μ] φ.1) {ε : ℝ}
    (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) :
    sCompact.toFullTriple.entI φ ε s ≤
      Real.exp (-2 * 2 * s) * sCompact.toFullTriple.entI φ ε 0 :=
  sCompact.fisher_decay sphere_CD_two_three φ h0 hε hs

end MarkovTriple.BGL.Instances.Sphere

#print axioms MarkovTriple.BGL.Instances.Sphere.sCompact
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_space_compact
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_CD
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_Γ_ne_zero
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_PI'
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_LS
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_gradient_bound
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_fisher_decay
