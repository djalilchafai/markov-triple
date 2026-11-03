import MarkovTriple.BGL.Instances.GibbsRd.EllRegProof
import MarkovTriple.BGL.Instances.GibbsRd.SobSharpMain

/-!
# Elliptic regularity with the sharp Sobolev index (R17 SobSharp)

The resolvent chain of `EllRegProof.lean` gives `H^{j}_loc` for `x₀` as soon as the chain has length `j`;
the sharp embedding `sob_contDiff_rep_sharp'` needs only `j = m + ⌊d/2⌋ + 1` (instead of `m + d`) for a `C^m`
representative.  `EllData.EllReg` and `ellReg` are unchanged; the new statements are added next to them.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- **Elliptic regularity with chain length `m + ⌊d/2⌋ + 1`**: every `L²(μ)` weak-solution chain of that length has
a `C^m` representative. -/
theorem ellReg_sharp_order (m : ℕ) (x : ℕ → (Rd d → ℝ))
    (hx : ∀ k ≤ m + d / 2 + 1, MemLp (x k) 2 E.μ)
    (hW : ∀ k < m + d / 2 + 1, ∀ a ∈ A₀ d,
      ∫ y, x k y * E.L a y ∂E.μ = ∫ y, (x k y - x (k + 1) y) * a y ∂E.μ) :
    ∃ g : Rd d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ x 0 =ᵐ[E.μ] g := by
  have hS := E.chain_sobolev hx hW (m + d / 2 + 1) 0 (by omega)
  obtain ⟨g, hg, hae⟩ := Sob.sob_contDiff_rep_sharp' m ((sobolev_iff_hasSobL2 _).1 hS)
  exact ⟨g, hg, (Measure.AbsolutelyContinuous.ae_eq (withDensity_absolutelyContinuous _ _) hae)⟩

/-- `EllReg` with the explicit sharp chain length `n = m + ⌊d/2⌋ + 1`. -/
theorem ellReg_sharp : ∀ m : ℕ, ∃ n : ℕ, n = m + d / 2 + 1 ∧ ∀ x : ℕ → (Rd d → ℝ),
    (∀ k ≤ n, MemLp (x k) 2 E.μ) →
    (∀ k < n, ∀ a ∈ A₀ d, ∫ y, x k y * E.L a y ∂E.μ = ∫ y, (x k y - x (k + 1) y) * a y ∂E.μ) →
    ∃ g : Rd d → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ x 0 =ᵐ[E.μ] g :=
  fun m => ⟨m + d / 2 + 1, rfl, fun x hx hW => E.ellReg_sharp_order m x hx hW⟩

/-- the existing statement `EllReg`, re-derived from the sharp embedding. -/
theorem ellReg_of_sharp : E.EllReg := fun m =>
  ⟨m + d / 2 + 1, fun x hx hW => E.ellReg_sharp_order m x hx hW⟩

end EllData
end MarkovTriple.BGL.Instances.GibbsRd
