import Mathlib
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Frozen.Gamma2

/-! # Curvature-dimension condition `CD(ρ,n)` (BGL Definition 3.3.14) -/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- The curvature-dimension condition `CD(ρ, n)`, `ρ ∈ ℝ`, `n ∈ [1, ∞]` (BGL Def. 3.3.14): for every
`f ∈ 𝒜`, `Γ₂(f) ≥ ρ Γ(f) + (1/n) (L f)²` (a.e.).  `n : ℝ≥0∞`; `n = ∞` means no `(Lf)²/n` term
(`∞⁻¹ = 0`); `n < 1` is excluded by the conjunct `1 ≤ n`, as in the book. -/
def FullTriple.CD (T : FullTriple E) (ρ : ℝ) (n : ℝ≥0∞) : Prop :=
  1 ≤ n ∧ ∀ f ∈ T.A, ∀ᵐ x ∂T.μ,
    ρ * T.toDiffusionTriple.ΓA f f x + (n⁻¹).toReal * (T.L f x) ^ 2 ≤
      T.toDiffusionTriple.Γ₂ f f x

end MarkovTriple.BGL
