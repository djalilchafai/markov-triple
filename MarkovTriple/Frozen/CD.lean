import Mathlib
import MarkovTriple.Frozen.Gamma2

/-! # Curvature-dimension condition `CD(ρ,n)` -/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- The curvature-dimension condition `CD(ρ,n)` (BGL Definition 1.16.1; exact numbering to be verified by the author):
`Γ₂(f) ≥ ρ Γ(f) + (1/n) (Lf)²` μ-a.e., for all `f ∈ 𝒜₀`, with `ρ : ℝ`, `n : ℝ≥0∞`.

* `n = ∞` : the term `(1/n)(Lf)²` is `0` (`(∞)⁻¹ = 0` in `ℝ≥0∞`), i.e. `CD(ρ,∞)`: `Γ₂ ≥ ρΓ`.
* `0 < n < ∞` : the term is `(Lf)²/n.toReal`.
* `n = 0` : excluded by the conjunct `0 < n` (so `CD ρ 0` is false; no division by zero accident).

The coefficient is written as `(n⁻¹).toReal` where `n⁻¹ : ℝ≥0∞`. -/
def CD (T : MarkovTriple E) (ρ : ℝ) (n : ℝ≥0∞) : Prop :=
  0 < n ∧ ∀ f ∈ T.A₀, ∀ᵐ x ∂T.μ,
    ρ * T.Γ f f x + (n⁻¹).toReal * (T.L f x) ^ 2 ≤ T.Γ₂ f x

end MarkovTriple
