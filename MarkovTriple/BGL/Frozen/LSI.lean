import Mathlib
import MarkovTriple.BGL.Frozen.Energy
import MarkovTriple.BGL.Frozen.Ent

/-! # Logarithmic Sobolev inequality (BGL Definition 5.1.1) -/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- Logarithmic Sobolev inequality `LS(C, D)` (BGL Def. 5.1.1), generic in `(μ, Γ)`: `μ` is a
probability measure, `C > 0`, `D ≥ 0`, and `Ent_μ(f²) ≤ 2 C ℰ(f) + D ∫ f² dμ` for all `f` in the class
`𝒞` (the book: all `f ∈ 𝒟(ℰ)`, enough on a dense family).  The tight inequality `LS(C)` is
`D = 0`; for the standard Gaussian it holds with `C = 1`. -/
def LogSobolevIneq (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (𝒞 : Set (E → ℝ))
    (C D : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ 0 < C ∧ 0 ≤ D ∧
    ∀ f ∈ 𝒞, Ent μ (fun x => f x ^ 2) ≤ 2 * C * energy μ Γ f + D * ∫ x, f x ^ 2 ∂μ

end MarkovTriple.BGL
