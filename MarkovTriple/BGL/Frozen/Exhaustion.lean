import Mathlib

/-!
# Exhaustion sequence (BGL Definition 3.1.1, last sentence)
-/

open MeasureTheory Filter
open scoped Topology

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- `u` is an **exhaustion sequence** for the algebra `A₀` and the measure `μ` (BGL Def. 3.1.1:
"an increasing sequence of functions in `𝒜₀` converging `μ`-almost everywhere to the constant
function `1`"; this gives a meaning to "`1`" when `μ` is infinite, cf. Def. 3.1.12).

Choice: "increasing" and "converging" are read `μ`-almost everywhere (the book's convention that
equalities and inequalities between functions hold a.e.); the stronger pointwise reading is
satisfied by all natural instances. -/
def IsExhaustion (μ : Measure E) (A₀ : NonUnitalSubalgebra ℝ (E → ℝ)) (u : ℕ → E → ℝ) : Prop :=
  (∀ n, u n ∈ A₀) ∧ (∀ n, u n ≤ᵐ[μ] u (n + 1)) ∧ ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (𝓝 1)

end MarkovTriple.BGL
