import Mathlib
import MarkovTriple.Sanity.Trivial
import MarkovTriple.Sanity.Circle
import MarkovTriple.Hilbert.FullBridge

/-!
# Non-vacuity of the bridge (NOT a frozen statement)

* `IsMarkovianForm` is now a theorem for every `MarkovTriple` (`isMarkovianForm`); here it is
  instantiated for the trivial triple (`Γ = 0`) and for the *circle* triple (`Γ ≠ 0`,
  `𝒜₀ = C^∞(𝕋)`), which gives evidence that the hypotheses of the derivation (stability of `𝒜₀`
  under `ψ_ε`) are satisfiable by a genuine diffusion.
* For the trivial *full* triple, `isSemigroupOf_full` produces a witness of `IsSemigroupOf`
  (the Friedrichs semigroup, here `P_t = id`) with no hypothesis.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Finite E]

theorem trivialTriple_isMarkovianForm (μ : Measure E) [IsFiniteMeasure μ] :
    IsMarkovianForm (MarkovTriple.Sanity.trivialTriple μ) :=
  isMarkovianForm _

/-- The Friedrichs semigroup of the trivial full triple is a witness of the frozen `IsSemigroupOf`. -/
theorem trivialFull_friedrichs_isSemigroupOf (μ : Measure E) [IsFiniteMeasure μ] :
    (MarkovTriple.Sanity.trivialFull μ).toMarkovTriple.IsSemigroupOf
      (tripleSemigroup (MarkovTriple.Sanity.trivialFull μ).toMarkovTriple) :=
  isSemigroupOf_full _

/-- The Markov property of the form holds for the circle triple (`Γ ≠ 0`). -/
theorem circle_isMarkovianForm : IsMarkovianForm MarkovTriple.Sanity.Circle.circleTriple :=
  isMarkovianForm _

end MarkovTriple.Hilbert
