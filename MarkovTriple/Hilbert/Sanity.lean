import Mathlib
import MarkovTriple.Sanity.Trivial
import MarkovTriple.Sanity.Circle
import MarkovTriple.Sanity.Lebesgue
import MarkovTriple.Hilbert.FullBridge
import MarkovTriple.Hilbert.SubMarkov

/-!
# Non-vacuity of the bridge (NOT a frozen statement)

* `IsMarkovianForm` is now a theorem for every `MarkovTriple` (`isMarkovianForm`); here it is
  instantiated for the trivial triple (`Γ = 0`) and for the *circle* triple (`Γ ≠ 0`,
  `𝒜₀ = C^∞(𝕋)`), which gives evidence that the hypotheses of the derivation (stability of `𝒜₀`
  under `ψ_ε`) are satisfiable by a genuine diffusion.
* For the trivial *full* triple, `isSemigroupOf_full` produces a witness of `IsSemigroupOf`
  (the Friedrichs semigroup, here `P_t = id`) with no hypothesis; this now includes the
  sub-Markov clause `u ≤ 1 ⇒ P_t u ≤ 1` (`tripleSemigroup_subMarkov`, ERRATA N2).
* The sub-Markov property holds for the Friedrichs semigroup of the circle triple (`Γ ≠ 0`) and of
  the Lebesgue triple on `ℝ` (infinite measure), with no hypothesis (it is a theorem for every
  `MarkovTriple`).
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

/-- Sub-Markov property of the Friedrichs semigroup of the circle triple. -/
theorem circle_subMarkov (t : ℝ≥0)
    (u : Lp ℝ 2 MarkovTriple.Sanity.Circle.circleTriple.μ)
    (hu : (u : _ → ℝ) ≤ᵐ[MarkovTriple.Sanity.Circle.circleTriple.μ] 1) :
    (tripleSemigroup MarkovTriple.Sanity.Circle.circleTriple t u : _ → ℝ)
      ≤ᵐ[MarkovTriple.Sanity.Circle.circleTriple.μ] 1 :=
  tripleSemigroup_subMarkov _ t u hu

/-- Sub-Markov property of the Friedrichs semigroup of the Lebesgue triple (infinite measure). -/
theorem lebesgue_subMarkov (t : ℝ≥0)
    (u : Lp ℝ 2 MarkovTriple.Sanity.Lebesgue.lebesgueTriple.μ)
    (hu : (u : _ → ℝ) ≤ᵐ[MarkovTriple.Sanity.Lebesgue.lebesgueTriple.μ] 1) :
    (tripleSemigroup MarkovTriple.Sanity.Lebesgue.lebesgueTriple t u : _ → ℝ)
      ≤ᵐ[MarkovTriple.Sanity.Lebesgue.lebesgueTriple.μ] 1 :=
  tripleSemigroup_subMarkov _ t u hu

end MarkovTriple.Hilbert
