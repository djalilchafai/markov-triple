import Mathlib
import MarkovTriple.Sanity.Trivial
import MarkovTriple.Hilbert.MarkovCriterion

/-!
# Non-vacuity of the bridge (NOT a frozen statement)

For the trivial triple of `Sanity/Trivial.lean` (`Γ = 0`, `L = 0`, finite discrete space), the
hypothesis `IsMarkovianForm` of the bridge theorem holds (via `isMarkovianForm_of_approx`, with the
exact approximant `g = |f| ∈ 𝒜₀ = ⊤`), so `isSemigroupOf_tripleSemigroup` applies and produces a
witness of `IsSemigroupOf`.  This shows that the hypotheses of the bridge are jointly satisfiable
and that the Friedrichs semigroup machinery does not collapse for degenerate reasons only in the
sense that the Markov criterion is checkable; it does *not* test `Γ ≠ 0`.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Finite E]

theorem trivialTriple_isMarkovianForm (μ : Measure E) [IsFiniteMeasure μ] :
    IsMarkovianForm (MarkovTriple.Sanity.trivialTriple μ) := by
  apply isMarkovianForm_of_approx
  intro f ε hε
  refine ⟨⟨fun x => |f.1 x|, Algebra.mem_top⟩, ?_, ?_⟩
  · have : toLp0 (MarkovTriple.Sanity.trivialTriple μ) ⟨fun x => |f.1 x|, Algebra.mem_top⟩ =
        |toLp0 (MarkovTriple.Sanity.trivialTriple μ) f| := by
      refine Lp.ext ?_
      filter_upwards [coeFn_toLp0 (MarkovTriple.Sanity.trivialTriple μ)
          ⟨fun x => |f.1 x|, Algebra.mem_top⟩, coeFn_toLp0 (MarkovTriple.Sanity.trivialTriple μ) f,
        Lp.coeFn_abs (toLp0 (MarkovTriple.Sanity.trivialTriple μ) f)] with x h1 h2 h3
      rw [h1, h3, h2]
    rw [this, sub_self, norm_zero]; exact hε
  · have hq : ∀ g : (MarkovTriple.Sanity.trivialTriple μ).A₀, qf (MarkovTriple.Sanity.trivialTriple μ) g g = 0 := by
      intro g; simp [qf, MarkovTriple.Sanity.trivialTriple]
    rw [hq, hq]; linarith

/-- The Friedrichs semigroup of the trivial triple is a witness of the frozen `IsSemigroupOf`. -/
theorem trivialTriple_friedrichs_isSemigroupOf (μ : Measure E) [IsFiniteMeasure μ] :
    (MarkovTriple.Sanity.trivialTriple μ).IsSemigroupOf
      (tripleSemigroup (MarkovTriple.Sanity.trivialTriple μ)) :=
  isSemigroupOf_tripleSemigroup _ (trivialTriple_isMarkovianForm μ)

end MarkovTriple.Hilbert
