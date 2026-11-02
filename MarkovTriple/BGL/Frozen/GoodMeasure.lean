import Mathlib

/-!
# "Good" measure space (BGL Def. 3.1.1, hypothesis D1; Sect. 1.14)
-/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- **Good measure** (BGL Sect. 1.14, D1 of Def. 3.1.1): the σ-algebra is countably generated *up to
`μ`-null sets*: there is a countable family `𝒢` of measurable sets such that every measurable set
differs by a `μ`-null set from a set of `σ(𝒢)`.  For σ-finite `μ` this is the checkable half of the
book's "good measurable space" (it makes every `Lᵖ(μ)`, `1 ≤ p < ∞`, separable).  The other half of
the book's requirement (the measure decomposition / bi-measure theorems of Sect. 1.14) is NOT
encoded: it is naturally obtained from a standard Borel model and cannot be stated abstractly. -/
def IsGoodMeasure (μ : Measure E) : Prop :=
  ∃ 𝒢 : Set (Set E), 𝒢.Countable ∧ (∀ s ∈ 𝒢, MeasurableSet s) ∧
    ∀ s, MeasurableSet s → ∃ t, MeasurableSet[MeasurableSpace.generateFrom 𝒢] t ∧
      μ (symmDiff s t) = 0

/-- A countably generated σ-algebra (e.g. the Borel σ-algebra of a second countable space) carries only
good measures.  This is the lemma that discharges the field `DiffusionTriple.good` in all concrete
instances (see the default tactic of that field). -/
theorem IsGoodMeasure.of_countablyGenerated [h : MeasurableSpace.CountablyGenerated E]
    (μ : Measure E) : IsGoodMeasure μ := by
  obtain ⟨b, hb, hgen⟩ := h.isCountablyGenerated
  refine ⟨b, hb, fun s hs => ?_, fun s hs => ⟨s, ?_, by simp⟩⟩
  · rw [hgen]; exact MeasurableSpace.measurableSet_generateFrom hs
  · rw [← hgen]; exact hs

end MarkovTriple.BGL
