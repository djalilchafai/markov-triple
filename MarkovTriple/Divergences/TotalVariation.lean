import Mathlib

/-!
# Genuine total variation and measurable pushforwards

The normalization is the paper's `sup_A |μ(A)-ν(A)|`, whose maximum value
for probability measures is one. This file proves its data-processing
inequality and a separating-halfspace lower bound from actual moments.
-/

namespace MarkovTriple

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- The paper's total variation distance, as a supremum over measurable sets. -/
noncomputable def totalVariationDistance (μ ν : Measure α) : ℝ :=
  sSup {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r = |μ.real A - ν.real A|}

private theorem tv_values_nonempty (μ ν : Measure α) :
    ({r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r = |μ.real A - ν.real A|}).Nonempty :=
  ⟨0, ∅, MeasurableSet.empty, by simp⟩

private theorem tv_value_le_one (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (A : Set α) :
    |μ.real A - ν.real A| ≤ 1 := by
  have hμ0 : 0 ≤ μ.real A := measureReal_nonneg
  have hν0 : 0 ≤ ν.real A := measureReal_nonneg
  have hμ1 : μ.real A ≤ 1 := measureReal_le_one
  have hν1 : ν.real A ≤ 1 := measureReal_le_one
  exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩

private theorem tv_values_bddAbove (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    BddAbove {r : ℝ | ∃ A : Set α, MeasurableSet A ∧ r = |μ.real A - ν.real A|} := by
  refine ⟨1, ?_⟩
  rintro r ⟨A, hA, rfl⟩
  exact tv_value_le_one μ ν A

/-- Every measurable separating set supplies a genuine TV lower bound. -/
theorem abs_measureReal_sub_le_totalVariationDistance (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : Set α} (hA : MeasurableSet A) :
    |μ.real A - ν.real A| ≤ totalVariationDistance μ ν :=
  le_csSup (tv_values_bddAbove μ ν) ⟨A, hA, rfl⟩

/-- Total variation is nonnegative in the paper's probability normalization. -/
theorem totalVariationDistance_nonneg (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : 0 ≤ totalVariationDistance μ ν := by
  simpa using abs_measureReal_sub_le_totalVariationDistance μ ν MeasurableSet.empty

/-- Total variation between probability measures is at most one. -/
theorem totalVariationDistance_le_one (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : totalVariationDistance μ ν ≤ 1 := by
  apply csSup_le (tv_values_nonempty μ ν)
  rintro r ⟨A, hA, rfl⟩
  exact tv_value_le_one μ ν A

@[simp] theorem totalVariationDistance_self (μ : Measure α) [IsProbabilityMeasure μ] :
    totalVariationDistance μ μ = 0 := by
  apply le_antisymm _ (totalVariationDistance_nonneg μ μ)
  apply csSup_le (tv_values_nonempty μ μ)
  rintro r ⟨A, hA, rfl⟩
  simp

/-- Genuine total variation decreases under a measurable map, as used in the
paper's entropy/TV cutoff lower bound. -/
theorem totalVariationDistance_map_le (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : α → β} (hT : Measurable T) :
    totalVariationDistance (μ.map T) (ν.map T) ≤ totalVariationDistance μ ν := by
  apply csSup_le (tv_values_nonempty _ _)
  rintro r ⟨A, hA, rfl⟩
  change |(μ.map T A).toReal - (ν.map T A).toReal| ≤ _
  rw [Measure.map_apply hT hA, Measure.map_apply hT hA]
  exact abs_measureReal_sub_le_totalVariationDistance μ ν (hT hA)

/-- An invertible measurable change of coordinates preserves total variation. -/
theorem totalVariationDistance_map_measurableEquiv (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (e : α ≃ᵐ β) :
    totalVariationDistance (μ.map e) (ν.map e) = totalVariationDistance μ ν := by
  apply le_antisymm (totalVariationDistance_map_le μ ν e.measurable)
  have : IsProbabilityMeasure (μ.map e) :=
    (Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (ν.map e) :=
    (Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).2 inferInstance
  have h := totalVariationDistance_map_le (μ.map e) (ν.map e) e.symm.measurable
  simpa only [e.map_symm_map] using h

/-- A separating halfspace yields a quantitative lower bound using only the
actual means and variances, by Chebyshev's inequality on each side. -/
theorem totalVariationDistance_ge_mean_separation (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : α → ℝ) (hX : Measurable X) (hXμ : MemLp X 2 μ) (hXν : MemLp X 2 ν)
    {m : ℝ} (hm : 0 < m) (hmeanμ : (∫ x, X x ∂μ) = m)
    (hmeanν : (∫ x, X x ∂ν) = 0) :
    1 - 4 * (variance X μ + variance X ν) / m ^ 2 ≤ totalVariationDistance μ ν := by
  let A : Set α := {x | m / 2 ≤ X x}
  have hA : MeasurableSet A := hX measurableSet_Ici
  have hμcheb := meas_ge_le_variance_div_sq hXμ (half_pos hm)
  have hνcheb := meas_ge_le_variance_div_sq hXν (half_pos hm)
  have hμA : μ Aᶜ ≤ ENNReal.ofReal (variance X μ / (m / 2) ^ 2) := by
    apply le_trans (measure_mono _) hμcheb
    intro x hx
    change m / 2 ≤ |X x - ∫ a, X a ∂μ|
    rw [hmeanμ]
    have hxlt : X x < m / 2 := by simpa [A] using hx
    linarith [neg_le_abs (X x - m)]
  have hνA : ν A ≤ ENNReal.ofReal (variance X ν / (m / 2) ^ 2) := by
    apply le_trans (measure_mono _) hνcheb
    intro x hx
    change m / 2 ≤ |X x - ∫ a, X a ∂ν|
    rw [hmeanν, sub_zero]
    exact le_trans hx (le_abs_self _)
  have hμAr : μ.real Aᶜ ≤ variance X μ / (m / 2) ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg X μ) (sq_nonneg _)) hμA
  have hνAr : ν.real A ≤ variance X ν / (m / 2) ^ 2 :=
    ENNReal.toReal_le_of_le_ofReal (div_nonneg (variance_nonneg X ν) (sq_nonneg _)) hνA
  have hcompl : μ.real Aᶜ = 1 - μ.real A := by
    rw [measureReal_compl hA]
    simp
  have hden : (m / 2) ^ 2 = m ^ 2 / 4 := by ring
  rw [hden] at hμAr hνAr
  have hdiv (a : ℝ) : a / (m ^ 2 / 4) = 4 * a / m ^ 2 := by ring
  rw [hdiv] at hμAr hνAr
  have hsep := abs_measureReal_sub_le_totalVariationDistance μ ν hA
  have habs := le_abs_self (μ.real A - ν.real A)
  rw [hcompl] at hμAr
  rw [mul_add, add_div]
  linarith

end MarkovTriple
