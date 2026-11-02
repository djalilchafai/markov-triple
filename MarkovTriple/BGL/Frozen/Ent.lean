import Mathlib

/-! # Entropy -/

open MeasureTheory

namespace MarkovTriple.BGL

/-- The entropy `Ent_μ(f) = ∫ f log f dμ − (∫ f dμ) log (∫ f dμ)` (BGL Ch. 5, (5.1.1)).
Intended for `f ≥ 0` and `μ` a probability measure; uses the Mathlib convention `Real.log 0 = 0`.
Junk value `0` if `f log f` is not integrable (Bochner convention).  Further junk (audit R2/L1):
`Real.log = log |·|`, so for `f` with negative values this is not an entropy, and `∫ f = 0` if
`f ∉ L¹`.  Guard: `IsEntAdmissible μ f` (`BGL/Guards.lean`: `f ≥ 0` a.e., `f` and `f log f`
integrable); all theorems about `Ent` for genuinely unbounded `f` must assume it. -/
noncomputable def Ent {E : Type*} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂μ) - (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)

end MarkovTriple.BGL
