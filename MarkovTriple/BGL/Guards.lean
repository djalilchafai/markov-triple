import Mathlib
import MarkovTriple.BGL.Frozen.Ent
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-!
# Guards and typeclass ergonomics for the BGL surface (not frozen; audit R2, L1 and L2)

* `IsEntAdmissible`: the guard under which `Ent` is a genuine entropy (BGL (5.1.1)).
* instances `SigmaFinite T.μ` for every diffusion triple; `IsProbabilityMeasure T.μ` can NOT be an
  instance (it would loop through `IsFiniteMeasure`), hence the theorem `isProb_of_finite`.
-/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- Guard for `Ent μ f` (audit R2/L1): `f ≥ 0` a.e., `f` and `f log f` integrable, so that `Ent` is
a genuine entropy and not a Bochner junk value. -/
def IsEntAdmissible (μ : Measure E) (f : E → ℝ) : Prop :=
  (0 ≤ᵐ[μ] f) ∧ Integrable f μ ∧ Integrable (fun x => f x * Real.log (f x)) μ

/-- (L2) `σ`-finiteness of the reference measure as an instance. -/
instance DiffusionTriple.instSigmaFinite (T : DiffusionTriple E) : SigmaFinite T.μ := T.sigmaFinite

/-- (L2) When `μ` is finite it is a probability measure (field `finite_prob`); a theorem, not an
instance. -/
theorem DiffusionTriple.isProb_of_finite (T : DiffusionTriple E) [IsFiniteMeasure T.μ] :
    IsProbabilityMeasure T.μ := T.finite_prob ‹_›

/-- The measure of a diffusion triple is good (field `good`, D1). -/
theorem DiffusionTriple.isGoodMeasure (T : DiffusionTriple E) : IsGoodMeasure T.μ := T.good

end MarkovTriple.BGL
