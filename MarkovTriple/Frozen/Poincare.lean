import Mathlib
import MarkovTriple.Frozen.Energy

/-! # Poincaré inequality -/

open MeasureTheory

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- Poincaré inequality `PI(C)` (BGL Def. 4.2.1 / (4.2.1)): `μ` is a probability measure and
`Var_μ(f) ≤ C ℰ(f)` for all `f ∈ 𝒜₀`. Variance is Mathlib's `ProbabilityTheory.variance`
(for a probability measure it is `∫ (f − ∫ f)² dμ`). -/
def PoincareIneq (T : MarkovTriple E) (C : ℝ) : Prop :=
  IsProbabilityMeasure T.μ ∧ ∀ f ∈ T.A₀, ProbabilityTheory.variance f T.μ ≤ C * T.energy f

end MarkovTriple
