import Mathlib
import MarkovTriple.Frozen.Energy
import MarkovTriple.Frozen.Ent

/-! # Logarithmic Sobolev inequality -/

open MeasureTheory

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- Logarithmic Sobolev inequality `LSI(C)` (BGL Def. 5.1.1, in the form (5.1.3) with constant `C`
as in PLAN §4.1): `μ` is a probability measure and `Ent_μ(f²) ≤ 2 C ℰ(f)` for all `f ∈ 𝒜₀`.
For the standard Gaussian, `C = 1`. -/
def LogSobolevIneq (T : MarkovTriple E) (C : ℝ) : Prop :=
  IsProbabilityMeasure T.μ ∧
    ∀ f ∈ T.A₀, Ent T.μ (fun x => f x ^ 2) ≤ 2 * C * T.energy f

end MarkovTriple
