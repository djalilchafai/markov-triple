import Mathlib
import MarkovTriple.Frozen.MarkovTriple

/-! # Dirichlet form (energy) on the test algebra -/

open MeasureTheory

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- The Dirichlet form `ℰ(f) = ∫ Γ(f,f) dμ` on `𝒜₀` (BGL (3.1.3)/§3.1). Its closure (domain `𝒟(ℰ)`)
is *not* part of the frozen surface. -/
noncomputable def energy (T : MarkovTriple E) (f : E → ℝ) : ℝ :=
  ∫ x, T.Γ f f x ∂T.μ

end MarkovTriple
