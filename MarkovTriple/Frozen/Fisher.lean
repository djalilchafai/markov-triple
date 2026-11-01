import Mathlib
import MarkovTriple.Frozen.MarkovTriple

/-! # Fisher information -/

open MeasureTheory

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- Fisher information `I_μ(h) = ∫ Γ(h,h)/h dμ` (BGL §5.7; numbering to be verified). Intended for `h > 0` in `𝒜₀`;
`x/0 = 0` in Lean. Equals `4 ∫ Γ(√h) dμ` for positive `h` (a theorem, not part of the surface). -/
noncomputable def fisherInfo (T : MarkovTriple E) (h : E → ℝ) : ℝ :=
  ∫ x, T.Γ h h x / h x ∂T.μ

end MarkovTriple
