import Mathlib
import MarkovTriple.Frozen.MarkovTriple

/-! # Iterated carré du champ `Γ₂` -/

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- `Γ₂(f) = ½ (L Γ(f,f) − 2 Γ(f, Lf))` (BGL Definition 1.4.2; exact numbering to be verified, in the Markov-triple
setting). Pointwise, as a function on `E`. Meaningful for `f ∈ 𝒜₀`. -/
noncomputable def Γ₂ (T : MarkovTriple E) (f : E → ℝ) : E → ℝ :=
  fun x => (T.L (T.Γ f f) x - 2 * T.Γ f (T.L f) x) / 2

end MarkovTriple
