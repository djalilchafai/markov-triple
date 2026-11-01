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

/-- Canonical hypothesis for theorems about `fisherInfo` (ERRATA F4): `h` is a.e. strictly positive
and the integrand `Γ(h,h)/h` is integrable, so `fisherInfo T h` is a genuine integral and not the
Bochner junk value `0`. Intended for `h ∈ 𝒜₀` (or `h ∈ 𝒜` for a full triple); membership is left to
the theorem, as `Γ` is only constrained on the algebra. -/
def IsFisherAdmissible (T : MarkovTriple E) (h : E → ℝ) : Prop :=
  (∀ᵐ x ∂T.μ, 0 < h x) ∧ Integrable (fun x => T.Γ h h x / h x) T.μ

end MarkovTriple
