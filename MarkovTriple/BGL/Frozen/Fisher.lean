import Mathlib

/-! # Fisher information (BGL (5.1.6)) -/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- Fisher information `I_μ(h) = ∫ Γ(h,h)/h dμ` (BGL (5.1.6)), generic in `(μ, Γ)`.  Intended for
`h > 0`; `x/0 = 0` in Lean.  Equals `4 ∫ Γ(√h) dμ` for positive `h` (a theorem, not part of the
surface). -/
noncomputable def fisherInfo (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (h : E → ℝ) : ℝ :=
  ∫ x, Γ h h x / h x ∂μ

/-- Canonical hypothesis for theorems about `fisherInfo`: `h` is a.e. strictly positive and the
integrand `Γ(h,h)/h` is integrable, so `fisherInfo` is a genuine integral and not the Bochner
junk value `0`. -/
def IsFisherAdmissible (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (h : E → ℝ) : Prop :=
  (∀ᵐ x ∂μ, 0 < h x) ∧ Integrable (fun x => Γ h h x / h x) μ

end MarkovTriple.BGL
