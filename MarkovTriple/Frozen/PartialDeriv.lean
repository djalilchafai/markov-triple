import Mathlib

/-!
# Partial derivatives on `Fin k → ℝ` (helper for the diffusion property)
-/

open scoped ENNReal

namespace MarkovTriple

/-- First partial derivative `∂ᵢψ(z)` of `ψ : ℝᵏ → ℝ` (Fréchet derivative applied to the `i`-th basis
vector). Junk value `0` where `ψ` is not differentiable. Used in the chain rule of BGL Def. 3.1.8
(diffusion property, see also BGL §1.11 eq. (1.11.3)). -/
noncomputable def pderiv {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (i : Fin k) (z : Fin k → ℝ) : ℝ :=
  fderiv ℝ ψ z (Pi.single i 1)

/-- Second partial derivative `∂ⱼ∂ᵢψ(z)`. For `ψ` of class `C²` it is symmetric in `(i,j)`. -/
noncomputable def pderiv₂ {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (i j : Fin k) (z : Fin k → ℝ) : ℝ :=
  fderiv ℝ (fun y => pderiv ψ i y) z (Pi.single j 1)

end MarkovTriple
