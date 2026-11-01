import Mathlib

/-!
# Partial derivatives on `Fin k → ℝ` (helper for the change-of-variables formulas)

Used in the diffusion property D3 (BGL Def. 3.1.3, formula (3.1.2)/(3.4.1)) and in the change of
variables formula for `L` (BGL (3.1.8)), also required on the extended algebra by F6.
-/

namespace MarkovTriple.BGL

/-- First partial derivative `∂ᵢψ(z)` of `ψ : ℝᵏ → ℝ` (Fréchet derivative applied to the `i`-th
basis vector). Junk value `0` where `ψ` is not differentiable. -/
noncomputable def pderiv {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (i : Fin k) (z : Fin k → ℝ) : ℝ :=
  fderiv ℝ ψ z (Pi.single i 1)

/-- Second partial derivative `∂ⱼ∂ᵢψ(z)`. For `ψ` of class `C²` it is symmetric in `(i,j)`. -/
noncomputable def pderiv₂ {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (i j : Fin k) (z : Fin k → ℝ) : ℝ :=
  fderiv ℝ (fun y => pderiv ψ i y) z (Pi.single j 1)

end MarkovTriple.BGL
