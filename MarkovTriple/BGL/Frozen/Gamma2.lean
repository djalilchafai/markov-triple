import Mathlib
import MarkovTriple.BGL.Frozen.GammaA

/-!
# The operator `Γ₂` (BGL Definition 3.3.12)
-/

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- `Γ₂(f,g) = ½ (L Γ(f,g) − Γ(f, Lg) − Γ(Lf, g))` (BGL Def. 3.3.12), with `Γ` the formula-defined
carré du champ `ΓA`.  Meaningful for `f, g` in the extended algebra `𝒜` of a full triple.
`Γ₂(f) = Γ₂(f,f)`. -/
noncomputable def DiffusionTriple.Γ₂ (T : DiffusionTriple E) (f g : E → ℝ) : E → ℝ :=
  fun x => (T.L (T.ΓA f g) x - T.ΓA f (T.L g) x - T.ΓA (T.L f) g x) / 2

end MarkovTriple.BGL
