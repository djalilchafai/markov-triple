import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-!
# The carré du champ on the extended algebra, defined by the formula (BGL Def. 3.3.1 (iv), F4)
-/

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- The carré du champ defined from `L` by the polarised formula
`Γ(f,g) = ½ (L(fg) − f L g − g L f)` (BGL Def. 3.3.1 (iv) / F4).  On the extended algebra `𝒜` of a
full triple this *is* the definition of `Γ` (there is no separate field); on `𝒜₀` it agrees with the
field `DiffusionTriple.Γ` a.e. (consequence of D3 + D5, BGL (3.1.6)). -/
noncomputable def DiffusionTriple.ΓA (T : DiffusionTriple E) (f g : E → ℝ) : E → ℝ :=
  fun x => (T.L (f * g) x - f x * T.L g x - g x * T.L f x) / 2

end MarkovTriple.BGL
