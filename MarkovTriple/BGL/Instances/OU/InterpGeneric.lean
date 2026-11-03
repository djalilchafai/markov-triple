import Mathlib
import MarkovTriple.BGL.Instances.OU.StrongFinal
import MarkovTriple.BGL.Theory.Interp.Main

/-!
# OU: consistency with the generic discharge

`ouFull_strongInterpolation_generic`: the generic `FullTriple.strongInterpolation` yields `StrongInterpolation` for the OU Full
triple without the Mehler-specific computation (`ouFull_StrongInterpolation`, kept).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.OU

theorem ouFull_strongInterpolation_generic : ouFull.StrongInterpolation :=
  FullTriple.strongInterpolation ouFull_CD

theorem ouFull_strong_gradient_bound_generic (f : ouFull.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂ouFull.μ, Real.sqrt (ouFull.toDiffusionTriple.ΓA (ouFull.Pt t f) (ouFull.Pt t f) x) ≤
      Real.exp (-1 * t) *
        (ouFull.toDiffusionTriple.semigroup t (ouFull.sqrtΓcls f) : Lp ℝ 2 ouFull.μ) x :=
  FullTriple.strong_gradient_bound_unconditional ouFull_CD zero_le_one f t

end MarkovTriple.BGL.Instances.OU
