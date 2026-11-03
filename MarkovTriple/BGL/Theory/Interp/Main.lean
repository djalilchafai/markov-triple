import Mathlib
import MarkovTriple.BGL.Theory.Interp.StrongMain

/-!
# Unconditional strong gradient bound (BGL Thm 3.3.18) for every `FullTriple`

`FullTriple.strong_gradient_bound_unconditional`: `CD(ρ,n)`, `ρ ≥ 0` ⇒ `√Γ(P_t f) ≤ e^{-ρt} P_t(√Γ f)` a.e. for `f ∈ 𝒜₀`.
No regularity hypothesis (the structure `StrongInterpolation` is discharged by `FullTriple.strongInterpolation`).
`ρ < 0` is not claimed (see `Theory/GAPS.md`).
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

namespace FullTriple

variable {E : Type*} [MeasurableSpace E] {T : FullTriple E}

theorem strong_gradient_bound_unconditional {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ)
    (f : T.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, Real.sqrt (G T (T.Pt t f) (T.Pt t f) x) ≤
      Real.exp (-ρ * t) * (T.toDiffusionTriple.semigroup t (T.sqrtΓcls f) : Lp ℝ 2 T.μ) x :=
  T.strong_gradient_bound hCD hρ (T.strongInterpolation hCD) f t

end FullTriple

end MarkovTriple.BGL
