import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.RegMain
import MarkovTriple.BGL.Theory.Interp.Main

/-!
# Gibbs `e^{-V}dx`, `V'' ≥ ρ ≥ 0`: the strong gradient bound with no hypothesis (BGL Thm 3.3.18)

New unconditional theorem alongside the conditional `gibbsFull_gradient_bound`; the latter is kept unchanged.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData

variable (G : GibbsData)

/-- **Strong gradient bound for `e^{-V}dx`** (`V'' ≥ ρ ≥ 0`), unconditional: `√Γ(P_t f) ≤ e^{-ρt} P_t(√Γ f)`. -/
theorem gibbsFull_strong_gradient_bound_unconditional {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) (f : G.gibbsFull_unconditional.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂G.μ, Real.sqrt (FullTriple.G G.gibbsFull_unconditional
        (G.gibbsFull_unconditional.Pt t f) (G.gibbsFull_unconditional.Pt t f) x) ≤
      Real.exp (-ρ * t) * (G.gibbsFull_unconditional.toDiffusionTriple.semigroup t
        (G.gibbsFull_unconditional.sqrtΓcls f) : Lp ℝ 2 G.μ) x :=
  FullTriple.strong_gradient_bound_unconditional (G.gibbsFull_CD_unconditional hρ) hρ0 f t

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
