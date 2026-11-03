import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.RegMain
import MarkovTriple.BGL.Instances.GibbsRd.Main
import MarkovTriple.BGL.Theory.Interp.JensenGrad

/-!
# Gibbs (`ℝ` and `ℝ^d`): weak gradient bound (BGL Cor 3.3.19), `HasGradientBound`, with no hypothesis

New unconditional theorems alongside the conditional `gibbsFull_gradient_bound`, `gibbsRdFull_gradient_bound`
(unchanged).  `ρ ≥ 0` (see `Theory/Interp/STATEMENTS_R16_Jensen.md`).  The `ℝ^d` version keeps the explicit
hypotheses `WeakHypo`, `F8` of `gibbsRdFull`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData

variable (G : GibbsData)

/-- **Weak gradient bound for `e^{-V}dx`** (`V'' ≥ ρ ≥ 0`), unconditional (Cor 3.3.19). -/
theorem gibbsFull_gradient_bound_unconditional {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) (f : G.gibbsFull_unconditional.A₀) (t : ℝ≥0) :
    G.gibbsFull_unconditional.toDiffusionTriple.ΓA (G.gibbsFull_unconditional.Pt t f)
        (G.gibbsFull_unconditional.Pt t f) ≤ᵐ[G.μ] fun x =>
      Real.exp (-2 * ρ * t) * (G.gibbsFull_unconditional.toDiffusionTriple.semigroup t
        (G.gibbsFull_unconditional.toDiffusionTriple.cls
          ⟨G.gibbsFull_unconditional.toDiffusionTriple.ΓA f.1 f.1,
            G.gibbsFull_unconditional.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 G.μ) x :=
  FullTriple.gradient_bound_unconditional _ (G.gibbsFull_CD_unconditional hρ) hρ0 f t

/-- `HasGradientBound` for the unconditional Gibbs Full triple (`V'' ≥ ρ ≥ 0`). -/
theorem gibbsFull_hasGradientBound {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    HasGradientBound G.gibbsFull_unconditional.toDiffusionTriple G.gibbsFull_unconditional.A ρ :=
  FullTriple.hasGradientBound_unconditional _ (G.gibbsFull_CD_unconditional hρ) hρ0

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL

namespace GibbsRdData

variable {d : ℕ} (G : GibbsRdData d)

/-- Weak gradient bound for `e^{-V}dx` on `ℝ^d` (`Hess V ≥ ρ ≥ 0`), with the explicit `WeakHypo`/`F8`
hypotheses of `gibbsRdFull`, and no `GradientInterpolation`. -/
theorem gibbsRdFull_gradient_bound_unconditional (hH : G.WeakHypo) (h8 : G.F8) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : HessGe G.V ρ) (f : (G.gibbsRdFull hH h8).A₀) (t : ℝ≥0) :
    (G.gibbsRdFull hH h8).toDiffusionTriple.ΓA ((G.gibbsRdFull hH h8).Pt t f)
        ((G.gibbsRdFull hH h8).Pt t f) ≤ᵐ[G.toEll.μ] fun x =>
      Real.exp (-2 * ρ * t) * ((G.gibbsRdFull hH h8).toDiffusionTriple.semigroup t
        ((G.gibbsRdFull hH h8).toDiffusionTriple.cls
          ⟨(G.gibbsRdFull hH h8).toDiffusionTriple.ΓA f.1 f.1,
            (G.gibbsRdFull hH h8).ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 G.toEll.μ) x :=
  FullTriple.gradient_bound_unconditional _ (G.gibbsRdFull_CD hH h8 hρ) hρ0 f t

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
