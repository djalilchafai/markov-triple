import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Unconditional

/-!
# The finite-measure counterpart on `ℝ^d`: the Gaussian `FullTriple` (Round 24, stream A)

BGL's `ℝ^d` examples with a probability measure are the Gibbs/OU triples `L = Δ - ∇V·∇`, `μ ∝ e^{-V}dx`.  For `V = |x|²/2` the triple
`(gaussData d).gibbsRdFull_unconditional` of `Instances/GibbsRd` (Round 16, `ellReg` + Friedrichs + Sobolev) is already a `FullTriple (Fin d → ℝ)` with
`CD(1,∞)`, Poincaré and log-Sobolev; this file only gives it a stable name next to the Lebesgue one.  No new analysis.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BGL.LebesgueRd

open MarkovTriple.BGL MarkovTriple.BGL.Instances.GibbsRd

/-- The Ornstein–Uhlenbeck (standard Gaussian) full triple on `ℝ^d`. -/
noncomputable def gaussRdFull (d : ℕ) : FullTriple (Fin d → ℝ) :=
  (gaussData d).gibbsRdFull_unconditional

theorem gaussRdFull_CD (d : ℕ) : (gaussRdFull d).CD 1 ∞ :=
  (gaussData d).gibbsRdFull_CD_unconditional hessGe_gauss

instance (d : ℕ) : IsProbabilityMeasure (gaussRdFull d).μ :=
  (inferInstance : IsProbabilityMeasure (gaussData d).toEll.μ)

theorem gaussRdFull_poincare (d : ℕ) : (gaussRdFull d).toDiffusionTriple.PI (1 / 1) :=
  (gaussData d).gibbsRdFull_poincare_unconditional one_pos hessGe_gauss

theorem gaussRdFull_logSobolev (d : ℕ) : (gaussRdFull d).toDiffusionTriple.LS (1 / 1) 0 :=
  (gaussData d).gibbsRdFull_logSobolev_unconditional one_pos hessGe_gauss

end MarkovTriple.BGL.LebesgueRd
