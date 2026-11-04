import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAPI

/-!
# Strong `L²`-derivative of the heat flow on `ℝ^d` (Round 24, stream A, part H-b)

STUB (statement fixed; proof `sorry` until stream H-b delivers).  Port of `IsTest.hasDerivAt_heatL2`
(`Instances/Lebesgue/Heat.lean`, `rho`, Taylor remainder, Gaussian integration by parts) to `ℝ^d`.
`∂ₐ heatRd a φ = a · heatRd a (Δφ)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ : (Fin d → ℝ) → ℝ}

theorem hasDerivAt_heatL2 (hφ : φ ∈ A₀ d) (a : ℝ) :
    HasDerivAt (fun b : ℝ => heatL2 φ b) (a • heatL2 (Lf φ) a) a := sorry

end MarkovTriple.BGL.LebesgueRd
