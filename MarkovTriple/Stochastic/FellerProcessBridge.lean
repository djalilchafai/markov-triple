import Mathlib
import MarkovTriple.Stochastic.FellerMeasurable
import MarkovTriple.Stochastic.SphereFeller

/-!
# Stochastic layer, part 18: `MarkovProcessBridge` for the zonal sphere `S³` (round 17, `STATEMENTS_R17.md` (A))

The zonal sphere of `SphereFeller.lean` is a conservative Feller triple on a compact metrizable space with full-support
`μ`; the jointly measurable Feller kernels (`FellerMeasurable.lean`) therefore give a `MarkovProcessBridge`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.Sphere

open MarkovTriple.BGL MarkovTriple.BGL.Instances.Sphere

/-- **A `MarkovProcessBridge` for the zonal sphere `S³`**: jointly measurable Markov kernels with exact
Chapman-Kolmogorov, `κ_0 = id`, `μZ` invariant, representing the heat semigroup. -/
noncomputable def sphereMarkovProcessBridge : MarkovProcessBridge sT :=
  fellerMarkovProcessBridge sphere_isFeller (fun t => semigroup_one t)

theorem sphereMarkovProcessBridge_kernel :
    sphereMarkovProcessBridge.kernel = sphereBridge.κ := rfl

theorem sphereMarkovProcessBridge_isMarkov : ∀ t x, sphereMarkovProcessBridge.kernel t x Set.univ = 1 :=
  fun t x => sphereBridge_isMarkov t x

end MarkovTriple.Stochastic.Sphere
