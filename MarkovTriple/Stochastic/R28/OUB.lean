import Mathlib
import MarkovTriple.Stochastic.MarkovProcessInterface
import MarkovTriple.Stochastic.OUFull
import MarkovTriple.BGL.Instances.OUCompact.Triple

/-!
# Round 28 (M), part 7: a `MarkovProcessBridge` for the OU triple with test algebra `ℬ` (`ouB`)

`ouB` has the same space `ℝ` and measure `γ` as `ouDiff` but the larger test algebra `ℬ` (bounded smooth, `f' ∈ 𝒮`).  Its Friedrichs semigroup is
given on `ℬ` by Mehler's formula (`PtB_mehler`), so the Mehler kernels (`ouKernel`) represent it on the test class `ℬ`; `ℬ` is dense
(axiom D2) and `kernelRep_of_dense` (via `KernelBridge.ofTestClass`) extends the representation to all bounded measurable `L²(γ)` functions.
No semigroup identification `ouB.semigroup = ouDiff.semigroup` is used or claimed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MarkovTriple.Stochastic.R28

open MarkovTriple.BGL MarkovTriple.BGL.Instances.OUCompact MarkovTriple.Stochastic MarkovTriple.Stochastic.OU
  MarkovTriple.Sanity.OU

/-- the Mehler kernels represent the `ouB` semigroup on the test class `ℬ` -/
theorem ouB_isTestClassRep : IsTestClassRep ouB ouKernel := by
  intro t f hf u hu
  have hm : Measurable f := ouB.measurable f hf
  filter_upwards [PtB_mehler t (f := f) hf u hu] with x hx
  rw [hx, integral_ouKernel hm]

/-- **The `ouB` semigroup is a full `KernelBridge`** (Mehler kernels). -/
noncomputable def ouBKernelBridge : KernelBridge ouB :=
  KernelBridge.ofTestClass ouSemigroup ouSemigroup_invariant ouB_isTestClassRep

/-- **A `MarkovProcessBridge` for `ouB`.** -/
noncomputable def ouBMarkovProcessBridge : MarkovProcessBridge ouB :=
  ouBKernelBridge.toMarkovProcessBridge ouKernel_measurable_joint

theorem ouBMarkovProcessBridge_kernel : ouBMarkovProcessBridge.kernel = ouKernel := rfl

theorem ouBMarkovProcessBridge_isMarkov : ∀ t x, ouBMarkovProcessBridge.kernel t x Set.univ = 1 :=
  fun t x => measure_univ (μ := ouKernel t x)

end MarkovTriple.Stochastic.R28
