import Mathlib
import MarkovTriple.Stochastic.RepExtend
import MarkovTriple.Stochastic.OU

/-!
# Stochastic layer, part 5: the Ornstein-Uhlenbeck semigroup is a full `KernelBridge`

Closes the gap recorded in `OU.lean`: the Mehler kernels represent `P_t` on **all** bounded measurable
`L²(γ)` functions, not only on the test class `C_c^∞`.

Classical statements used (all via `RepExtend.lean`): the Mehler kernels are Markov and `γ` is
invariant (`ouKernel_invariant`), hence `g ↦ κ_t g` is an `L²(γ)`-contraction (Jensen /
Cauchy-Schwarz; BGL (1.2.1) and the remark after Def. 1.2.1: Markov kernels with invariant `μ` contract
`L^p(μ)`); the representation holds on `C_c^∞` (Mehler formula, BGL Sect. 2.7.1, p. 103-104, kernel
densities (Mehler kernel)); `C_c^∞` is dense in `L²(γ)`
(axiom D2 of `ouDiff`); `P_t` is an `L²` contraction.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal
open MarkovTriple.Sanity.OU hiding A₀
open MarkovTriple.BGL MarkovTriple.BGL.Instances.OU

namespace MarkovTriple.Stochastic.OU

/-- **The OU semigroup is a full `KernelBridge`**: exact Chapman-Kolmogorov, `γ` invariant, and
`P_t [g] = (x ↦ ∫ g dκ_t(x,·))` `γ`-a.e. for every bounded measurable `g ∈ L²(γ)`. -/
noncomputable def ouKernelBridge : KernelBridge ouDiff :=
  KernelBridge.ofTestClass ouSemigroup ouSemigroup_invariant ou_isTestClassRep

theorem ouKernelBridge_κ : ouKernelBridge.κ = ouKernel := rfl

theorem ouKernelBridge_isMarkov : ouKernelBridge.toSubMarkovKernelSemigroup.IsMarkov :=
  ouSemigroup_isMarkov

/-- The OU kernel representation, in the `a.e.`-Chapman-Kolmogorov interface of `KernelRep.lean`. -/
noncomputable def ouKernelRepresentation : KernelRepresentation ouDiff :=
  ouKernelBridge.toKernelRepresentation

/-- **Full OU representation**: for every bounded measurable `g ∈ L²(γ)`,
`P_t g = (x ↦ ∫ g dκ_t(x,·))` `γ`-a.e. -/
theorem ou_rep_full (t : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 γ) :
    ((Pt t (hL.toLp g) : Lp ℝ 2 ouDiff.μ) : ℝ → ℝ) =ᵐ[γ] fun x => ∫ y, g y ∂(ouKernel t x) :=
  ouKernelBridge.rep t g hg hb hL

end MarkovTriple.Stochastic.OU
