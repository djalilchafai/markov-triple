import Mathlib
import MarkovTriple.Stochastic.FellerKernel
import MarkovTriple.BGL.Semigroup.Conservative

/-!
# Stochastic layer, part 19: Feller bridge for every Standard / Compact triple (round 16, `STATEMENTS_R16.md` T2 corollary)

For a `StandardTriple` (S10 ergodicity, S11 conservativeness) with finite `μ`, S11 (BGL Def. 3.1.12) gives
`P_t 1 = 1` in `L²` (`semigroup_one_of_conservative`, `conservative_all`), hence the hypothesis `hcons` of
`fellerBridge` is automatic.  The remaining hypotheses are exactly (F) `IsFeller` and (S) full support.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal


namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

/-- A standard triple with finite measure has `P_t 1 = 1`. -/
theorem standardSemigroup_one_fin {E : Type*} [MeasurableSpace E] (S : StandardTriple E)
    [IsFiniteMeasure S.μ] (t : ℝ≥0) : S.semigroup t S.one2 = S.one2 := by
  obtain ⟨u, hu⟩ := S.exhaustion
  exact S.toDiffusionTriple.semigroup_one_of_conservative hu t (StandardTriple.conservative_all S hu t)

/-- **The exact `KernelBridge` of a Feller standard triple on a compact metrizable space with full-support `μ`.** -/
noncomputable def standardFellerBridge {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (S : StandardTriple X) [IsFiniteMeasure S.μ] [S.μ.IsOpenPosMeasure]
    (hF : IsFeller S.toDiffusionTriple) : KernelBridge S.toDiffusionTriple :=
  MarkovTriple.Stochastic.fellerBridge hF (fun t => standardSemigroup_one_fin S t)

/-- Same for a `CompactTriple` (`μ` is automatically finite: `compactTriple_isFiniteMeasure`, to be supplied as an instance). -/
noncomputable def compactFellerBridge {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (C : CompactTriple X) [IsFiniteMeasure C.μ] [C.μ.IsOpenPosMeasure]
    (hF : IsFeller C.toDiffusionTriple) :
    KernelBridge C.toDiffusionTriple :=
  standardFellerBridge C.toFullTriple.toStandardTriple hF

end MarkovTriple.Stochastic
