import Mathlib
import MarkovTriple.Stochastic.R23.Markov
import MarkovTriple.BGL.Instances.Lebesgue.Full

/-!
# Round 23 (S), part 5: non-vacuity, Lebesgue measure on `ℝ`

`lebesgueFull` (`μ = volume`, infinite) is a `StandardTriple` on the non-compact space `ℝ`; its semigroup is the heat
semigroup.  The infinite-`μ` kernel representation applies (no finiteness of `μ` is used), and, by conservativity of
`lebesgueFull`, the kernels are Markov (`exists_markovRep`).  See `STATEMENTS_R23_S.md`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R23

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.BGL.Lebesgue

/-- the Lebesgue triple has the infinite reference measure `volume`. -/
example : lebesgueFull.toDiffusionTriple.μ = (volume : Measure ℝ) := rfl

/-- ... and that measure is genuinely infinite (so this is not covered by the finite-`μ` theorem R22). -/
example : lebesgueFull.toDiffusionTriple.μ Set.univ = ∞ := Real.volume_univ

/-- `volume` is finite on compacts, transported to the triple. -/
instance lebesgue_locFin : IsFiniteMeasureOnCompacts lebesgueFull.toDiffusionTriple.μ := by
  have h : lebesgueFull.toDiffusionTriple.μ = (volume : Measure ℝ) := rfl
  rw [h]; infer_instance

instance lebesgue_locFin' : IsFiniteMeasureOnCompacts lebesgueFull.toStandardTriple.μ :=
  lebesgue_locFin

/-- **Kernel representation of the heat semigroup on `ℝ` with Lebesgue measure.** -/
noncomputable def lebesgueKernelRep : KernelRepresentation lebesgueFull.toDiffusionTriple :=
  ncKernelRepInf lebesgueFull.toDiffusionTriple

theorem lebesgueKernelRep_subInvariant (t : ℝ≥0) :
    (volume : Measure ℝ).bind (lebesgueKernelRep.κ t) ≤ volume :=
  ncKernelRepInf_subInvariant lebesgueFull.toDiffusionTriple t

/-- the Lebesgue heat semigroup has a Markov (conservative) kernel representation. -/
theorem lebesgue_exists_markovRep :
    ∃ K : KernelRepresentation lebesgueFull.toDiffusionTriple, K.IsMarkovRep :=
  exists_markovRep lebesgueFull.toStandardTriple

end MarkovTriple.Stochastic.R23
