import Mathlib
import MarkovTriple.Stochastic.RieszRep

/-!
# Stochastic layer, part 11: conservative triples give Markov (not merely sub-Markov) kernels

If `P_t 1 = 1` (conservative, BGL Sect. 3.2 / `conservative_iff_semigroup_one`), the Riesz kernels of
`RieszRep.lean` have total mass `1` for `μ`-a.e. `x` (apply `rep` to `g = 1`); redefining them on the
(measurable) null set `{κ_t(x, ·)(E) ≠ 1}` as the Dirac mass `δ_x` gives kernels that are Markov **everywhere**
and still represent `P_t` (the representation is only a.e.).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (T : DiffusionTriple X) [IsFiniteMeasure T.μ]

/-- Conservative case: the Riesz kernels have mass one a.e. -/
theorem rieszKernel_univ_ae (h : ∀ t, T.semigroup t T.one2 = T.one2) (t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, rieszKernel T t x Set.univ = 1 := by
  have hr := (rieszKernelRep T).rep t (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by simp⟩
    (memLp_const 1)
  have e : (memLp_const (1 : ℝ)).toLp (fun _ => (1 : ℝ)) = T.one2 := rfl
  rw [e, h t] at hr
  filter_upwards [hr, T.coeFn_one2] with x h1 h2
  have : IsFiniteMeasure (rieszKernel T t x) :=
    ⟨lt_of_le_of_lt (rieszKernel_subMarkov T t x) ENNReal.one_lt_top⟩
  have h3 : (rieszKernel T t x).real Set.univ = 1 := by
    have : ∫ y, (1 : ℝ) ∂(rieszKernel T t x) = (rieszKernel T t x).real Set.univ := by simp
    rw [← this]
    exact h1.symm.trans h2
  rw [Measure.real] at h3
  exact (ENNReal.toReal_eq_one_iff _).1 h3

/-- **Markov kernel representation for conservative triples on compact metrizable spaces.** -/
theorem rieszKernelRep_markov (h : ∀ t, T.semigroup t T.one2 = T.one2) :
    ∃ K : KernelRepresentation T, K.IsMarkovRep := by
  classical
  have hs : ∀ t, MeasurableSet {x | rieszKernel T t x Set.univ = 1} := fun t =>
    (Kernel.measurable_coe (rieszKernel T t) MeasurableSet.univ) (measurableSet_singleton 1)
  let κ' : ℝ≥0 → Kernel X X := fun t => Kernel.piecewise (hs t) (rieszKernel T t) Kernel.id
  have hmk : ∀ t x, κ' t x Set.univ = 1 := by
    intro t x
    by_cases hx : x ∈ {x | rieszKernel T t x Set.univ = 1}
    · simp only [κ', Kernel.piecewise_apply, hx, ite_true]; exact hx
    · simp only [κ', Kernel.piecewise_apply, hx, ite_false]; simp
  have hae : ∀ t, ∀ᵐ x ∂T.μ, κ' t x = rieszKernel T t x := fun t => by
    filter_upwards [rieszKernel_univ_ae T h t] with x hx
    simp [κ', Kernel.piecewise_apply, hx]
  refine ⟨⟨κ', fun t x => (hmk t x).le, ?_⟩, hmk⟩
  intro t g hg hb hL
  filter_upwards [(rieszKernelRep T).rep t g hg hb hL, hae t] with x h1 h2
  rw [h1, h2]; rfl

end MarkovTriple.Stochastic
