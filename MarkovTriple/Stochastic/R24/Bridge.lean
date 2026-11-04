import Mathlib
import MarkovTriple.Stochastic.R24.Measurable
import MarkovTriple.Stochastic.MarkovProcessInterface

/-!
# Round 24 (C), part 7: the `MarkovProcess` semigroup data and (conservative case) `MarkovProcessBridge` for infinite `μ`

* `fellerMarkovProcessDataInf hF : MarkovProcessSemigroupData X` (always: jointly measurable, exact CK, `κ_0 = id`,
  sub-Markov);
* `fellerKernelInf_bind`: if every `κ_t(x, ·)` has total mass `1` (hypothesis `hM`), then `μ.bind κ_t = μ`
  (reversibility `∫_B κ(·,A) dμ = ∫_A κ(·,B) dμ` for compact `A, B`, then `B = K_n ↑ X`);
* `fellerMarkovProcessBridgeInf hF hM : MarkovProcessBridge T`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R23

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

/-- **The `MarkovProcess` semigroup data of a `C_0`-Feller triple** (sub-Markov case; infinite `μ` allowed). -/
noncomputable def fellerMarkovProcessDataInf : MarkovProcessSemigroupData X :=
  (fellerSemigroupInf hF).toMarkovProcessData (fellerKernelInf_measurable_joint hF)

theorem fellerMarkovProcessDataInf_kernel : (fellerMarkovProcessDataInf hF).kernel = fellerKernelInf hF := rfl

section Cons

/-- the `L²` class of the indicator of a compact set -/
noncomputable def indL2 (T : DiffusionTriple X) [IsFiniteMeasureOnCompacts T.μ] {A : Set X}
    (hA : IsCompact A) : Lp ℝ 2 T.μ :=
  (memLp_indicator_const 2 hA.measurableSet (1 : ℝ) (Or.inr hA.measure_lt_top.ne)).toLp _

omit [LocallyCompactSpace X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] in
lemma coeFn_indL2 {A : Set X} (hA : IsCompact A) :
    (indL2 T hA : X → ℝ) =ᵐ[T.μ] A.indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _

lemma semigroup_indL2 (t : ℝ≥0) {A : Set X} (hA : IsCompact A) :
    (T.semigroup t (indL2 T hA) : X → ℝ) =ᵐ[T.μ] fun x => (fellerKernelInf hF t x A).toReal := by
  have hb : ∃ C, ∀ x, |A.indicator (fun _ => (1 : ℝ)) x| ≤ C :=
    ⟨1, fun x => by by_cases h : x ∈ A <;> simp [h]⟩
  have := fellerKernelInf_rep hF t _ (measurable_const.indicator hA.measurableSet) hb
    (memLp_indicator_const 2 hA.measurableSet (1 : ℝ) (Or.inr hA.measure_lt_top.ne))
  filter_upwards [this] with x hx
  rw [show (T.semigroup t (indL2 T hA) : X → ℝ) x = _ from hx]
  rw [integral_indicator hA.measurableSet]
  simp [Measure.real]

/-- **Reversibility for compact sets**: `∫_B κ_t(x, A) dμ(x) = ∫_A κ_t(y, B) dμ(y)`. -/
theorem fellerKernelInf_reversible (t : ℝ≥0) {A B : Set X} (hA : IsCompact A) (hB : IsCompact B) :
    ∫ x, B.indicator (fun x => (fellerKernelInf hF t x A).toReal) x ∂T.μ
      = ∫ y, A.indicator (fun y => (fellerKernelInf hF t y B).toReal) y ∂T.μ := by
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 (T.semigroup_isSelfAdjoint t))
  have h1 : inner ℝ (indL2 T hB) (T.semigroup t (indL2 T hA))
      = ∫ x, B.indicator (fun x => (fellerKernelInf hF t x A).toReal) x ∂T.μ := by
    rw [l2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_indL2 (T := T) hB, semigroup_indL2 hF t hA] with x h1 h2
    rw [h1, h2]
    by_cases hx : x ∈ B <;> simp [hx]
  have h2 : inner ℝ (indL2 T hA) (T.semigroup t (indL2 T hB))
      = ∫ y, A.indicator (fun y => (fellerKernelInf hF t y B).toReal) y ∂T.μ := by
    rw [l2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_indL2 (T := T) hA, semigroup_indL2 hF t hB] with x h1 h2
    rw [h1, h2]
    by_cases hx : x ∈ A <;> simp [hx]
  rw [← h1, ← h2]
  exact (real_inner_comm _ _).trans (hsym _ _)

variable (hM : ∀ t x, fellerKernelInf hF t x Set.univ = 1)
include hM

/-- on compact sets, `μ.bind κ_t` and `μ` agree (Markov kernels, symmetry) -/
theorem fellerKernelInf_bind_compact (t : ℝ≥0) {A : Set X} (hA : IsCompact A) :
    T.μ.bind (fellerKernelInf hF t) A = T.μ A := by
  have hbind := fellerKernelInf_bind_le hF t
  have hAm : MeasurableSet A := hA.measurableSet
  have hAfin : T.μ A < ∞ := hA.measure_lt_top
  have hνA : T.μ.bind (fellerKernelInf hF t) A = ∫⁻ x, fellerKernelInf hF t x A ∂T.μ :=
    Measure.bind_apply hAm (fellerKernelInf hF t).aemeasurable
  have hmeas : Measurable fun x => (fellerKernelInf hF t x A).toReal :=
    (Kernel.measurable_coe _ hAm).ennreal_toReal
  have hlf : ∫⁻ x, fellerKernelInf hF t x A ∂T.μ ≠ ∞ := by
    rw [← hνA]; exact ((hbind A).trans_lt hAfin).ne
  have hint : Integrable (fun x => (fellerKernelInf hF t x A).toReal) T.μ :=
    integrable_toReal_of_lintegral_ne_top (Kernel.measurable_coe _ hAm).aemeasurable hlf
  -- the exhaustion
  have hrev := fun n => fellerKernelInf_reversible hF t hA ((cexh X).isCompact n)
  have hL : Tendsto (fun n => ∫ x, (cexh X n).indicator (fun x => (fellerKernelInf hF t x A).toReal) x ∂T.μ)
      atTop (𝓝 (∫ x, (fellerKernelInf hF t x A).toReal ∂T.μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => (fellerKernelInf hF t x A).toReal)
      (fun n => (hmeas.indicator ((cexh X).isCompact n).measurableSet).aestronglyMeasurable) hint
      (fun n => Filter.Eventually.of_forall fun x => ?_)
      (Filter.Eventually.of_forall fun x => ?_)
    · by_cases hx : x ∈ cexh X n
      · simp [hx]
      · simp [hx]
    · refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := (cexh X).exists_mem x
      filter_upwards [eventually_ge_atTop N] with n hn
      simp [(cexh X).subset hn hN]
  have hR : Tendsto (fun n => ∫ y, A.indicator (fun y => (fellerKernelInf hF t y (cexh X n)).toReal) y ∂T.μ)
      atTop (𝓝 (∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂T.μ)) := by
    have hint1 : Integrable (A.indicator (fun _ => (1 : ℝ))) T.μ :=
      (integrableOn_const (C := (1 : ℝ)) hAfin.ne).integrable_indicator hAm
    refine tendsto_integral_of_dominated_convergence (A.indicator fun _ => (1 : ℝ))
      (fun n => ((Kernel.measurable_coe _ ((cexh X).isCompact n).measurableSet).ennreal_toReal.indicator
        hAm).aestronglyMeasurable) hint1 (fun n => Filter.Eventually.of_forall fun y => ?_)
      (Filter.Eventually.of_forall fun y => ?_)
    · by_cases hy : y ∈ A
      · simp only [hy, Set.indicator_of_mem, Real.norm_eq_abs]
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
        have := (fellerKernelInf_subMarkov hF t y)
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one
          ((measure_mono (Set.subset_univ _)).trans (this.trans (by simp)))
      · simp [hy]
    · by_cases hy : y ∈ A
      · simp only [hy, Set.indicator_of_mem]
        have hmono : Monotone (cexh X) := fun m n h => (cexh X).subset h
        have := tendsto_measure_iUnion_atTop (μ := fellerKernelInf hF t y) hmono
        rw [(cexh X).iUnion_eq, hM t y] at this
        have h2 := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp this
        exact h2
      · simp [hy]
  have hEq : ∫ x, (fellerKernelInf hF t x A).toReal ∂T.μ = ∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂T.μ := by
    refine tendsto_nhds_unique hL ?_
    simp_rw [hrev]
    exact hR
  rw [integral_indicator hAm] at hEq
  simp only [integral_const, smul_eq_mul, mul_one, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.real] at hEq
  have h3 : ∫ x, (fellerKernelInf hF t x A).toReal ∂T.μ = (∫⁻ x, fellerKernelInf hF t x A ∂T.μ).toReal :=
    integral_toReal (Kernel.measurable_coe _ hAm).aemeasurable
      (Filter.Eventually.of_forall fun x => measure_lt_top _ _)
  rw [h3] at hEq
  rw [hνA]
  exact (ENNReal.toReal_eq_toReal_iff' hlf hAfin.ne).1 hEq

/-- **Equality invariance** `μ.bind κ_t = μ` for Markov kernels (conservative + symmetric). -/
theorem fellerKernelInf_bind (t : ℝ≥0) : T.μ.bind (fellerKernelInf hF t) = T.μ := by
  have hbind := fellerKernelInf_bind_le hF t
  have : IsFiniteMeasureOnCompacts (T.μ.bind (fellerKernelInf hF t)) :=
    ⟨fun K hK => lt_of_le_of_lt (hbind K) hK.measure_lt_top⟩
  have : (T.μ.bind (fellerKernelInf hF t)).Regular := inferInstance
  have : T.μ.Regular := inferInstance
  apply Measure.OuterRegular.ext_isOpen
  apply Measure.InnerRegularWRT.eq_of_innerRegularWRT_of_forall_eq Measure.Regular.innerRegular
    Measure.Regular.innerRegular
  intro K hK
  exact fellerKernelInf_bind_compact hF hM t hK

/-- **A `MarkovProcessBridge` for a conservative (pointwise Markov) `C_0`-Feller triple with infinite `μ`**:
jointly measurable Markov kernels with exact Chapman-Kolmogorov, `κ_0 = id`, `μ` invariant, representing `P_t`. -/
noncomputable def fellerMarkovProcessBridgeInf : MarkovProcessBridge T where
  toMarkovProcessSemigroupData := fellerMarkovProcessDataInf hF
  rep := fun t g hg hb hL => fellerKernelInf_rep hF t g hg hb hL
  invariant := fun t => fellerKernelInf_bind hF hM t

end Cons

end MarkovTriple.Stochastic.R24
