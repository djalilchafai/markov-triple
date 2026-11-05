import Mathlib
import MarkovTriple.Stochastic.R28.FellerSG

/-!
# Round 28 (M), part 3: the compact Feller kernel layer for abstract semigroup data

Verbatim transcription of `FellerKernel.lean` / `RepExtend.lean` / `FellerMeasurable.lean` (R16/R17/R15) with
`T : DiffusionTriple X` replaced by `T : SGData X` (only the semigroup and `T.μ` are used there).  Names are prefixed `sg`
(`sgOp`, `sgKernel`, ...).  No new mathematics.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R28

open MarkovTriple.BGL MarkovTriple.Stochastic


section Meas

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {T : SGData X} [IsFiniteMeasure T.μ]
  [T.μ.IsOpenPosMeasure] (hF : IsFellerSG T)
omit [T2Space X] [SecondCountableTopology X] in
/-- `{t : ‖P_t f - g‖_∞ ≤ r}` is closed: strong `L²` continuity of the semigroup and order-closedness of `L²`. -/
lemma isClosed_sgOp_ball (f g : C(X, ℝ)) (r : ℝ) :
    IsClosed {t : ℝ≥0 | ∀ x, |sgOp hF t f x - g x| ≤ r} := by
  let a : C(X, ℝ) := ⟨fun x => g x - r, g.continuous.sub continuous_const⟩
  let b : C(X, ℝ) := ⟨fun x => g x + r, g.continuous.add continuous_const⟩
  have hcont : Continuous fun t : ℝ≥0 => T.semigroup t (clsC T.μ f) :=
    T.continuous_semigroup_apply _
  have hset : {t : ℝ≥0 | ∀ x, |sgOp hF t f x - g x| ≤ r} =
      (fun t => T.semigroup t (clsC T.μ f)) ⁻¹' ({u | clsC T.μ a ≤ u} ∩ {u | u ≤ clsC T.μ b}) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, sgOp_cls hF,
      clsC_le_iff]
    constructor
    · intro h
      refine ⟨fun x => ?_, fun x => ?_⟩
      · have := (abs_le.1 (h x)).1
        simp only [a, ContinuousMap.coe_mk]; linarith
      · have := (abs_le.1 (h x)).2
        simp only [b, ContinuousMap.coe_mk]; linarith
    · rintro ⟨h1, h2⟩ x
      have e1 := h1 x
      have e2 := h2 x
      simp only [a, b, ContinuousMap.coe_mk] at e1 e2
      exact abs_le.2 ⟨by linarith, by linarith⟩
  rw [hset]
  exact (isClosed_le continuous_const continuous_id |>.inter (isClosed_le continuous_id continuous_const)).preimage hcont

/-- `t ↦ P_t f` is Borel measurable into `(C(X), ‖·‖_∞)`. -/
theorem measurable_sgOp_time (f : C(X, ℝ)) : Measurable fun t : ℝ≥0 => sgOp hF t f := by
  have hball : ∀ (g : C(X, ℝ)) (r : ℝ), 0 ≤ r →
      MeasurableSet {t : ℝ≥0 | sgOp hF t f ∈ Metric.closedBall g r} := by
    intro g r hr
    have := (isClosed_sgOp_ball hF f g r).measurableSet
    convert this using 1
    ext t
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm]
    rw [ContinuousMap.norm_le _ hr]
    simp [Real.norm_eq_abs]
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  refine measurable_of_isOpen fun U hU => ?_
  have hU' : (fun t : ℝ≥0 => sgOp hF t f) ⁻¹' U =
      ⋃ (p : ℕ × ℕ) (_ : Metric.closedBall (g p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ U),
        {t : ℝ≥0 | sgOp hF t f ∈ Metric.closedBall (g p.1) (1 / ((p.2 : ℝ) + 1))} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro ht
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hU _ ht
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hg (sgOp hF t f) (1 / ((k : ℝ) + 1))
        (by positivity)
      refine ⟨(n, k), fun y hy => hsub ?_, ?_⟩
      · rw [Metric.mem_ball]
        have h1 : dist y (g n) ≤ 1 / ((k : ℝ) + 1) := hy
        have h2 : dist (sgOp hF t f) (g n) < 1 / ((k : ℝ) + 1) := hn
        have := dist_triangle y (g n) (sgOp hF t f)
        rw [dist_comm (g n)] at this
        linarith
      · rw [Metric.mem_closedBall, dist_comm]
        exact (show dist (g n) (sgOp hF t f) < 1 / ((k : ℝ) + 1) by
          rw [dist_comm]; exact hn).le
    · rintro ⟨p, hp, hmem⟩
      exact hp hmem
  rw [hU']
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ => hball _ _ (by positivity)

/-- `(t, x) ↦ (P_t f)(x)` is jointly measurable. -/
theorem measurable_sgOp_joint (f : C(X, ℝ)) :
    Measurable fun p : ℝ≥0 × X => sgOp hF p.1 f p.2 := by
  have h1 : Measurable fun p : ℝ≥0 × X => ((sgOp hF p.1 f, p.2) : C(X, ℝ) × X) :=
    ((measurable_sgOp_time hF f).comp measurable_fst).prodMk measurable_snd
  exact (show Continuous fun q : C(X, ℝ) × X => q.1 q.2 from continuous_eval).measurable.comp h1

/-- **Joint measurability** of the Feller kernels in `(t, x)`. -/
theorem sgKernel_measurable_joint :
    Measurable fun p : ℝ≥0 × X => sgKernel hF p.1 p.2 := by
  refine measurable_of_integrals_param (κ := fun p : ℝ≥0 × X => sgKernel hF p.1 p.2) fun f => ?_
  simp_rw [integral_sgKernel]
  exact measurable_sgOp_joint hF f

/-- **The `MarkovProcess` semigroup data of a Feller triple** (sub-Markov case). -/
noncomputable def sgMarkovProcessData : MarkovProcessSemigroupData X :=
  (sgSemigroup hF).toMarkovProcessData (sgKernel_measurable_joint hF)

end Meas

end MarkovTriple.Stochastic.R28
