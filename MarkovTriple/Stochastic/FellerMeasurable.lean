import Mathlib
import MarkovTriple.Stochastic.FellerKernel
import MarkovTriple.Stochastic.MarkovProcessInterface

/-!
# Stochastic layer, part 17: joint measurability in time of the Feller kernels (round 17, `STATEMENTS_R17.md` (A))

Setting as in `FellerKernel.lean`: `X` compact metrizable Borel, `T : DiffusionTriple X` with finite `μ` of full
support, `hF : IsFeller T`.  The map `(t, x) ↦ κ_t(x, ·)` of exact Chapman-Kolmogorov kernels
(`fellerKernel hF`) is **jointly measurable**, hence the kernels give a `MarkovProcessSemigroupData`
(`fellerMarkovProcessData`) and, in the conservative case, a `MarkovProcessBridge`.

Proof (BGL Sect. 1.2-1.4: strong `L²` continuity of the semigroup and the kernel representation):
* `t ↦ P_t [f]` is continuous into `L²(μ)` (`continuous_semigroup_apply`);
* `{u : |u - [g]| ≤ r a.e.}` is closed in `L²` (`Lp` is an `OrderClosedTopology`);
* for continuous functions and full-support `μ`, `‖h - g‖_∞ ≤ r ⇔ |h - g| ≤ r` a.e.; so
  `{t : ‖fellerOp t f - g‖_∞ ≤ r}` is closed, `t ↦ fellerOp t f` is Borel into `C(X)` (separable metric), and evaluation
  `C(X) × X → ℝ` is continuous: `(t, x) ↦ (P_t f)(x)` is jointly measurable;
* the closed-set approximation of the Riesz measures (as in `measurable_of_integrals`, here with a general parameter
  space) turns this into joint measurability of the kernel.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

section Aux

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- Measurability of `y ↦ ∫ f dκ y` for all continuous `f` gives measurability of the measure-valued map `κ`
on an arbitrary measurable parameter space (generalisation of `measurable_of_integrals`). -/
lemma measurable_of_integrals_param {Y : Type*} [MeasurableSpace Y] {κ : Y → Measure X}
    [∀ y, IsFiniteMeasure (κ y)]
    (h : ∀ f : C(X, ℝ), Measurable fun y => ∫ z, f z ∂(κ y)) : Measurable κ := by
  have hclosed : ∀ K : Set X, IsClosed K → Measurable fun y => κ y K := by
    intro K hK
    let ap : ℕ → C(X, ℝ) := fun n =>
      ⟨fun z => ((hK.apprSeq n z : ℝ≥0) : ℝ),
        (NNReal.continuous_coe.comp (hK.apprSeq n).continuous)⟩
    have hlim : ∀ y, Tendsto (fun n => ∫ z, ap n z ∂(κ y)) atTop (𝓝 ((κ y).real K)) := by
      intro y
      have hb : ∀ n z, ‖ap n z‖ ≤ 1 := fun n z => by
        simp only [ap, ContinuousMap.coe_mk, Real.norm_eq_abs, NNReal.abs_eq]
        exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hK n z
      have := tendsto_integral_of_dominated_convergence (μ := κ y) (fun _ => (1 : ℝ))
        (F := fun n z => ap n z) (f := K.indicator (fun _ => (1 : ℝ)))
        (fun n => (ap n).continuous.aestronglyMeasurable)
        (integrable_const _)
        (fun n => Filter.Eventually.of_forall fun z => hb n z)
        (Filter.Eventually.of_forall fun z => by
          have key := NNReal.tendsto_coe.2
            (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hK) z)
          by_cases hz : z ∈ K
          · simpa [hz, ap] using key
          · simpa [hz, ap] using key)
      simpa [integral_indicator hK.measurableSet, Measure.real] using this
    have hm : Measurable fun y => (κ y).real K :=
      measurable_of_tendsto_metrizable (fun n => h (ap n)) (tendsto_pi_nhds.2 hlim)
    have : (fun y => κ y K) = fun y => ENNReal.ofReal ((κ y).real K) := by
      funext y
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    exact ENNReal.measurable_ofReal.comp hm
  refine Measurable.measure_of_isPiSystem (S := {s : Set X | IsClosed s}) ?_ isPiSystem_isClosed
    (fun s hs => hclosed s hs) (hclosed _ isClosed_univ)
  exact BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed

omit [T2Space X] [SecondCountableTopology X] in
/-- Order on classes of continuous functions (full support): `[h₁] ≤ [h₂] ⇔ h₁ ≤ h₂` everywhere. -/
lemma clsC_le_iff {μ : Measure X} [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] (h₁ h₂ : C(X, ℝ)) :
    clsC μ h₁ ≤ clsC μ h₂ ↔ ∀ x, h₁ x ≤ h₂ x := by
  constructor
  · intro h
    have h' : ∀ᵐ x ∂μ, 0 ≤ (h₂ - h₁) x := by
      filter_upwards [(Lp.coeFn_le _ _).2 h, coeFn_clsC (μ := μ) h₁, coeFn_clsC (μ := μ) h₂]
        with x hx e1 e2
      rw [e1, e2] at hx
      simpa using hx
    intro x
    have := cont_nonneg_of_ae h' x
    simpa using this
  · intro h
    refine (Lp.coeFn_le _ _).1 ?_
    filter_upwards [coeFn_clsC (μ := μ) h₁, coeFn_clsC (μ := μ) h₂] with x e1 e2
    rw [e1, e2]; exact h x

end Aux

section Meas

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {T : DiffusionTriple X} [IsFiniteMeasure T.μ]
  [T.μ.IsOpenPosMeasure] (hF : IsFeller T)
omit [T2Space X] [SecondCountableTopology X] in
/-- `{t : ‖P_t f - g‖_∞ ≤ r}` is closed: strong `L²` continuity of the semigroup and order-closedness of `L²`. -/
lemma isClosed_fellerOp_ball (f g : C(X, ℝ)) (r : ℝ) :
    IsClosed {t : ℝ≥0 | ∀ x, |fellerOp hF t f x - g x| ≤ r} := by
  let a : C(X, ℝ) := ⟨fun x => g x - r, g.continuous.sub continuous_const⟩
  let b : C(X, ℝ) := ⟨fun x => g x + r, g.continuous.add continuous_const⟩
  have hcont : Continuous fun t : ℝ≥0 => T.semigroup t (clsC T.μ f) :=
    T.continuous_semigroup_apply _
  have hset : {t : ℝ≥0 | ∀ x, |fellerOp hF t f x - g x| ≤ r} =
      (fun t => T.semigroup t (clsC T.μ f)) ⁻¹' ({u | clsC T.μ a ≤ u} ∩ {u | u ≤ clsC T.μ b}) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_inter_iff, fellerOp_cls hF,
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
theorem measurable_fellerOp_time (f : C(X, ℝ)) : Measurable fun t : ℝ≥0 => fellerOp hF t f := by
  have hball : ∀ (g : C(X, ℝ)) (r : ℝ), 0 ≤ r →
      MeasurableSet {t : ℝ≥0 | fellerOp hF t f ∈ Metric.closedBall g r} := by
    intro g r hr
    have := (isClosed_fellerOp_ball hF f g r).measurableSet
    convert this using 1
    ext t
    simp only [Set.mem_ofPred_eq, Metric.mem_closedBall, dist_eq_norm]
    rw [ContinuousMap.norm_le _ hr]
    simp [Real.norm_eq_abs]
  obtain ⟨g, hg⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  refine measurable_of_isOpen fun U hU => ?_
  have hU' : (fun t : ℝ≥0 => fellerOp hF t f) ⁻¹' U =
      ⋃ (p : ℕ × ℕ) (_ : Metric.closedBall (g p.1) (1 / ((p.2 : ℝ) + 1)) ⊆ U),
        {t : ℝ≥0 | fellerOp hF t f ∈ Metric.closedBall (g p.1) (1 / ((p.2 : ℝ) + 1))} := by
    ext t
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro ht
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 hU _ ht
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
      obtain ⟨n, hn⟩ := Metric.denseRange_iff.1 hg (fellerOp hF t f) (1 / ((k : ℝ) + 1))
        (by positivity)
      refine ⟨(n, k), fun y hy => hsub ?_, ?_⟩
      · rw [Metric.mem_ball]
        have h1 : dist y (g n) ≤ 1 / ((k : ℝ) + 1) := hy
        have h2 : dist (fellerOp hF t f) (g n) < 1 / ((k : ℝ) + 1) := hn
        have := dist_triangle y (g n) (fellerOp hF t f)
        rw [dist_comm (g n)] at this
        linarith
      · rw [Metric.mem_closedBall, dist_comm]
        exact (show dist (g n) (fellerOp hF t f) < 1 / ((k : ℝ) + 1) by
          rw [dist_comm]; exact hn).le
    · rintro ⟨p, hp, hmem⟩
      exact hp hmem
  rw [hU']
  exact MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun _ => hball _ _ (by positivity)

/-- `(t, x) ↦ (P_t f)(x)` is jointly measurable. -/
theorem measurable_fellerOp_joint (f : C(X, ℝ)) :
    Measurable fun p : ℝ≥0 × X => fellerOp hF p.1 f p.2 := by
  have h1 : Measurable fun p : ℝ≥0 × X => ((fellerOp hF p.1 f, p.2) : C(X, ℝ) × X) :=
    ((measurable_fellerOp_time hF f).comp measurable_fst).prodMk measurable_snd
  exact (show Continuous fun q : C(X, ℝ) × X => q.1 q.2 from continuous_eval).measurable.comp h1

/-- **Joint measurability** of the Feller kernels in `(t, x)`. -/
theorem fellerKernel_measurable_joint :
    Measurable fun p : ℝ≥0 × X => fellerKernel hF p.1 p.2 := by
  refine measurable_of_integrals_param (κ := fun p : ℝ≥0 × X => fellerKernel hF p.1 p.2) fun f => ?_
  simp_rw [integral_fellerKernel]
  exact measurable_fellerOp_joint hF f

/-- **The `MarkovProcess` semigroup data of a Feller triple** (sub-Markov case). -/
noncomputable def fellerMarkovProcessData : MarkovProcessSemigroupData X :=
  (fellerSemigroup hF).toMarkovProcessData (fellerKernel_measurable_joint hF)

/-- **A `MarkovProcessBridge` for every conservative Feller triple** on a compact metrizable space with
full-support `μ`: jointly measurable exact Chapman-Kolmogorov kernels representing `P_t`, `μ` invariant. -/
noncomputable def fellerMarkovProcessBridge (hcons : ∀ t, T.semigroup t T.one2 = T.one2) :
    MarkovProcessBridge T :=
  (fellerBridge hF hcons).toMarkovProcessBridge (fellerKernel_measurable_joint hF)

theorem fellerMarkovProcessBridge_kernel (hcons : ∀ t, T.semigroup t T.one2 = T.one2) :
    (fellerMarkovProcessBridge hF hcons).kernel = fellerKernel hF := rfl

end Meas

end MarkovTriple.Stochastic
