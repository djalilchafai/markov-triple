import Mathlib
import MarkovTriple.Stochastic.RieszFunctional

/-!
# Stochastic layer, part 8: kernels from a positive sub-Markov contraction (Riesz-Markov-Kakutani)

Classical statement used: BGL Proposition 1.2.3 (kernel representation: a Markov operator on a good
measure space is given by a probability kernel; its proof there uses `ν₁(A×B) = ∫ 1_A P(1_B) dμ` and the
measure decomposition theorem), here replaced, on a compact metrizable space and in the sub-Markov case, by
the Riesz-Markov-Kakutani representation theorem (Mathlib `RealRMK.integral_rieszMeasure`; the measure
decomposition theorem and "good measurable spaces" are discussed in BGL Sect. 1.1).  Statement: a positive linear contraction `P` of
`L²(μ)` with `P u ≤ 1` whenever `u ≤ 1` (sub-Markov) on a compact metrizable Borel space with a finite
measure `μ` is represented by a sub-Markov **kernel**: `P [f] = (x ↦ ∫ f dκ(x,·))` `μ`-a.e. for every
`f ∈ C(X)`.

Proof (standard, "regularisation of a positive operator"): fix a countable dense additive subgroup
`V ⊂ C(X)` containing `1`.  Off a `μ`-null Borel set `N` the representatives of `P v`, `v ∈ V`, are
additive, positive and bounded by `‖v‖` (countably many a.e. conditions), hence give a positive additive
functional on `V`; extend it (`exists_posFunctional`) to a positive linear functional on `C(X)` and
represent it by a measure (Riesz-Markov-Kakutani, `exists_measure_of_pos`).  Measurability of the
resulting family is checked on closed sets (π-system, `Measurable.measure_of_isPiSystem`), and the
a.e. identification for every `f ∈ C(X)` follows by `L²`-approximation along `V`.

* `exists_kernel_of_posContraction`: the statement.
-/

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

section Aux

variable {μ : Measure X} [IsFiniteMeasure μ]

/-- the `L²`-class of a continuous function -/
noncomputable abbrev clsC (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℝ)) : Lp ℝ 2 μ :=
  ContinuousMap.toLp 2 μ ℝ f

omit [T2Space X] [SecondCountableTopology X] in
lemma coeFn_clsC (f : C(X, ℝ)) : (clsC μ f : X → ℝ) =ᵐ[μ] f := ContinuousMap.coeFn_toLp _ _

/-- measurability of `x ↦ ∫ f dκ x` for all continuous `f` gives measurability of the measure-valued
map (on closed sets, then the π-system of closed sets). -/
lemma measurable_of_integrals {κ : X → Measure X} [∀ x, IsFiniteMeasure (κ x)]
    (h : ∀ f : C(X, ℝ), Measurable fun x => ∫ y, f y ∂(κ x)) : Measurable κ := by
  have hclosed : ∀ K : Set X, IsClosed K → Measurable fun x => κ x K := by
    intro K hK
    let ap : ℕ → C(X, ℝ) := fun n =>
      ⟨fun y => ((hK.apprSeq n y : ℝ≥0) : ℝ),
        (NNReal.continuous_coe.comp (hK.apprSeq n).continuous)⟩
    have hlim : ∀ x, Tendsto (fun n => ∫ y, ap n y ∂(κ x)) atTop (𝓝 ((κ x).real K)) := by
      intro x
      have hb : ∀ n y, ‖ap n y‖ ≤ 1 := fun n y => by
        simp only [ap, ContinuousMap.coe_mk, Real.norm_eq_abs, NNReal.abs_eq]
        exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hK n y
      have := tendsto_integral_of_dominated_convergence (μ := κ x) (fun _ => (1 : ℝ))
        (F := fun n y => ap n y) (f := K.indicator (fun _ => (1 : ℝ)))
        (fun n => (ap n).continuous.aestronglyMeasurable)
        (integrable_const _)
        (fun n => Filter.Eventually.of_forall fun y => hb n y)
        (Filter.Eventually.of_forall fun y => by
          have key := NNReal.tendsto_coe.2
            (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hK) y)
          by_cases hy : y ∈ K
          · simpa [hy, ap] using key
          · simpa [hy, ap] using key)
      simpa [integral_indicator hK.measurableSet, Measure.real] using this
    have hm : Measurable fun x => (κ x).real K :=
      measurable_of_tendsto_metrizable (fun n => h (ap n)) (tendsto_pi_nhds.2 hlim)
    have : (fun x => κ x K) = fun x => ENNReal.ofReal ((κ x).real K) := by
      funext x
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    exact ENNReal.measurable_ofReal.comp hm
  refine Measurable.measure_of_isPiSystem (S := {s : Set X | IsClosed s}) ?_ isPiSystem_isClosed
    (fun s hs => hclosed s hs) (hclosed _ isClosed_univ)
  exact BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed

end Aux

section Main

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- The composite `f ↦ P [f]`. -/
noncomputable def psiOf (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : C(X, ℝ) →L[ℝ] Lp ℝ 2 μ :=
  P.comp (ContinuousMap.toLp 2 μ ℝ)

variable {μ}

omit [T2Space X] [SecondCountableTopology X] in
lemma psiOf_nonneg {P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ}
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u) {f : C(X, ℝ)} (hf : 0 ≤ f) :
    ∀ᵐ x ∂μ, 0 ≤ (psiOf μ P f : X → ℝ) x := by
  have : 0 ≤ᵐ[μ] (clsC μ f : Lp ℝ 2 μ) := by
    filter_upwards [coeFn_clsC (μ := μ) f] with x hx
    rw [hx]; exact hf x
  exact hpos _ this

omit [T2Space X] [SecondCountableTopology X] in
lemma psiOf_abs_le {P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ}
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1) (f : C(X, ℝ)) :
    ∀ᵐ x ∂μ, |(psiOf μ P f : X → ℝ) x| ≤ ‖f‖ := by
  have h1 : (psiOf μ P (1 : C(X, ℝ)) : X → ℝ) ≤ᵐ[μ] 1 := by
    refine hle _ ?_
    filter_upwards [coeFn_clsC (μ := μ) (1 : C(X, ℝ))] with x hx
    exact hx.le
  have hc : 0 ≤ ‖f‖ := norm_nonneg f
  -- `c • 1 - f ≥ 0` and `c • 1 + f ≥ 0`
  have hA : 0 ≤ ‖f‖ • (1 : C(X, ℝ)) - f := by
    intro x
    have := ContinuousMap.norm_coe_le_norm f x
    rw [Real.norm_eq_abs] at this
    show (0 : ℝ) ≤ ‖f‖ • (1 : ℝ) - f x
    rw [smul_eq_mul, mul_one]
    linarith [le_abs_self (f x)]
  have hB : 0 ≤ ‖f‖ • (1 : C(X, ℝ)) + f := by
    intro x
    have := ContinuousMap.norm_coe_le_norm f x
    rw [Real.norm_eq_abs] at this
    show (0 : ℝ) ≤ ‖f‖ • (1 : ℝ) + f x
    rw [smul_eq_mul, mul_one]
    linarith [neg_abs_le (f x)]
  have hA' := psiOf_nonneg hpos hA
  have hB' := psiOf_nonneg hpos hB
  rw [map_sub, map_smul] at hA'
  rw [map_add, map_smul] at hB'
  filter_upwards [hA', hB', h1,
    Lp.coeFn_sub (‖f‖ • psiOf μ P (1 : C(X, ℝ))) (psiOf μ P f),
    Lp.coeFn_smul ‖f‖ (psiOf μ P (1 : C(X, ℝ))),
    Lp.coeFn_add (‖f‖ • psiOf μ P (1 : C(X, ℝ))) (psiOf μ P f)] with x hA hB h1 e1 e2 e3
  rw [e1, Pi.sub_apply, e2, Pi.smul_apply, smul_eq_mul] at hA
  rw [e3, Pi.add_apply, e2, Pi.smul_apply, smul_eq_mul] at hB
  have h1x : (psiOf μ P (1 : C(X, ℝ)) : X → ℝ) x ≤ 1 := h1
  have : ‖f‖ * (psiOf μ P (1 : C(X, ℝ)) : X → ℝ) x ≤ ‖f‖ := by
    calc _ ≤ ‖f‖ * 1 := by gcongr
      _ = ‖f‖ := mul_one _
  rw [abs_le]
  constructor <;> linarith

/-- **Kernel from a positive sub-Markov contraction** (Riesz-Markov-Kakutani; see the file header). -/
theorem exists_kernel_of_posContraction (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1) :
    ∃ κ : Kernel X X, (∀ x, κ x Set.univ ≤ 1) ∧
      ∀ f : C(X, ℝ), (P (clsC μ f) : X → ℝ) =ᵐ[μ] fun x => ∫ y, f y ∂(κ x) := by
  classical
  set Ψ := psiOf μ P with hΨ
  have hΨapp : ∀ f, Ψ f = P (clsC μ f) := fun f => rfl
  -- representatives
  let F : C(X, ℝ) → X → ℝ := fun f => (Lp.aestronglyMeasurable (Ψ f)).mk _
  have hFm : ∀ f, Measurable (F f) := fun f =>
    (Lp.aestronglyMeasurable (Ψ f)).stronglyMeasurable_mk.measurable
  have hFae : ∀ f, F f =ᵐ[μ] (Ψ f : X → ℝ) := fun f =>
    (Lp.aestronglyMeasurable (Ψ f)).ae_eq_mk.symm
  -- a countable dense additive subgroup `V ∋ 1`
  obtain ⟨D0, hD0c, hD0d⟩ := TopologicalSpace.exists_countable_dense C(X, ℝ)
  set S : Set C(X, ℝ) := insert 1 D0 with hS
  have hSc : S.Countable := hD0c.insert 1
  have : Countable S := hSc.to_subtype
  let V : Submodule ℤ C(X, ℝ) := Submodule.span ℤ (Set.range ((↑) : S → C(X, ℝ)))
  have hVS : S ⊆ (V : Set C(X, ℝ)) := fun a ha => Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  let Vg : AddSubgroup C(X, ℝ) := V.toAddSubgroup
  have hVdense : Dense (Vg : Set C(X, ℝ)) :=
    hD0d.mono (fun a ha => hVS (Set.mem_insert_of_mem _ ha))
  have h1V : (1 : C(X, ℝ)) ∈ Vg := hVS (Set.mem_insert _ _)
  have : Countable V := inferInstance
  have : Countable Vg := inferInstanceAs (Countable V)
  -- a.e. good conditions
  have hadd : ∀ v w : Vg, ∀ᵐ x ∂μ, F ((v : C(X, ℝ)) + (w : C(X, ℝ))) x = F v x + F w x := by
    intro v w
    filter_upwards [hFae ((v : C(X, ℝ)) + (w : C(X, ℝ))), hFae v, hFae w,
      Lp.coeFn_add (Ψ v) (Ψ w)] with x h1 h2 h3 h4
    rw [h1, map_add, h4, Pi.add_apply, h2, h3]
  have hbd : ∀ v : Vg, ∀ᵐ x ∂μ, |F v x| ≤ ‖(v : C(X, ℝ))‖ := by
    intro v
    filter_upwards [hFae v, psiOf_abs_le hpos hle (v : C(X, ℝ))] with x h1 h2
    rw [h1]; exact h2
  have hpv : ∀ v : Vg, 0 ≤ (v : C(X, ℝ)) → ∀ᵐ x ∂μ, 0 ≤ F v x := by
    intro v hv
    filter_upwards [hFae v, psiOf_nonneg hpos hv] with x h1 h2
    rw [h1]; exact h2
  have hgood : ∀ᵐ x ∂μ, (∀ v w : Vg, F ((v : C(X, ℝ)) + (w : C(X, ℝ))) x = F v x + F w x) ∧
      (∀ v : Vg, |F v x| ≤ ‖(v : C(X, ℝ))‖) ∧ (∀ v : Vg, 0 ≤ (v : C(X, ℝ)) → 0 ≤ F v x) := by
    have e1 : ∀ᵐ x ∂μ, ∀ p : Vg × Vg, F ((p.1 : C(X, ℝ)) + (p.2 : C(X, ℝ))) x = F p.1 x + F p.2 x :=
      ae_all_iff.2 fun p => hadd p.1 p.2
    have e2 : ∀ᵐ x ∂μ, ∀ v : Vg, |F v x| ≤ ‖(v : C(X, ℝ))‖ := ae_all_iff.2 hbd
    have e3 : ∀ᵐ x ∂μ, ∀ v : Vg, 0 ≤ (v : C(X, ℝ)) → 0 ≤ F v x :=
      ae_all_iff.2 fun v => by
        by_cases hv : 0 ≤ (v : C(X, ℝ))
        · filter_upwards [hpv v hv] with x hx _ using hx
        · exact Filter.Eventually.of_forall fun x h => absurd h hv
    filter_upwards [e1, e2, e3] with x a b c
    exact ⟨fun v w => a (v, w), b, c⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodN : ∀ x, x ∉ N → (∀ v w : Vg, F ((v : C(X, ℝ)) + (w : C(X, ℝ))) x = F v x + F w x) ∧
      (∀ v : Vg, |F v x| ≤ ‖(v : C(X, ℝ))‖) ∧ (∀ v : Vg, 0 ≤ (v : C(X, ℝ)) → 0 ≤ F v x) := by
    intro x hx
    by_contra hcon
    exact hx (hNsub hcon)
  -- pointwise positive functionals
  have hL : ∀ x : X, ∃ L : C(X, ℝ) →L[ℝ] ℝ, x ∉ N → (∀ v : Vg, L v = F v x) ∧
      (∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) := by
    intro x
    by_cases hx : x ∈ N
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨hA, hB, hC⟩ := hgoodN x hx
      let Λ : Vg →+ ℝ := AddMonoidHom.mk' (fun v : Vg => F v x) (fun v w => hA v w)
      obtain ⟨L, hL1, hL2, -⟩ := exists_posFunctional Vg hVdense h1V Λ (fun v => hB v)
        (fun v hv => hC v hv)
      exact ⟨L, fun _ => ⟨hL1, hL2⟩⟩
  choose Lx hLx using hL
  -- measures
  have hM : ∀ x : X, ∃ m : Measure X, IsFiniteMeasure m ∧
      (x ∉ N → ∀ f : C(X, ℝ), ∫ y, f y ∂m = Lx x f) ∧ (x ∈ N → m = 0) := by
    intro x
    by_cases hx : x ∈ N
    · exact ⟨0, inferInstance, fun h => absurd hx h, fun _ => rfl⟩
    · obtain ⟨m, hm, hint⟩ := exists_measure_of_pos (Lx x) ((hLx x hx).2)
      exact ⟨m, hm, fun _ => hint, fun h => absurd h hx⟩
  choose κ' hκfin hκint hκzero using hM
  have : ∀ x, IsFiniteMeasure (κ' x) := hκfin
  -- sequences in `Vg` converging to `f`
  have hseq : ∀ f : C(X, ℝ), ∃ v : ℕ → Vg, Tendsto (fun n => (v n : C(X, ℝ))) atTop (𝓝 f) := by
    intro f
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hVdense f)
    exact ⟨fun n => ⟨u n, hu n⟩, hlim⟩
  -- measurability of the family
  have hmeas_int : ∀ f : C(X, ℝ), Measurable fun x => ∫ y, f y ∂(κ' x) := by
    intro f
    obtain ⟨v, hv⟩ := hseq f
    have hg : ∀ n, Measurable fun x => if x ∈ N then (0 : ℝ) else F (v n) x := fun n =>
      Measurable.ite hNm measurable_const (hFm _)
    refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun x => ?_)
    by_cases hx : x ∈ N
    · simp only [hx, ite_true, hκzero x hx, integral_zero_measure]
      exact tendsto_const_nhds
    · simp only [hx, ite_false, hκint x hx f]
      have h2 : Tendsto (fun n => Lx x (v n : C(X, ℝ))) atTop (𝓝 (Lx x f)) :=
        ((Lx x).continuous.tendsto f).comp hv
      refine h2.congr fun n => ?_
      exact (hLx x hx).1 (v n)
  have hκmeas : Measurable κ' := measurable_of_integrals hmeas_int
  refine ⟨{ toFun := κ', measurable' := hκmeas }, ?_, ?_⟩
  · intro x
    show κ' x Set.univ ≤ 1
    by_cases hx : x ∈ N
    · rw [hκzero x hx]; simp
    · have h1 := hκint x hx 1
      have h2 : Lx x (1 : C(X, ℝ)) = F (1 : C(X, ℝ)) x := (hLx x hx).1 ⟨1, h1V⟩
      have h3 : |F (1 : C(X, ℝ)) x| ≤ ‖(1 : C(X, ℝ))‖ := (hgoodN x hx).2.1 ⟨1, h1V⟩
      have h4 : (κ' x).real Set.univ ≤ 1 := by
        have : (κ' x).real Set.univ = Lx x (1 : C(X, ℝ)) := by
          rw [← h1]; simp
        rw [this, h2]
        exact (le_abs_self _).trans (h3.trans norm_one_le_one)
      calc κ' x Set.univ = ENNReal.ofReal ((κ' x).real Set.univ) := by
            rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h4
        _ = 1 := ENNReal.ofReal_one
  · intro f
    obtain ⟨v, hv⟩ := hseq f
    have hT : Tendsto (fun n => Ψ (v n : C(X, ℝ))) atTop (𝓝 (Ψ f)) :=
      (Ψ.continuous.tendsto f).comp hv
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hT).exists_seq_tendsto_ae
    have hFall : ∀ᵐ x ∂μ, ∀ n, F (v n : C(X, ℝ)) x = Ψ (v n : C(X, ℝ)) x :=
      ae_all_iff.2 fun n => hFae _
    have hNc : ∀ᵐ x ∂μ, x ∉ N := by
      rw [ae_iff]; simpa using hN0
    filter_upwards [hae, hFall, hNc] with x h1 h2 h3
    show (Ψ f : X → ℝ) x = ∫ y, f y ∂(κ' x)
    rw [hκint x h3 f]
    have h4 : Tendsto (fun i => Lx x (v (ns i) : C(X, ℝ))) atTop (𝓝 (Lx x f)) :=
      ((Lx x).continuous.tendsto f).comp (hv.comp hns.tendsto_atTop)
    have h5 : Tendsto (fun i => (Ψ (v (ns i) : C(X, ℝ)) : X → ℝ) x) atTop (𝓝 (Lx x f)) :=
      h4.congr fun i => by rw [(hLx x h3).1, h2]
    exact tendsto_nhds_unique h1 h5

end Main

end MarkovTriple.Stochastic
