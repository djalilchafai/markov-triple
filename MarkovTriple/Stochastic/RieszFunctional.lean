import Mathlib

/-!
# Stochastic layer, part 7: positive functionals on `C(X)` from a dense additive subgroup; Riesz measure

Two classical functional-analytic steps used to build kernels from a positive semigroup
(`RieszKernel.lean`):

* `exists_extend_addSubgroup`: an additive functional `Λ` on a **dense additive subgroup** `V` of a normed real
  vector space with `|Λ v| ≤ ‖v‖` extends to a continuous **real-linear** functional with the same bound
  (uniformly continuous extension from a dense subgroup, then additive + continuous ⇒ `ℝ`-linear:
  Mathlib `ContinuousLinearMap.extend` over `ℤ` and `AddMonoidHom.toRealLinearMap`);
* `exists_posFunctional`: if moreover `1 ∈ V` and `Λ ≥ 0` on nonnegative elements of `V ⊂ C(X)`
  (`X` compact), the extension is positive;
* `exists_measure_of_pos`: **Riesz-Markov-Kakutani** (Mathlib `RealRMK.integral_rieszMeasure`): a positive
  linear functional on `C(X)` (`X` compact Hausdorff, Borel) is integration against a finite Borel measure.
-/

open MeasureTheory Topology

namespace MarkovTriple.Stochastic

theorem exists_extend_addSubgroup {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : AddSubgroup E) (hV : Dense (V : Set E)) (Λ : V →+ ℝ)
    (hΛ : ∀ v : V, |Λ v| ≤ ‖(v : E)‖) :
    ∃ L : E →L[ℝ] ℝ, (∀ v : V, L v = Λ v) ∧ ∀ e, |L e| ≤ ‖e‖ := by
  have hc : Continuous Λ := AddMonoidHomClass.continuous_of_bound Λ 1 (fun v => by
    simpa using hΛ v)
  let f : V →L[ℤ] ℝ := ⟨Λ.toIntLinearMap, hc⟩
  let e : V →L[ℤ] E := ⟨(AddSubgroup.subtype V).toIntLinearMap, continuous_subtype_val⟩
  have hd : DenseRange e := hV.denseRange_val
  have hu : IsUniformInducing e := isUniformEmbedding_subtype_val.isUniformInducing
  let g : E →L[ℤ] ℝ := f.extend e
  have hg : ∀ v : V, g v = Λ v := fun v => by
    have := ContinuousLinearMap.extend_eq f hd hu v
    exact this
  let L : E →L[ℝ] ℝ := AddMonoidHom.toRealLinearMap (g : E →+ ℝ) g.continuous
  have hL : ∀ x, L x = g x := fun x => rfl
  refine ⟨L, fun v => by rw [hL, hg], ?_⟩
  have hcl : IsClosed {x : E | |L x| ≤ ‖x‖} :=
    isClosed_le (continuous_abs.comp L.continuous) continuous_norm
  have : (V : Set E) ⊆ {x : E | |L x| ≤ ‖x‖} := fun v hv => by
    show |L v| ≤ ‖v‖
    have := hΛ ⟨v, hv⟩
    rw [hL]
    have h2 := hg ⟨v, hv⟩
    simp only at h2
    rw [h2]; exact this
  have := closure_minimal this hcl
  rw [hV.closure_eq] at this
  exact fun x => this (Set.mem_univ x)

section Positive

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

lemma norm_one_le_one : ‖(1 : C(X, ℝ))‖ ≤ 1 :=
  (ContinuousMap.norm_le _ zero_le_one).2 fun x => by simp

/-- **Positive extension** (classical: extension by density, positivity via the unit). -/
theorem exists_posFunctional (V : AddSubgroup C(X, ℝ)) (hV : Dense (V : Set C(X, ℝ)))
    (h1 : (1 : C(X, ℝ)) ∈ V) (Λ : V →+ ℝ) (hΛ : ∀ v : V, |Λ v| ≤ ‖(v : C(X, ℝ))‖)
    (hpos : ∀ v : V, 0 ≤ (v : C(X, ℝ)) → 0 ≤ Λ v) :
    ∃ L : C(X, ℝ) →L[ℝ] ℝ, (∀ v : V, L v = Λ v) ∧ (∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) ∧
      ∀ f, |L f| ≤ ‖f‖ := by
  obtain ⟨L, hLV, hLb⟩ := exists_extend_addSubgroup V hV Λ hΛ
  refine ⟨L, hLV, ?_, hLb⟩
  intro f hf
  by_contra hneg
  replace hneg := not_le.1 hneg
  obtain ⟨m, hm⟩ := exists_nat_gt (2 / (-L f))
  have hm0 : (0 : ℝ) < m := lt_trans (div_pos two_pos (neg_pos.2 hneg)) hm
  -- approximate `m • f` by an element of `V`
  obtain ⟨v, hv, hvV⟩ := Metric.dense_iff.1 hV ((m : ℝ) • f) 1 one_pos
  rw [Metric.mem_ball, dist_eq_norm] at hv
  have hvmem : v ∈ V := hvV
  -- `v + 1 ≥ 0`
  have hv1 : 0 ≤ ((⟨v + 1, V.add_mem hvmem h1⟩ : V) : C(X, ℝ)) := by
    intro x
    have h1 := (ContinuousMap.norm_coe_le_norm (v - (m : ℝ) • f) x)
    have h2 : (v - (m : ℝ) • f) x ≥ -1 := by
      have := (abs_le.1 (by simpa [Real.norm_eq_abs] using h1.trans hv.le)).1
      simpa using this
    have h3 : 0 ≤ (m : ℝ) * f x := mul_nonneg hm0.le (hf x)
    show 0 ≤ (v + 1 : C(X, ℝ)) x
    simp only [ContinuousMap.add_apply, ContinuousMap.one_apply, ContinuousMap.sub_apply,
      ContinuousMap.smul_apply, smul_eq_mul] at h2 ⊢
    linarith
  have hnn : 0 ≤ Λ ⟨v + 1, V.add_mem hvmem h1⟩ := hpos _ hv1
  have hadd : Λ ⟨v + 1, V.add_mem hvmem h1⟩ = Λ ⟨v, hvmem⟩ + Λ ⟨1, h1⟩ := by
    rw [← map_add]; rfl
  have hΛ1 : Λ ⟨1, h1⟩ ≤ 1 := (le_abs_self _).trans ((hΛ ⟨1, h1⟩).trans norm_one_le_one)
  have hLv : L v = Λ ⟨v, hvmem⟩ := hLV ⟨v, hvmem⟩
  have hdiff : |L ((m : ℝ) • f) - L v| ≤ ‖(m : ℝ) • f - v‖ := by
    rw [← map_sub]; exact hLb _
  have hnormeq : ‖(m : ℝ) • f - v‖ < 1 := by rw [norm_sub_rev]; exact hv
  have hlow : -2 < (m : ℝ) * L f := by
    have := (abs_lt.1 (lt_of_le_of_lt hdiff hnormeq)).1
    rw [map_smul, smul_eq_mul] at this
    linarith
  have : (m : ℝ) * L f < -2 := by
    have h4 := (div_lt_iff₀ (neg_pos.2 hneg)).1 hm
    linarith
  linarith

end Positive

section Riesz

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
  [BorelSpace X]

/-- The positive linear functional on `C_c(X, ℝ)` attached to a positive `L : C(X,ℝ) →L[ℝ] ℝ`. -/
noncomputable def posMapOf (L : C(X, ℝ) →L[ℝ] ℝ) (hpos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) :
    CompactlySupportedContinuousMap X ℝ →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun g => L g.toContinuousMap
      map_add' := fun g h => by
        rw [← map_add]; rfl
      map_smul' := fun c g => by
        rw [← map_smul]; rfl }
    (fun g hg => hpos _ (fun x => hg x))

/-- **Riesz-Markov-Kakutani** on a compact Hausdorff Borel space: a positive linear functional on
`C(X, ℝ)` is integration against a finite Borel measure. -/
theorem exists_measure_of_pos (L : C(X, ℝ) →L[ℝ] ℝ) (hpos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ L f) :
    ∃ m : Measure X, IsFiniteMeasure m ∧ ∀ f : C(X, ℝ), ∫ x, f x ∂m = L f := by
  refine ⟨RealRMK.rieszMeasure (posMapOf L hpos), inferInstance, fun f => ?_⟩
  have := RealRMK.integral_rieszMeasure (posMapOf L hpos) (CompactlySupportedContinuousMap.continuousMapEquiv f)
  exact this

end Riesz

end MarkovTriple.Stochastic
