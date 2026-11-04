import Mathlib
import MarkovTriple.Stochastic.R23.Exhaustion

/-!
# Round 23 (S), part 2: sub-invariance `μ.bind κ ≤ μ` for infinite `μ`

For `P` symmetric, positivity preserving, `L^∞`-contractive on `L²(μ)` (`μ` finite on compacts) the kernel of
`exists_kernel_of_posContraction_locFinite` satisfies `μ.bind κ ≤ μ`.  Route: for `0 ≤ u ∈ L² ∩ L¹`,
`∫⁻ P u ≤ ∫ u` (`∫_{K_n} P u = ⟨P u, 1_{K_n}⟩ = ⟨u, P 1_{K_n}⟩ ≤ ∫ u`, monotone limit), then compact sets by
Urysohn functions and outer regularity of `μ`, then all measurable sets by inner regularity of `μ.bind κ`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty

namespace MarkovTriple.Stochastic.R23

open MarkovTriple.Stochastic MarkovTriple.Stochastic.R22

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

attribute [local instance] R22.ncMeas R22.ncBorel

omit [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [BorelSpace X] in
lemma l2_inner_eq {μ : Measure X} (a b : Lp ℝ 2 μ) : inner ℝ a b = ∫ x, a x * b x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [mul_comm])

variable {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- **Mass bound on compacts and `lintegral`**: `∫⁻ P u ≤ ∫ u` for `0 ≤ u ∈ L² ∩ L¹`
(`P` symmetric, positivity preserving, sub-Markov). -/
theorem lintegral_P_le (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1)
    (hsa : IsSelfAdjoint P) (u : Lp ℝ 2 μ) (hu : 0 ≤ᵐ[μ] u) (hint : Integrable (u : X → ℝ) μ) :
    ∫⁻ x, ENNReal.ofReal ((P u : X → ℝ) x) ∂μ ≤ ∫⁻ x, ENNReal.ofReal ((u : X → ℝ) x) ∂μ := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  have hPu0 := hpos u hu
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa)
  set g : X → ℝ≥0∞ := fun x => ENNReal.ofReal ((P u : X → ℝ) x) with hg
  have hgm : AEMeasurable g μ :=
    (Lp.aestronglyMeasurable (P u)).aemeasurable.ennreal_ofReal
  have hsup : ∀ x, g x = ⨆ n, (K n).indicator g x := by
    intro x
    apply le_antisymm
    · have hx : x ∈ ⋃ n, K n := by rw [K.iUnion_eq]; trivial
      obtain ⟨N, hN⟩ := Set.mem_iUnion.1 hx
      refine le_trans (le_of_eq ?_) (le_iSup _ N)
      simp [hN]
    · exact iSup_le fun n => Set.indicator_le_self _ _ x
  have hmono : ∀ x, Monotone fun n => (K n).indicator g x := by
    intro x m n hmn
    by_cases hx : x ∈ K m
    · have : x ∈ K n := K.subset hmn hx
      simp [hx, this]
    · simp [hx]
  calc ∫⁻ x, g x ∂μ = ∫⁻ x, ⨆ n, (K n).indicator g x ∂μ := lintegral_congr hsup
    _ = ⨆ n, ∫⁻ x, (K n).indicator g x ∂μ :=
        lintegral_iSup' (fun n => hgm.indicator (measurableSet_K K n))
          (Filter.Eventually.of_forall hmono)
    _ ≤ ∫⁻ x, ENNReal.ofReal ((u : X → ℝ) x) ∂μ := by
        refine iSup_le fun n => ?_
        rw [lintegral_indicator (measurableSet_K K n)]
        have hfin : IsFiniteMeasure (μ.restrict (K n)) :=
          ⟨by rw [Measure.restrict_apply_univ]; exact (K.isCompact n).measure_lt_top⟩
        have hiPu : Integrable (fun x => (P u : X → ℝ) x) (μ.restrict (K n)) :=
          ((Lp.memLp (P u)).restrict (K n)).integrable (by norm_num)
        have hnn : 0 ≤ᵐ[μ.restrict (K n)] fun x => (P u : X → ℝ) x := ae_restrict_of_ae hPu0
        have h1 : ∫⁻ x in K n, g x ∂μ = ENNReal.ofReal (∫ x in K n, (P u : X → ℝ) x ∂μ) :=
          (ofReal_integral_eq_lintegral_ofReal hiPu hnn).symm
        have h2 : ∫ x in K n, (P u : X → ℝ) x ∂μ = inner ℝ (tr μ K n 1) (P u) := by
          rw [l2_inner_eq, ← integral_indicator (measurableSet_K K n)]
          refine integral_congr_ae ?_
          filter_upwards [coeFn_tr μ K n 1] with x hx
          rw [hx]
          by_cases hxK : x ∈ K n <;> simp [hxK]
        have h3 : inner ℝ (tr μ K n 1) (P u) = inner ℝ (P (tr μ K n 1)) u :=
          (hsym (tr μ K n 1) u).symm
        have hi1 : Integrable (fun x => (P (tr μ K n 1) : X → ℝ) x * (u : X → ℝ) x) μ := by
          have := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) u (P (tr μ K n 1))
          refine this.congr (Filter.Eventually.of_forall fun x => ?_)
          simp [mul_comm]
        have h4 : ∫ x, (P (tr μ K n 1) : X → ℝ) x * (u : X → ℝ) x ∂μ ≤ ∫ x, (u : X → ℝ) x ∂μ := by
          refine integral_mono_ae hi1 hint ?_
          filter_upwards [hu, hle _ (tr_one_le μ K n)] with x h1 h2
          have h1' : 0 ≤ (u : X → ℝ) x := h1
          calc (P (tr μ K n 1) : X → ℝ) x * (u : X → ℝ) x ≤ 1 * (u : X → ℝ) x :=
                mul_le_mul_of_nonneg_right h2 h1'
            _ = (u : X → ℝ) x := one_mul _
        rw [h1, h2, h3, l2_inner_eq]
        calc ENNReal.ofReal (∫ x, (P (tr μ K n 1) : X → ℝ) x * (u : X → ℝ) x ∂μ)
            ≤ ENNReal.ofReal (∫ x, (u : X → ℝ) x ∂μ) := ENNReal.ofReal_le_ofReal h4
          _ = ∫⁻ x, ENNReal.ofReal ((u : X → ℝ) x) ∂μ :=
              ofReal_integral_eq_lintegral_ofReal hint hu

/-- compact sets suffice for `ν ≤ μ` (inner regularity of `ν`). -/
lemma le_of_compact (ν : Measure X) (h : ∀ K : Set X, IsCompact K → ν K ≤ μ K) : ν ≤ μ := by
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => (h K hK).trans_lt hK.measure_lt_top⟩
  refine Measure.le_iff.2 fun A hA => ?_
  rw [hA.measure_eq_iSup_isCompact]
  exact iSup₂_le fun K hKA => iSup_le fun hK => (h K hK).trans (measure_mono hKA)

/-- **Sub-invariance of the kernel** representing a symmetric positive sub-Markov `P`. -/
theorem bind_le_of_rep (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1)
    (hsa : IsSelfAdjoint P) (κ : Kernel X X) (hsub : ∀ x, κ x Set.univ ≤ 1)
    (hrep : ∀ (f : C₀(X, ℝ)) (u : Lp ℝ 2 μ), (u : X → ℝ) =ᵐ[μ] f →
        (P u : X → ℝ) =ᵐ[μ] fun x => ∫ y, f y ∂(κ x)) :
    μ.bind κ ≤ μ := by
  refine le_of_compact _ fun Kc hKc => ?_
  rw [IsCompact.measure_eq_iInf_isOpen (μ := μ) hKc]
  refine le_iInf fun U => le_iInf fun hKU => le_iInf fun hU => ?_
  obtain ⟨f, hf1, hf0, hfc, hfI⟩ := exists_continuous_one_zero_of_isCompact hKc hU.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 hKU)
  have hf0' : ∀ x, 0 ≤ f x := fun x => (hfI x).1
  have hf1' : ∀ x, f x ≤ 1 := fun x => (hfI x).2
  let f₀ : C₀(X, ℝ) := ⟨f, hfc.is_zero_at_infty⟩
  have hfL : MemLp f 2 μ := f.continuous.memLp_of_hasCompactSupport hfc
  have hfi : Integrable f μ := f.continuous.integrable_of_hasCompactSupport hfc
  let u : Lp ℝ 2 μ := hfL.toLp f
  have hu : (u : X → ℝ) =ᵐ[μ] f₀ := hfL.coeFn_toLp
  have hu0 : 0 ≤ᵐ[μ] u := by
    filter_upwards [hfL.coeFn_toLp] with x hx
    rw [hx]; exact hf0' x
  have hint : Integrable (u : X → ℝ) μ := hfi.congr hfL.coeFn_toLp.symm
  have hK : MeasurableSet Kc := hKc.isClosed.measurableSet
  have hpt : ∀ x, κ x Kc ≤ ENNReal.ofReal (∫ y, f y ∂(κ x)) := by
    intro x
    have : IsFiniteMeasure (κ x) := ⟨lt_of_le_of_lt (hsub x) ENNReal.one_lt_top⟩
    have hi : Integrable f (κ x) := f.continuous.integrable_of_hasCompactSupport hfc
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hf0'),
      ← lintegral_indicator_one hK]
    refine lintegral_mono fun y => ?_
    by_cases hy : y ∈ Kc
    · simp [hy, hf1 hy]
    · simp [hy]
  calc (μ.bind κ) Kc = ∫⁻ x, κ x Kc ∂μ := Measure.bind_apply hK κ.aemeasurable
    _ ≤ ∫⁻ x, ENNReal.ofReal (∫ y, f y ∂(κ x)) ∂μ := lintegral_mono hpt
    _ = ∫⁻ x, ENNReal.ofReal ((P u : X → ℝ) x) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hrep f₀ u hu] with x hx
        rw [hx]
        rfl
    _ ≤ ∫⁻ x, ENNReal.ofReal ((u : X → ℝ) x) ∂μ := lintegral_P_le P hpos hle hsa u hu0 hint
    _ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hfL.coeFn_toLp] with x hx
        rw [hx]
    _ ≤ ∫⁻ x, U.indicator 1 x ∂μ := by
        refine lintegral_mono fun x => ?_
        by_cases hx : x ∈ U
        · simpa [hx] using ENNReal.ofReal_le_ofReal (hf1' x)
        · have : f x = 0 := hf0 (by simpa using hx)
          simp [hx, this]
    _ = μ U := lintegral_indicator_one hU.measurableSet

/-- **S1 with sub-invariance**: kernel representation for infinite `μ` (finite on compacts). -/
theorem exists_kernel_of_posContraction_locFinite_subInv (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1)
    (hsa : IsSelfAdjoint P) :
    ∃ κ : Kernel X X, (∀ x, κ x Set.univ ≤ 1) ∧ μ.bind κ ≤ μ ∧
      ∀ (f : C₀(X, ℝ)) (u : Lp ℝ 2 μ), (u : X → ℝ) =ᵐ[μ] f →
        (P u : X → ℝ) =ᵐ[μ] fun x => ∫ y, f y ∂(κ x) := by
  obtain ⟨κ, hsub, hrep⟩ := exists_kernel_of_posContraction_locFinite P hpos hle
  exact ⟨κ, hsub, bind_le_of_rep P hpos hle hsa κ hsub hrep, hrep⟩

end MarkovTriple.Stochastic.R23
