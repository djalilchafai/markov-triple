import Mathlib
import MarkovTriple.Stochastic.R23.AEKernel
import MarkovTriple.Stochastic.R22.NonCompact
import MarkovTriple.Stochastic.RepExtend

/-!
# Round 23 (S), part 1: the monotone-exhaustion limit `F f = lim_n P(1_{K_n} f)`

`X` locally compact, `T2`, second countable, `μ` finite on compacts (possibly infinite), `K_n` a compact
exhaustion (`K_n ⊆ int K_{n+1}`).  For `P` positivity preserving and `L^∞`-contractive on `L²(μ)` and
`f ∈ C(X⁺)` (`X⁺` the one-point compactification), `P(1_{K_n} f|_X)` converges `μ`-a.e. (monotone and
bounded for `f ≥ 0`); the limit `F f` is an a.e.-linear positive family with `F 1 ≤ 1`.
See `STATEMENTS_R23_S.md`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty

namespace MarkovTriple.Stochastic.R23

open MarkovTriple.Stochastic MarkovTriple.Stochastic.R22

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

attribute [local instance] R22.ncMeas R22.ncBorel

section Trunc

variable (μ : Measure X) [IsFiniteMeasureOnCompacts μ] (K : CompactExhaustion X)

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma measurableSet_K (n : ℕ) : MeasurableSet (K n) := (K.isCompact n).isClosed.measurableSet

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma trunc_memLp (n : ℕ) (f : C(OnePoint X, ℝ)) :
    MemLp ((K n).indicator (fun x : X => f (x : OnePoint X))) 2 μ := by
  rw [memLp_indicator_iff_restrict (measurableSet_K K n)]
  have : IsFiniteMeasure (μ.restrict (K n)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (K.isCompact n).measure_lt_top⟩
  exact MemLp.of_bound (f.continuous.comp OnePoint.continuous_coe).aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f (x : OnePoint X))

/-- the `L²`-class of `1_{K_n} f|_X`. -/
noncomputable def tr (n : ℕ) (f : C(OnePoint X, ℝ)) : Lp ℝ 2 μ := (trunc_memLp μ K n f).toLp _

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma coeFn_tr (n : ℕ) (f : C(OnePoint X, ℝ)) :
    (tr μ K n f : X → ℝ) =ᵐ[μ] (K n).indicator (fun x : X => f (x : OnePoint X)) :=
  MemLp.coeFn_toLp _

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma tr_add (n : ℕ) (f g : C(OnePoint X, ℝ)) : tr μ K n (f + g) = tr μ K n f + tr μ K n g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_tr μ K n (f + g), coeFn_tr μ K n f, coeFn_tr μ K n g,
    Lp.coeFn_add (tr μ K n f) (tr μ K n g)] with x h1 h2 h3 h4
  rw [h4, Pi.add_apply, h2, h3, h1]
  by_cases hx : x ∈ K n <;> simp [hx]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma tr_smul (n : ℕ) (c : ℝ) (f : C(OnePoint X, ℝ)) : tr μ K n (c • f) = c • tr μ K n f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_tr μ K n (c • f), coeFn_tr μ K n f,
    Lp.coeFn_smul c (tr μ K n f)] with x h1 h2 h4
  rw [h4, Pi.smul_apply, h2, h1]
  by_cases hx : x ∈ K n <;> simp [hx]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma tr_nonneg (n : ℕ) {f : C(OnePoint X, ℝ)} (hf : 0 ≤ f) : 0 ≤ᵐ[μ] (tr μ K n f : X → ℝ) := by
  filter_upwards [coeFn_tr μ K n f] with x h1
  rw [h1]
  by_cases hx : x ∈ K n
  · simpa [hx] using hf (x : OnePoint X)
  · simp [hx]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma tr_le_succ (n : ℕ) {f : C(OnePoint X, ℝ)} (hf : 0 ≤ f) :
    (tr μ K n f : X → ℝ) ≤ᵐ[μ] (tr μ K (n + 1) f : X → ℝ) := by
  filter_upwards [coeFn_tr μ K n f, coeFn_tr μ K (n + 1) f] with x h1 h2
  rw [h1, h2]
  by_cases hx : x ∈ K n
  · have : x ∈ K (n + 1) := K.subset (Nat.le_succ n) hx
    simp [hx, this]
  · by_cases hx' : x ∈ K (n + 1)
    · simpa [hx, hx'] using hf (x : OnePoint X)
    · simp [hx, hx']

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma tr_one_le (n : ℕ) : (tr μ K n 1 : X → ℝ) ≤ᵐ[μ] 1 := by
  filter_upwards [coeFn_tr μ K n 1] with x h1
  rw [h1]
  by_cases hx : x ∈ K n <;> simp [hx]

end Trunc


section Op

variable {μ : Measure X} [IsFiniteMeasureOnCompacts μ] (K : CompactExhaustion X)
  (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)

/-- a measurable representative of `P(1_{K_n} f|_X)`. -/
noncomputable def rr (n : ℕ) (f : C(OnePoint X, ℝ)) : X → ℝ :=
  (Lp.aestronglyMeasurable (P (tr μ K n f))).mk _

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma rr_meas (n : ℕ) (f : C(OnePoint X, ℝ)) : Measurable (rr K P n f) :=
  (Lp.aestronglyMeasurable _).stronglyMeasurable_mk.measurable

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma rr_ae (n : ℕ) (f : C(OnePoint X, ℝ)) : (P (tr μ K n f) : X → ℝ) =ᵐ[μ] rr K P n f :=
  (Lp.aestronglyMeasurable _).ae_eq_mk

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma rr_add (n : ℕ) (f g : C(OnePoint X, ℝ)) :
    rr K P n (f + g) =ᵐ[μ] rr K P n f + rr K P n g := by
  filter_upwards [rr_ae K P n (f + g), rr_ae K P n f, rr_ae K P n g,
    Lp.coeFn_add (P (tr μ K n f)) (P (tr μ K n g))] with x h1 h2 h3 h4
  have e : P (tr μ K n (f + g)) = P (tr μ K n f) + P (tr μ K n g) := by rw [tr_add, map_add]
  have h5 : (P (tr μ K n (f + g)) : X → ℝ) x
      = (P (tr μ K n f) : X → ℝ) x + (P (tr μ K n g) : X → ℝ) x := by rw [e]; exact h4
  rw [Pi.add_apply, ← h2, ← h3, ← h5, h1]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma rr_smul (n : ℕ) (c : ℝ) (f : C(OnePoint X, ℝ)) :
    rr K P n (c • f) =ᵐ[μ] c • rr K P n f := by
  filter_upwards [rr_ae K P n (c • f), rr_ae K P n f,
    Lp.coeFn_smul c (P (tr μ K n f))] with x h1 h2 h4
  have e : P (tr μ K n (c • f)) = c • P (tr μ K n f) := by rw [tr_smul, map_smul]
  have h5 : (P (tr μ K n (c • f)) : X → ℝ) x = c • (P (tr μ K n f) : X → ℝ) x := by
    rw [e]; exact h4
  rw [Pi.smul_apply, ← h2, ← h5, h1]

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma rr_nonneg (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u) (n : ℕ)
    {f : C(OnePoint X, ℝ)} (hf : 0 ≤ f) : 0 ≤ᵐ[μ] rr K P n f := by
  filter_upwards [hpos _ (tr_nonneg μ K n hf), rr_ae K P n f] with x h1 h2
  rw [← h2]; exact h1

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma rr_mono (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u) (n : ℕ)
    {f : C(OnePoint X, ℝ)} (hf : 0 ≤ f) : rr K P n f ≤ᵐ[μ] rr K P (n + 1) f := by
  have hd : 0 ≤ᵐ[μ] (tr μ K (n + 1) f - tr μ K n f : Lp ℝ 2 μ) := by
    filter_upwards [tr_le_succ μ K n hf, Lp.coeFn_sub (tr μ K (n + 1) f) (tr μ K n f)] with x h1 h2
    rw [h2, Pi.sub_apply]; simpa using h1
  filter_upwards [hpos _ hd, rr_ae K P n f, rr_ae K P (n + 1) f,
    Lp.coeFn_sub (P (tr μ K (n + 1) f)) (P (tr μ K n f))] with x h1 h2 h3 h4
  rw [map_sub, h4, Pi.sub_apply, h2, h3] at h1
  simpa using h1

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma rr_one_le (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1) (n : ℕ) :
    rr K P n 1 ≤ᵐ[μ] 1 := by
  filter_upwards [hle _ (tr_one_le μ K n), rr_ae K P n 1] with x h1 h2
  rw [← h2]; exact h1

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma rr_abs_le (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1) (n : ℕ)
    (f : C(OnePoint X, ℝ)) : ∀ᵐ x ∂μ, |rr K P n f x| ≤ ‖f‖ :=
  abs_le_norm_of_aeLinear (m := μ) (rr K P n) (rr_add K P n) (rr_smul K P n)
    (fun _ hf => rr_nonneg K P hpos n hf) (rr_one_le K P hle n) f

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
/-- a.e. convergence of `P(1_{K_n} f)` -/
lemma rr_tendsto_ae (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1)
    (f : C(OnePoint X, ℝ)) :
    ∀ᵐ x ∂μ, ∃ l : ℝ, Tendsto (fun n => rr K P n f x) atTop (𝓝 l) := by
  have hnn : ∀ g : C(OnePoint X, ℝ), 0 ≤ g →
      ∀ᵐ x ∂μ, ∃ l : ℝ, Tendsto (fun n => rr K P n g x) atTop (𝓝 l) := by
    intro g hg
    have h1 : ∀ᵐ x ∂μ, ∀ n, rr K P n g x ≤ rr K P (n + 1) g x :=
      ae_all_iff.2 fun n => rr_mono K P hpos n hg
    have h2 : ∀ᵐ x ∂μ, ∀ n, |rr K P n g x| ≤ ‖g‖ := ae_all_iff.2 fun n => rr_abs_le K P hpos hle n g
    filter_upwards [h1, h2] with x a b
    exact ⟨_, tendsto_atTop_ciSup (monotone_nat_of_le_succ a)
      ⟨‖g‖, by rintro _ ⟨n, rfl⟩; exact (le_abs_self _).trans (b n)⟩⟩
  set fp : C(OnePoint X, ℝ) := f ⊔ 0 with hfp
  set fm : C(OnePoint X, ℝ) := (-f) ⊔ 0 with hfm
  have hf : f = fp + (-1 : ℝ) • fm := by
    ext y
    simp only [hfp, hfm, ContinuousMap.add_apply, ContinuousMap.smul_apply,
      ContinuousMap.sup_apply, ContinuousMap.neg_apply, ContinuousMap.zero_apply, smul_eq_mul]
    rcases le_total (f y) 0 with h | h
    · simp [h, neg_nonneg.2 h]
    · have : -f y ≤ 0 := by linarith
      simp [h, this]
  have hp0 : 0 ≤ fp := fun y => le_sup_right
  have hm0 : 0 ≤ fm := fun y => le_sup_right
  have e : ∀ n, rr K P n f =ᵐ[μ] rr K P n fp + (-1 : ℝ) • rr K P n fm := fun n => by
    have h1 := rr_add K P n fp ((-1 : ℝ) • fm)
    have h2 := rr_smul K P n (-1 : ℝ) fm
    rw [← hf] at h1
    filter_upwards [h1, h2] with x a b
    rw [a, Pi.add_apply, b]
    rfl
  have eall : ∀ᵐ x ∂μ, ∀ n, rr K P n f x = rr K P n fp x + (-1 : ℝ) * rr K P n fm x := by
    refine ae_all_iff.2 fun n => ?_
    filter_upwards [e n] with x h
    simpa using h
  filter_upwards [eall, hnn fp hp0, hnn fm hm0] with x h1 ⟨l1, hl1⟩ ⟨l2, hl2⟩
  exact ⟨l1 + (-1) * l2, (hl1.add (hl2.const_mul (-1))).congr fun n => (h1 n).symm⟩

end Op

section Main

variable {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

omit [LocallyCompactSpace X] [SecondCountableTopology X] [IsFiniteMeasureOnCompacts μ] in
/-- the `L²`-tail `‖1_{K_n^c} g‖₂ → 0`. -/
lemma tendsto_eLpNorm_compl (K : CompactExhaustion X) {g : X → ℝ} (hg : MemLp g 2 μ) :
    Tendsto (fun n => eLpNorm ((K n)ᶜ.indicator g) 2 μ) atTop (𝓝 0) := by
  have hmK : ∀ n, MeasurableSet (K n)ᶜ := fun n => (measurableSet_K K n).compl
  have hsq : ∀ n, eLpNorm ((K n)ᶜ.indicator g) 2 μ ^ 2
      = ∫⁻ x, ENNReal.ofReal (((K n)ᶜ.indicator g x) ^ 2) ∂μ := fun n =>
    eLpNorm_two_sq_eq (hg.aestronglyMeasurable.indicator (hmK n))
  have hfin : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ ≠ ∞ := by
    rw [← eLpNorm_two_sq_eq hg.aestronglyMeasurable]
    exact (ENNReal.pow_lt_top hg.eLpNorm_lt_top).ne
  have hI : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (((K n)ᶜ.indicator g x) ^ 2) ∂μ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := μ)
      (F := fun n x => ENNReal.ofReal (((K n)ᶜ.indicator g x) ^ 2)) (f := fun _ => 0)
      (fun x => ENNReal.ofReal (g x ^ 2))
      (fun n => ((hg.aestronglyMeasurable.indicator (hmK n)).aemeasurable.pow_const 2).ennreal_ofReal)
      (fun n => Filter.Eventually.of_forall fun x => by
        by_cases hx : x ∈ (K n)ᶜ <;> simp [hx])
      hfin
      (Filter.Eventually.of_forall fun x => by
        have hx : x ∈ ⋃ n, K n := by rw [K.iUnion_eq]; trivial
        obtain ⟨N, hN⟩ := Set.mem_iUnion.1 hx
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have : x ∈ K n := K.subset hn hN
        simp [this])
    simpa using this
  have h2 : Tendsto (fun n => eLpNorm ((K n)ᶜ.indicator g) 2 μ ^ 2) atTop (𝓝 0) := by
    simpa only [hsq] using hI
  have h3 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h2
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  refine h3.congr fun n => ?_
  simp only [Function.comp]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

omit [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma tendsto_tr (K : CompactExhaustion X) (f₀ : C₀(X, ℝ)) (u : Lp ℝ 2 μ)
    (hu : (u : X → ℝ) =ᵐ[μ] f₀) :
    Tendsto (fun n => tr μ K n (R22.extC0 f₀)) atTop (𝓝 u) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := tendsto_eLpNorm_compl K (Lp.memLp u)
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  simp only [ENNReal.toReal_zero] at h1
  refine h1.congr fun n => ?_
  simp only [Function.comp]
  rw [Lp.norm_def]
  congr 1
  have hae : ((tr μ K n (R22.extC0 f₀) - u : Lp ℝ 2 μ) : X → ℝ)
      =ᵐ[μ] -((K n)ᶜ.indicator (u : X → ℝ)) := by
    filter_upwards [Lp.coeFn_sub (tr μ K n (R22.extC0 f₀)) u, coeFn_tr μ K n (R22.extC0 f₀), hu]
      with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, Pi.neg_apply]
    by_cases hx : x ∈ K n
    · have hext : R22.extC0 f₀ (x : OnePoint X) = f₀ x := rfl
      simp [hx, hext, h3]
    · simp [hx]
  rw [eLpNorm_congr_ae hae, eLpNorm_neg]

end Main

section Kernel

/-- the restriction to `X` of a kernel on the one-point compactification. -/
noncomputable def comapKernel (κ' : Kernel (OnePoint X) (OnePoint X)) : Kernel X X :=
  ⟨fun x => (κ' (x : OnePoint X)).comap ((↑) : X → OnePoint X), by
    have hι := R22.measurableEmbedding_coe (X := X)
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have : ∀ x, (κ' (x : OnePoint X)).comap ((↑) : X → OnePoint X) A
        = κ' (x : OnePoint X) (((↑) : X → OnePoint X) '' A) := fun x => hι.comap_apply _ _
    simp_rw [this]
    exact (κ'.measurable_coe (hι.measurableSet_image.2 hA)).comp hι.measurable⟩

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma comapKernel_apply (κ' : Kernel (OnePoint X) (OnePoint X)) (x : X) (A : Set X) :
    comapKernel κ' x A = κ' (x : OnePoint X) (((↑) : X → OnePoint X) '' A) :=
  (R22.measurableEmbedding_coe (X := X)).comap_apply _ _

end Kernel

section Main2

variable {μ : Measure X} [IsFiniteMeasureOnCompacts μ]

/-- **Riesz-Markov kernel on a non-compact space, `μ` finite on compacts (possibly infinite).** -/
theorem exists_kernel_of_posContraction_locFinite (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1) :
    ∃ κ : Kernel X X, (∀ x, κ x Set.univ ≤ 1) ∧
      ∀ (f : C₀(X, ℝ)) (u : Lp ℝ 2 μ), (u : X → ℝ) =ᵐ[μ] f →
        (P u : X → ℝ) =ᵐ[μ] fun x => ∫ y, f y ∂(κ x) := by
  classical
  let K : CompactExhaustion X := CompactExhaustion.choice X
  have hι := R22.measurableEmbedding_coe (X := X)
  -- the limit family
  have hlim : ∀ f : C(OnePoint X, ℝ), ∃ Ff : X → ℝ, Measurable Ff ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => rr K P n f x) atTop (𝓝 (Ff x)) := fun f =>
    measurable_limit_of_tendsto_metrizable_ae (fun n => (rr_meas K P n f).aemeasurable)
      (rr_tendsto_ae K P hpos hle f)
  choose F hFm hFt using hlim
  have hFadd : ∀ f g, F (f + g) =ᵐ[μ] F f + F g := by
    intro f g
    filter_upwards [hFt (f + g), hFt f, hFt g, ae_all_iff.2 (fun n => rr_add K P n f g)]
      with x h1 h2 h3 h4
    have h5 : Tendsto (fun n => rr K P n (f + g) x) atTop (𝓝 (F f x + F g x)) :=
      (h2.add h3).congr fun n => by rw [h4 n]; rfl
    exact tendsto_nhds_unique h1 h5
  have hFsmul : ∀ (c : ℝ) f, F (c • f) =ᵐ[μ] c • F f := by
    intro c f
    filter_upwards [hFt (c • f), hFt f, ae_all_iff.2 (fun n => rr_smul K P n c f)]
      with x h1 h2 h4
    have h5 : Tendsto (fun n => rr K P n (c • f) x) atTop (𝓝 (c • F f x)) :=
      (h2.const_smul c).congr fun n => by rw [h4 n]; rfl
    exact tendsto_nhds_unique h1 h5
  have hFpos : ∀ f : C(OnePoint X, ℝ), 0 ≤ f → 0 ≤ᵐ[μ] F f := by
    intro f hf
    filter_upwards [hFt f, ae_all_iff.2 (fun n => rr_nonneg K P hpos n hf)] with x h1 h2
    exact ge_of_tendsto' h1 fun n => h2 n
  have hFone : F 1 ≤ᵐ[μ] 1 := by
    filter_upwards [hFt 1, ae_all_iff.2 (fun n => rr_one_le K P hle n)] with x h1 h2
    exact le_of_tendsto' h1 fun n => h2 n
  -- transport to `X⁺`
  let G : C(OnePoint X, ℝ) → OnePoint X → ℝ := fun f => Function.extend ((↑) : X → OnePoint X) (F f) 0
  have hG : ∀ (f : C(OnePoint X, ℝ)) (x : X), G f (x : OnePoint X) = F f x := fun f x => hι.injective.extend_apply _ _ x
  have hGm : ∀ f, Measurable (G f) := fun f => hι.measurable_extend (hFm f) measurable_const
  have transfer : ∀ (p : OnePoint X → Prop), (∀ᵐ (x : X) ∂μ, p (x : OnePoint X)) →
      ∀ᵐ y ∂(μ.map ((↑) : X → OnePoint X)), p y := fun p h => hι.ae_map_iff.2 h
  obtain ⟨κ', hsub', hrep'⟩ := exists_kernel_of_aeLinear (μ.map ((↑) : X → OnePoint X)) G hGm
    (fun f g => transfer (fun y => G (f + g) y = (G f + G g) y) (by
      filter_upwards [hFadd f g] with x h
      simp only [Pi.add_apply, hG] at h ⊢; exact h))
    (fun c f => transfer (fun y => G (c • f) y = (c • G f) y) (by
      filter_upwards [hFsmul c f] with x h
      simp only [Pi.smul_apply, hG] at h ⊢; exact h))
    (fun f hf => transfer (fun y => (0 : OnePoint X → ℝ) y ≤ G f y) (by
      filter_upwards [hFpos f hf] with x h
      simp only [Pi.zero_apply, hG] at h ⊢; exact h))
    (transfer (fun y => G 1 y ≤ (1 : OnePoint X → ℝ) y) (by
      filter_upwards [hFone] with x h
      simp only [Pi.one_apply, hG] at h ⊢; exact h))
  have hFrep : ∀ f : C(OnePoint X, ℝ), ∀ᵐ x ∂μ, F f x = ∫ z, f z ∂(κ' (x : OnePoint X)) := by
    intro f
    have := hι.ae_map_iff.1 (hrep' f)
    filter_upwards [this] with x h
    rw [← hG]; exact h
  refine ⟨comapKernel κ', fun x => ?_, ?_⟩
  · rw [comapKernel_apply]
    exact (measure_mono (μ := κ' (x : OnePoint X)) (Set.subset_univ _)).trans (hsub' _)
  · intro f₀ u hu
    have hconv := tendsto_tr K f₀ u hu
    have hconv' : Tendsto (fun n => P (tr μ K n (R22.extC0 f₀))) atTop (𝓝 (P u)) :=
      (P.continuous.tendsto u).comp hconv
    obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hconv').exists_seq_tendsto_ae
    have hrall : ∀ᵐ x ∂μ, ∀ n, (P (tr μ K n (R22.extC0 f₀)) : X → ℝ) x
        = rr K P n (R22.extC0 f₀) x := ae_all_iff.2 fun n => rr_ae K P n _
    filter_upwards [hae, hrall, hFt (R22.extC0 f₀), hFrep (R22.extC0 f₀)] with x h1 h2 h3 h4
    have h5 : Tendsto (fun i => (P (tr μ K (ns i) (R22.extC0 f₀)) : X → ℝ) x) atTop
        (𝓝 (F (R22.extC0 f₀) x)) :=
      (h3.comp hns.tendsto_atTop).congr fun i => (h2 (ns i)).symm
    rw [tendsto_nhds_unique h1 h5, h4]
    show _ = ∫ y, f₀ y ∂((κ' (x : OnePoint X)).comap ((↑) : X → OnePoint X))
    rw [R22.integral_comap_extC0]

end Main2

end MarkovTriple.Stochastic.R23
