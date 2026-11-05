import Mathlib
import MarkovTriple.Stochastic.R28.SGData

/-!
# Round 28 (M), part 2: the compact Feller kernel layer for abstract semigroup data

Verbatim transcription of `FellerKernel.lean` / `RepExtend.lean` / `FellerMeasurable.lean` (R16/R17/R15) with
`T : DiffusionTriple X` replaced by `T : SGData X` (only the semigroup and `T.μ` are used there).  Names are prefixed `sg`
(`sgOp`, `sgKernel`, ...).  No new mathematics.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R28

open MarkovTriple.BGL MarkovTriple.Stochastic

section RepExt

variable {E : Type*} [MeasurableSpace E]

/-- **Extension of the representation from a dense test class** (classical: `L²`-contractivity of
`P_t` and, by Jensen + sub-invariance, of `h ↦ κ_t h`; density of `D`).
If sub-Markov kernels `κ_t` with `μ.bind κ_t ≤ μ` represent `P_t` on a set `D` of bounded measurable
`L²` functions dense in `L²(μ)`, then they represent `P_t` on every bounded measurable `L²` function. -/
theorem sgKernelRepOfDense {T : SGData E} (κ : ℝ≥0 → Kernel E E)
    (hsub : ∀ t x, κ t x Set.univ ≤ 1)
    (hinv : ∀ t, T.μ.bind (κ t) ≤ T.μ)
    (D : Set (E → ℝ))
    (hDmeas : ∀ f ∈ D, Measurable f) (hDbdd : ∀ f ∈ D, ∃ C, ∀ x, |f x| ≤ C)
    (hDL : ∀ f ∈ D, MemLp f 2 T.μ)
    (hDdense : Dense {u : Lp ℝ 2 T.μ | ∃ f ∈ D, (u : E → ℝ) =ᵐ[T.μ] f})
    (hD : ∀ t, ∀ f (hf : f ∈ D),
      (T.semigroup t ((hDL f hf).toLp f) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ t x)) :
    ∀ (t : ℝ≥0) (g : E → ℝ), Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ hL : MemLp g 2 T.μ,
      (T.semigroup t (hL.toLp g) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(κ t x) := by
  intro t g hg ⟨C, hC⟩ hL
  have : IsFiniteKernel (κ t) := ⟨⟨1, ENNReal.one_lt_top, fun x => hsub t x⟩⟩
  have hKg : MemLp (fun x => ∫ y, g y ∂(κ t x)) 2 T.μ :=
    memLp_kernel_integral (κ t) (hsub t) (hinv t) hg hC hL
  -- it suffices to show the two `L²` classes are equal
  suffices hEq : T.semigroup t (hL.toLp g) = hKg.toLp _ by
    have := Lp.ext_iff.1 hEq
    filter_upwards [this, hKg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rw [← sub_eq_zero]
  refine norm_le_zero_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_)
  rw [zero_add]
  -- approximate `g` by `f ∈ D`
  obtain ⟨u, hdist, ⟨f, hfD, hu⟩⟩ :=
    Metric.dense_iff.1 hDdense (hL.toLp g) (ε / 3) (by positivity)
  rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hdist
  have hfL := hDL f hfD
  have huf : u = hfL.toLp f := Lp.ext (hu.trans hfL.coeFn_toLp.symm)
  obtain ⟨Cf, hCf⟩ := hDbdd f hfD
  have hKf : MemLp (fun x => ∫ y, f y ∂(κ t x)) 2 T.μ :=
    memLp_kernel_integral (κ t) (hsub t) (hinv t) (hDmeas f hfD) hCf hfL
  -- `P_t u = κ f`
  have e1 : T.semigroup t u = hKf.toLp _ := by
    rw [huf]
    refine Lp.ext ?_
    filter_upwards [hD t f hfD, hKf.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  -- `h = g - f`
  have hh : Measurable (g - f) := hg.sub (hDmeas f hfD)
  have hCh : ∀ x, |(g - f) x| ≤ C + Cf := fun x => by
    simp only [Pi.sub_apply]
    exact (abs_sub _ _).trans (add_le_add (hC x) (hCf x))
  have hhL : MemLp (g - f) 2 T.μ := hL.sub hfL
  have hKh : MemLp (fun x => ∫ y, (g - f) y ∂(κ t x)) 2 T.μ :=
    memLp_kernel_integral (κ t) (hsub t) (hinv t) hh hCh hhL
  have hKint : ∀ x, ∫ y, (g - f) y ∂(κ t x) =
      (∫ y, g y ∂(κ t x)) - ∫ y, f y ∂(κ t x) := by
    intro x
    have hi : ∀ {k : E → ℝ} {c : ℝ}, Measurable k → (∀ y, |k y| ≤ c) → Integrable k (κ t x) :=
      fun {k c} hk hkc => Integrable.of_bound hk.aestronglyMeasurable c
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hkc y)
    exact integral_sub (hi hg hC) (hi (hDmeas f hfD) hCf)
  -- bound the three terms
  have hsplit : T.semigroup t (hL.toLp g) - hKg.toLp _ =
      T.semigroup t (hL.toLp g - u) + (hKf.toLp _ - hKg.toLp _) := by
    rw [map_sub, e1]; abel
  have hn1 : ‖T.semigroup t (hL.toLp g - u)‖ ≤ ‖hL.toLp g - u‖ :=
    T.norm_semigroup_apply_le t _
  have hn2 : ‖hKf.toLp _ - hKg.toLp _‖ ≤ ‖hL.toLp g - u‖ := by
    have e2 : hKf.toLp _ - hKg.toLp _ = -(hKh.toLp _) := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (hKf.toLp _) (hKg.toLp _), hKf.coeFn_toLp, hKg.coeFn_toLp,
        Lp.coeFn_neg (hKh.toLp _), hKh.coeFn_toLp] with x h1 h2 h3 h4 h5
      rw [h1, Pi.sub_apply, h2, h3, h4, Pi.neg_apply, h5, hKint x]; ring
    rw [e2, norm_neg, Lp.norm_toLp]
    have e3 : ‖hL.toLp g - u‖ = (eLpNorm (g - f) 2 T.μ).toReal := by
      rw [huf, ← Lp.norm_toLp (g - f) hhL]
      congr 1
    rw [e3]
    exact ENNReal.toReal_mono hhL.ne (eLpNorm_kernel_le (κ t) (hsub t) (hinv t) hh hCh)
  rw [hsplit]
  calc ‖T.semigroup t (hL.toLp g - u) + (hKf.toLp _ - hKg.toLp _)‖
      ≤ ‖T.semigroup t (hL.toLp g - u)‖ + ‖hKf.toLp _ - hKg.toLp _‖ := norm_add_le _ _
    _ ≤ ‖hL.toLp g - u‖ + ‖hL.toLp g - u‖ := add_le_add hn1 hn2
    _ ≤ ε / 3 + ε / 3 := by gcongr
    _ ≤ ε := by linarith


end RepExt

section Feller

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (T : SGData X) [IsFiniteMeasure T.μ]

/-- **Feller property** (a.e. form): `P_t [f]` has a continuous representative for every `f ∈ C(X)`. -/
def IsFellerSG : Prop :=
  ∀ (t : ℝ≥0) (f : C(X, ℝ)), ∃ g : C(X, ℝ), (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] ⇑g

omit [T2Space X] [SecondCountableTopology X] in
/-- `|P_t [f]| ≤ ‖f‖` a.e. (positivity + sub-Markov). -/
lemma sg_semigroup_cls_abs_le (t : ℝ≥0) (f : C(X, ℝ)) :
    ∀ᵐ x ∂T.μ, |(T.semigroup t (clsC T.μ f) : X → ℝ) x| ≤ ‖f‖ :=
  psiOf_abs_le (P := T.semigroup t) (fun _ hu => T.semigroup_nonneg t hu)
    (fun u hu => T.semigroup_le_one t u hu) f

omit [SecondCountableTopology X] in
/-- **Feller criterion**: if a sup-norm dense set of continuous functions has continuous `P_t`-images
(a.e.), then `P_t` is Feller (`P_t` is a sup-norm contraction on classes of continuous functions). -/
theorem isFellerSG_of_dense [T.μ.IsOpenPosMeasure] (D : Set C(X, ℝ)) (hD : Dense D)
    (h : ∀ t : ℝ≥0, ∀ d ∈ D, ∃ g : C(X, ℝ), (T.semigroup t (clsC T.μ d) : X → ℝ) =ᵐ[T.μ] ⇑g) :
    IsFellerSG T := by
  intro t f
  let S : Set C(X, ℝ) := {f | ∃ g : C(X, ℝ), T.semigroup t (clsC T.μ f) = clsC T.μ g}
  have hDS : D ⊆ S := fun d hd => by
    obtain ⟨g, hg⟩ := h t d hd
    exact ⟨g, Lp.ext (hg.trans (coeFn_clsC g).symm)⟩
  have hS : IsClosed S := by
    refine isClosed_of_closure_subset fun f hf => ?_
    obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.1 hf
    choose g hg using huS
    have hdist : ∀ m n, dist (g m) (g n) ≤ dist (u m) (u n) := by
      intro m n
      have e : T.semigroup t (clsC T.μ (u m - u n)) = clsC T.μ (g m - g n) := by
        have e1 : clsC T.μ (u m - u n) = clsC T.μ (u m) - clsC T.μ (u n) :=
          map_sub (ContinuousMap.toLp 2 T.μ ℝ) _ _
        have e2 : clsC T.μ (g m - g n) = clsC T.μ (g m) - clsC T.μ (g n) :=
          map_sub (ContinuousMap.toLp 2 T.μ ℝ) _ _
        rw [e1, e2, map_sub, hg m, hg n]
      have hb := sg_semigroup_cls_abs_le T t (u m - u n)
      rw [e] at hb
      have hb2 : ∀ᵐ x ∂T.μ, |(g m - g n) x| ≤ ‖u m - u n‖ := by
        filter_upwards [hb, coeFn_clsC (μ := T.μ) (g m - g n)] with x h1 h2
        rwa [h2] at h1
      rw [dist_eq_norm, dist_eq_norm]
      exact (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun x => by
        simpa [Real.norm_eq_abs] using cont_bound_of_ae hb2 x
    have hcs : CauchySeq g := Metric.cauchySeq_iff.2 fun ε hε => by
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu.cauchySeq ε hε
      exact ⟨N, fun m hm n hn => (hdist m n).trans_lt (hN m hm n hn)⟩
    obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete hcs
    refine ⟨G, ?_⟩
    have hc1 : Continuous fun f : C(X, ℝ) => T.semigroup t (clsC T.μ f) :=
      (T.semigroup t).continuous.comp (ContinuousMap.toLp 2 T.μ ℝ).continuous
    have hc2 : Continuous fun f : C(X, ℝ) => clsC T.μ f := (ContinuousMap.toLp 2 T.μ ℝ).continuous
    have h1 : Tendsto (fun n => T.semigroup t (clsC T.μ (u n))) atTop
        (𝓝 (T.semigroup t (clsC T.μ f))) := (hc1.tendsto f).comp hu
    have h2 : Tendsto (fun n => clsC T.μ (g n)) atTop (𝓝 (clsC T.μ G)) := (hc2.tendsto G).comp hG
    have h1' : Tendsto (fun n => T.semigroup t (clsC T.μ (u n))) atTop (𝓝 (clsC T.μ G)) := by
      refine h2.congr fun n => (hg n).symm
    exact tendsto_nhds_unique h1 h1'
  have hf : f ∈ S := by
    have : f ∈ closure D := by rw [hD.closure_eq]; trivial
    exact (hS.closure_subset_iff.2 hDS) this
  obtain ⟨g, hg⟩ := hf
  exact ⟨g, by rw [hg]; exact coeFn_clsC g⟩

omit [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X] [BorelSpace X] in
/-- Mass identity: if `P_t 1 = 1` then `∫ P_t u = ∫ u` (symmetry of `P_t`). -/
theorem sg_integral_semigroup_eq (t : ℝ≥0) (h1 : T.semigroup t T.one2 = T.one2) (u : Lp ℝ 2 T.μ) :
    ∫ x, (T.semigroup t u : X → ℝ) x ∂T.μ = ∫ x, (u : X → ℝ) x ∂T.μ := by
  have hone := T.coeFn_one2
  have hsa : IsSelfAdjoint (T.semigroup t) := T.semigroup_isSelfAdjoint t
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa) u T.one2
  have e : ∀ v : Lp ℝ 2 T.μ, ∫ x, (v : X → ℝ) x ∂T.μ = inner ℝ v T.one2 := by
    intro v
    rw [L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [hone] with x hx
    rw [hx, mul_one]
  rw [e, e]
  have hsym' : inner ℝ (T.semigroup t u) T.one2 = inner ℝ u (T.semigroup t T.one2) := hsym
  rw [hsym', h1]

variable {T}

section WithFull

variable [T.μ.IsOpenPosMeasure] (hF : IsFellerSG T)

/-- The continuous representative of `P_t [f]`. -/
noncomputable def sgOp (t : ℝ≥0) (f : C(X, ℝ)) : C(X, ℝ) := Classical.choose (hF t f)

omit [T2Space X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] in
lemma sgOp_ae (t : ℝ≥0) (f : C(X, ℝ)) :
    (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] ⇑(sgOp hF t f) :=
  Classical.choose_spec (hF t f)

omit [T2Space X] [SecondCountableTopology X] in
lemma sg_clsC_injective : Function.Injective (fun f : C(X, ℝ) => clsC T.μ f) := by
  intro f g hfg
  have h1 : (clsC T.μ f : X → ℝ) =ᵐ[T.μ] (clsC T.μ g : X → ℝ) := by
    rw [show clsC T.μ f = clsC T.μ g from hfg]
  have h2 : (f : X → ℝ) =ᵐ[T.μ] g :=
    (coeFn_clsC f).symm.trans (h1.trans (coeFn_clsC g))
  exact DFunLike.coe_injective ((f.continuous.ae_eq_iff_eq T.μ g.continuous).1 h2)

omit [T2Space X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] in
lemma sgOp_cls (t : ℝ≥0) (f : C(X, ℝ)) :
    T.semigroup t (clsC T.μ f) = clsC T.μ (sgOp hF t f) :=
  Lp.ext ((sgOp_ae hF t f).trans (coeFn_clsC _).symm)

omit [T2Space X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] in
lemma sg_clsC_add (f g : C(X, ℝ)) : clsC T.μ (f + g) = clsC T.μ f + clsC T.μ g :=
  map_add (ContinuousMap.toLp 2 T.μ ℝ) _ _

omit [T2Space X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] in
lemma sg_clsC_smul (c : ℝ) (f : C(X, ℝ)) : clsC T.μ (c • f) = c • clsC T.μ f :=
  map_smul (ContinuousMap.toLp 2 T.μ ℝ) _ _

omit [T2Space X] [SecondCountableTopology X] in
lemma sgOp_add (t : ℝ≥0) (f g : C(X, ℝ)) :
    sgOp hF t (f + g) = sgOp hF t f + sgOp hF t g := by
  apply sg_clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← sgOp_cls hF, sg_clsC_add, map_add, sgOp_cls hF, sgOp_cls hF, sg_clsC_add]

omit [T2Space X] [SecondCountableTopology X] in
lemma sgOp_smul (t : ℝ≥0) (c : ℝ) (f : C(X, ℝ)) :
    sgOp hF t (c • f) = c • sgOp hF t f := by
  apply sg_clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← sgOp_cls hF, sg_clsC_smul, map_smul, sgOp_cls hF, sg_clsC_smul]

omit [T2Space X] [SecondCountableTopology X] in
lemma sgOp_zero (f : C(X, ℝ)) : sgOp hF 0 f = f := by
  apply sg_clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← sgOp_cls hF, SGData.semigroup_zero]; rfl

omit [T2Space X] [SecondCountableTopology X] in
lemma sgOp_add_time (s t : ℝ≥0) (f : C(X, ℝ)) :
    sgOp hF (s + t) f = sgOp hF s (sgOp hF t f) := by
  apply sg_clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← sgOp_cls hF, ← sgOp_cls hF, SGData.semigroup_add]
  show T.semigroup s (T.semigroup t (clsC T.μ f)) = _
  rw [sgOp_cls hF t f, sgOp_cls hF]

omit [T2Space X] [SecondCountableTopology X] in
lemma sgOp_nonneg (t : ℝ≥0) {f : C(X, ℝ)} (hf : 0 ≤ f) : ∀ x, 0 ≤ sgOp hF t f x := by
  have hu : 0 ≤ᵐ[T.μ] (clsC T.μ f : X → ℝ) := by
    filter_upwards [coeFn_clsC (μ := T.μ) f] with x hx
    rw [hx]; exact hf x
  have := T.semigroup_nonneg t hu
  refine cont_nonneg_of_ae (μ := T.μ) ?_
  filter_upwards [this, sgOp_ae hF t f] with x h1 h2
  rw [← h2]; exact h1

omit [T2Space X] [SecondCountableTopology X] in
lemma sgOp_abs_le (t : ℝ≥0) (f : C(X, ℝ)) (x : X) : |sgOp hF t f x| ≤ ‖f‖ := by
  refine cont_bound_of_ae (μ := T.μ) ?_ x
  filter_upwards [sg_semigroup_cls_abs_le T t f, sgOp_ae hF t f] with x h1 h2
  rwa [h2] at h1

/-- The positive linear functional `f ↦ (P_t f)(x)`. -/
noncomputable def sgFun (t : ℝ≥0) (x : X) : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => sgOp hF t f x
      map_add' := fun f g => by simp [sgOp_add hF]
      map_smul' := fun c f => by simp [sgOp_smul hF] } 1
    (fun f => by
      simpa [Real.norm_eq_abs] using sgOp_abs_le hF t f x)

omit [T2Space X] [SecondCountableTopology X] in
lemma sgFun_apply (t : ℝ≥0) (x : X) (f : C(X, ℝ)) : sgFun hF t x f = sgOp hF t f x := rfl

omit [T2Space X] [SecondCountableTopology X] in
lemma sgFun_pos (t : ℝ≥0) (x : X) : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ sgFun hF t x f :=
  fun _ hf => sgOp_nonneg hF t hf x

omit [SecondCountableTopology X] in
private lemma sgMeasure_exists (t : ℝ≥0) (x : X) :
    ∃ m : Measure X, IsFiniteMeasure m ∧ ∀ f : C(X, ℝ), ∫ y, f y ∂m = sgFun hF t x f :=
  exists_measure_of_pos _ (sgFun_pos hF t x)

/-- The Riesz measure of the functional `f ↦ (P_t f)(x)`. -/
noncomputable def sgMeasure (t : ℝ≥0) (x : X) : Measure X :=
  Classical.choose (sgMeasure_exists hF t x)

instance sgMeasure_finite (t : ℝ≥0) (x : X) : IsFiniteMeasure (sgMeasure hF t x) :=
  (Classical.choose_spec (sgMeasure_exists hF t x)).1

omit [SecondCountableTopology X] in
lemma integral_sgMeasure (t : ℝ≥0) (x : X) (f : C(X, ℝ)) :
    ∫ y, f y ∂(sgMeasure hF t x) = sgOp hF t f x :=
  (Classical.choose_spec (sgMeasure_exists hF t x)).2 f

/-- **The Feller kernels** (everywhere defined): `κ_t(x,·)` represents `f ↦ (P_t f)(x)`. -/
noncomputable def sgKernel (t : ℝ≥0) : Kernel X X where
  toFun := fun x => sgMeasure hF t x
  measurable' := measurable_of_integrals (κ := fun x => sgMeasure hF t x) fun f => by
    simp_rw [integral_sgMeasure]
    exact (sgOp hF t f).continuous.measurable

lemma sgKernel_apply (t : ℝ≥0) (x : X) : sgKernel hF t x = sgMeasure hF t x := rfl

instance sgKernel_finite (t : ℝ≥0) (x : X) : IsFiniteMeasure (sgKernel hF t x) :=
  sgMeasure_finite hF t x

/-- **Pointwise representation, for all `x`.** -/
theorem integral_sgKernel (t : ℝ≥0) (x : X) (f : C(X, ℝ)) :
    ∫ y, f y ∂(sgKernel hF t x) = sgOp hF t f x := integral_sgMeasure hF t x f

theorem sgKernel_subMarkov (t : ℝ≥0) (x : X) : sgKernel hF t x Set.univ ≤ 1 := by
  have h1 : ∫ y, (1 : C(X, ℝ)) y ∂(sgKernel hF t x) = (sgKernel hF t x).real Set.univ := by
    simp
  have h2 := integral_sgKernel hF t x 1
  have h3 : (sgKernel hF t x).real Set.univ ≤ 1 := by
    rw [← h1, h2]
    exact (le_abs_self _).trans ((sgOp_abs_le hF t 1 x).trans norm_one_le_one)
  have h4 : (sgKernel hF t x Set.univ).toReal ≤ 1 := h3
  have hfin : sgKernel hF t x Set.univ ≠ ∞ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  simpa using ENNReal.ofReal_le_ofReal h4

instance (t : ℝ≥0) : IsFiniteKernel (sgKernel hF t) :=
  ⟨⟨1, ENNReal.one_lt_top, sgKernel_subMarkov hF t⟩⟩

/-- `κ_0 = id` exactly. -/
theorem sgKernel_zero : sgKernel hF 0 = Kernel.id := by
  ext x : 1
  rw [Kernel.id_apply]
  refine measure_ext_C fun f => ?_
  rw [integral_sgKernel, sgOp_zero, integral_dirac]

/-- **Exact Chapman-Kolmogorov**: `κ_{s+t} = κ_t ∘ₖ κ_s` (for all `s, t` and all `x`). -/
theorem sgKernel_add (s t : ℝ≥0) :
    sgKernel hF (s + t) = sgKernel hF t ∘ₖ sgKernel hF s := by
  ext x : 1
  refine measure_ext_C fun f => ?_
  rw [Kernel.integral_comp (integrable_cont _ f)]
  simp_rw [integral_sgKernel]
  rw [← integral_sgKernel hF s x (sgOp hF t f), sgOp_add_time hF]
  exact (integral_sgKernel hF s x _).symm ▸ rfl

/-- The exact sub-Markov kernel semigroup of a Feller triple. -/
noncomputable def sgSemigroup : SubMarkovKernelSemigroup X where
  κ := sgKernel hF
  subMarkov := sgKernel_subMarkov hF
  zero := sgKernel_zero hF
  add := sgKernel_add hF

/-- Sub-invariance `μ.bind κ_t ≤ μ`. -/
theorem sgKernel_bind_le (t : ℝ≥0) : T.μ.bind (sgKernel hF t) ≤ T.μ := by
  refine bind_le_of_integral_le (sgKernel hF t) (sgKernel_subMarkov hF t) fun f hf => ?_
  have hu : 0 ≤ᵐ[T.μ] (clsC T.μ f : X → ℝ) := by
    filter_upwards [coeFn_clsC (μ := T.μ) f] with x hx
    rw [hx]; exact hf x
  have h1 := SGData.integral_semigroup_le T t _ hu
  have e1 : ∫ x, ∫ y, f y ∂(sgKernel hF t x) ∂T.μ
      = ∫ x, (T.semigroup t (clsC T.μ f) : X → ℝ) x ∂T.μ := by
    simp_rw [integral_sgKernel]
    exact (integral_congr_ae (sgOp_ae hF t f)).symm
  have e2 : ∫ x, (clsC T.μ f : X → ℝ) x ∂T.μ = ∫ x, f x ∂T.μ :=
    integral_congr_ae (coeFn_clsC (μ := T.μ) f)
  rw [e1]; exact h1.trans e2.le

/-- **Representation on all bounded measurable `L²` functions** (a.e.; BGL Sect. 1.2.2). -/
theorem sgKernel_rep (t : ℝ≥0) (g : X → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 T.μ) :
    (T.semigroup t (hL.toLp g) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(sgKernel hF t x) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  refine sgKernelRepOfDense (D := Set.range (fun g : C(X, ℝ) => (g : X → ℝ))) (sgKernel hF)
    (sgKernel_subMarkov hF) (sgKernel_bind_le hF) ?_ ?_ ?_ ?_ ?_ t g hg hb hL
  · rintro _ ⟨g, rfl⟩; exact g.continuous.measurable
  · rintro _ ⟨g, rfl⟩
    exact ⟨‖g‖, fun x => by simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm g x⟩
  · rintro _ ⟨g, rfl⟩
    exact MemLp.of_bound g.continuous.aestronglyMeasurable ‖g‖
      (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm g x)
  · refine Dense.mono ?_ (ContinuousMap.toLp_denseRange ℝ T.μ ℝ (p := 2) (by norm_num))
    rintro _ ⟨g, rfl⟩
    exact ⟨g, ⟨g, rfl⟩, ContinuousMap.coeFn_toLp _ _⟩
  · rintro t _ ⟨g, rfl⟩
    have hL : MemLp (g : X → ℝ) 2 T.μ :=
      MemLp.of_bound g.continuous.aestronglyMeasurable ‖g‖
        (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm g x)
    have e : hL.toLp g = clsC T.μ g := Lp.ext (hL.coeFn_toLp.trans (coeFn_clsC g).symm)
    show (T.semigroup t (hL.toLp g) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(sgKernel hF t x)
    rw [e]
    simp_rw [integral_sgKernel]
    exact sgOp_ae hF t g

/-- **Uniqueness (everywhere)**: any finite-measure kernel which is weakly continuous in `x` and represents
`P_t` on continuous functions a.e. coincides with `sgKernel` at every point. -/
theorem sgKernel_unique (t : ℝ≥0) (κ' : Kernel X X) [∀ x, IsFiniteMeasure (κ' x)]
    (hc : ∀ f : C(X, ℝ), Continuous fun x => ∫ y, f y ∂(κ' x))
    (hr : ∀ f : C(X, ℝ), (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ' x))
    (x : X) : κ' x = sgKernel hF t x := by
  refine measure_ext_C fun f => ?_
  rw [integral_sgKernel]
  have h : (fun x => ∫ y, f y ∂(κ' x)) = ⇑(sgOp hF t f) := by
    have := ((hc f).ae_eq_iff_eq T.μ (sgOp hF t f).continuous).1
      ((hr f).symm.trans (sgOp_ae hF t f))
    exact this
  exact congrFun h x

/-! ### Conservative case -/

section Conservative

variable (hcons : ∀ t, T.semigroup t T.one2 = T.one2)
include hcons

omit [T2Space X] [SecondCountableTopology X] in
theorem sgOp_one (t : ℝ≥0) : sgOp hF t 1 = 1 := by
  apply sg_clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← sgOp_cls hF]
  have : clsC T.μ (1 : C(X, ℝ)) = T.one2 :=
    Lp.ext ((coeFn_clsC (μ := T.μ) (1 : C(X, ℝ))).trans T.coeFn_one2.symm)
  rw [this, hcons t]

theorem sgKernel_isMarkov (t : ℝ≥0) (x : X) : sgKernel hF t x Set.univ = 1 := by
  have h1 := integral_sgKernel hF t x 1
  rw [sgOp_one hF hcons] at h1
  have hfin : sgKernel hF t x Set.univ ≠ ∞ := measure_ne_top _ _
  have h2 : (sgKernel hF t x).real Set.univ = 1 := by simpa using h1
  rw [Measure.real] at h2
  exact (ENNReal.toReal_eq_one_iff _).1 h2

/-- **Equality invariance** `μ.bind κ_t = μ` (conservative + symmetric). -/
theorem sgKernel_bind (t : ℝ≥0) : T.μ.bind (sgKernel hF t) = T.μ := by
  have : IsFiniteKernel (sgKernel hF t) := inferInstance
  refine measure_ext_C fun f => ?_
  have e : T.μ.bind (sgKernel hF t) = ((sgKernel hF t) ∘ₖ (Kernel.const Unit T.μ)) () := by
    rw [Kernel.comp_apply, Kernel.const_apply]
  have hfin : IsFiniteMeasure (T.μ.bind (sgKernel hF t)) := inferInstance
  rw [e, Kernel.integral_comp (integrable_cont _ f)]
  simp_rw [Kernel.const_apply, integral_sgKernel]
  rw [← integral_congr_ae (sgOp_ae hF t f), sg_integral_semigroup_eq T t (hcons t)]
  exact integral_congr_ae (coeFn_clsC (μ := T.μ) f)


end Conservative

end WithFull

end Feller

end MarkovTriple.Stochastic.R28
