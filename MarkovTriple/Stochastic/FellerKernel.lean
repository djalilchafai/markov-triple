import Mathlib
import MarkovTriple.Stochastic.RieszMarkov
import MarkovTriple.Stochastic.Bridge

/-!
# Stochastic layer, part 16: exact kernel semigroups from the Feller property (round 16, `STATEMENTS_R16.md`)

Setting: `X` compact Hausdorff, second countable, Borel; `T : DiffusionTriple X` with finite `μ`.

If `P_t` is **Feller** (`IsFeller T`: `P_t [f]` has a continuous representative for each `f ∈ C(X)`) and
`μ` has **full support** (`μ.IsOpenPosMeasure`), then the continuous representatives are unique
(a.e. equal continuous functions are equal everywhere), so the *a.e.* identities of the semigroup
(linearity, positivity, `P_0 = id`, `P_{s+t} = P_s P_t`, sup-norm contractivity) become *exact* identities
between continuous functions, and the point functionals `f ↦ (P_t f)(x)` are positive linear functionals on `C(X)`
for **every** `x`.  Riesz-Markov-Kakutani (Mathlib `RealRMK`) then gives probability/sub-probability measures
`κ_t(x,·)` for all `x`, with exact Chapman-Kolmogorov `κ_{s+t} = κ_t ∘ₖ κ_s`, `κ_0 = id`
(two finite Borel measures on a compact metric space are determined by integrals of continuous functions).
In the conservative case `P_t 1 = 1` this is a `KernelBridge` (equality invariance by symmetry).

Textbook source: BGL Prop. 1.2.3 and Sect. 1.2.2 (representation of a Markov semigroup by a kernel);
the Feller route is the usual regularisation (Riesz-Markov + continuity of `x ↦ P_t f(x)`).  No claim is made
without the Feller property (`AUDIT_R16_SELF.md`, item 7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

set_option linter.unusedSectionVars false

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

section Aux

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- Finite Borel measures on a compact metrizable space are determined by integrals of continuous functions. -/
lemma measure_ext_C {m n : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure n]
    (h : ∀ f : C(X, ℝ), ∫ x, f x ∂m = ∫ x, f x ∂n) : m = n :=
  ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => h f.toContinuousMap

lemma integrable_cont (m : Measure X) [IsFiniteMeasure m] (f : C(X, ℝ)) : Integrable f m :=
  Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
    (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)

variable {μ : Measure X} [μ.IsOpenPosMeasure]

lemma cont_bound_of_ae {g : C(X, ℝ)} {c : ℝ} (h : ∀ᵐ x ∂μ, |g x| ≤ c) : ∀ x, |g x| ≤ c := by
  by_contra hx
  push Not at hx
  obtain ⟨x0, hx0⟩ := hx
  have hU : IsOpen {x | c < |g x|} := isOpen_lt continuous_const (continuous_abs.comp g.continuous)
  have hpos : 0 < μ {x | c < |g x|} := hU.measure_pos μ ⟨x0, hx0⟩
  have hnull : μ {x | c < |g x|} = 0 := by
    have := ae_iff.1 h
    simpa [not_le] using this
  exact absurd hnull hpos.ne'

lemma cont_nonneg_of_ae {g : C(X, ℝ)} (h : ∀ᵐ x ∂μ, 0 ≤ g x) : ∀ x, 0 ≤ g x := by
  by_contra hx
  push Not at hx
  obtain ⟨x0, hx0⟩ := hx
  have hU : IsOpen {x | g x < 0} := isOpen_lt g.continuous continuous_const
  have hpos : 0 < μ {x | g x < 0} := hU.measure_pos μ ⟨x0, hx0⟩
  have hnull : μ {x | g x < 0} = 0 := by
    have := ae_iff.1 h
    simpa [not_le] using this
  exact absurd hnull hpos.ne'

end Aux

section Feller

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (T : DiffusionTriple X) [IsFiniteMeasure T.μ]

/-- **Feller property** (a.e. form): `P_t [f]` has a continuous representative for every `f ∈ C(X)`. -/
def IsFeller : Prop :=
  ∀ (t : ℝ≥0) (f : C(X, ℝ)), ∃ g : C(X, ℝ), (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] ⇑g

/-- `|P_t [f]| ≤ ‖f‖` a.e. (positivity + sub-Markov). -/
lemma semigroup_cls_abs_le (t : ℝ≥0) (f : C(X, ℝ)) :
    ∀ᵐ x ∂T.μ, |(T.semigroup t (clsC T.μ f) : X → ℝ) x| ≤ ‖f‖ :=
  psiOf_abs_le (P := T.semigroup t) (fun _ hu => T.semigroup_nonneg t hu)
    (fun u hu => T.semigroup_le_one t u hu) f

/-- **Feller criterion**: if a sup-norm dense set of continuous functions has continuous `P_t`-images
(a.e.), then `P_t` is Feller (`P_t` is a sup-norm contraction on classes of continuous functions). -/
theorem isFeller_of_dense [T.μ.IsOpenPosMeasure] (D : Set C(X, ℝ)) (hD : Dense D)
    (h : ∀ t : ℝ≥0, ∀ d ∈ D, ∃ g : C(X, ℝ), (T.semigroup t (clsC T.μ d) : X → ℝ) =ᵐ[T.μ] ⇑g) :
    IsFeller T := by
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
      have hb := semigroup_cls_abs_le T t (u m - u n)
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

/-- Mass identity: if `P_t 1 = 1` then `∫ P_t u = ∫ u` (symmetry of `P_t`). -/
theorem integral_semigroup_eq (t : ℝ≥0) (h1 : T.semigroup t T.one2 = T.one2) (u : Lp ℝ 2 T.μ) :
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

variable [T.μ.IsOpenPosMeasure] (hF : IsFeller T)

/-- The continuous representative of `P_t [f]`. -/
noncomputable def fellerOp (t : ℝ≥0) (f : C(X, ℝ)) : C(X, ℝ) := Classical.choose (hF t f)

lemma fellerOp_ae (t : ℝ≥0) (f : C(X, ℝ)) :
    (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] ⇑(fellerOp hF t f) :=
  Classical.choose_spec (hF t f)

lemma clsC_injective : Function.Injective (fun f : C(X, ℝ) => clsC T.μ f) := by
  intro f g hfg
  have h1 : (clsC T.μ f : X → ℝ) =ᵐ[T.μ] (clsC T.μ g : X → ℝ) := by
    rw [show clsC T.μ f = clsC T.μ g from hfg]
  have h2 : (f : X → ℝ) =ᵐ[T.μ] g :=
    (coeFn_clsC f).symm.trans (h1.trans (coeFn_clsC g))
  exact DFunLike.coe_injective ((f.continuous.ae_eq_iff_eq T.μ g.continuous).1 h2)

lemma fellerOp_cls (t : ℝ≥0) (f : C(X, ℝ)) :
    T.semigroup t (clsC T.μ f) = clsC T.μ (fellerOp hF t f) :=
  Lp.ext ((fellerOp_ae hF t f).trans (coeFn_clsC _).symm)

lemma clsC_add (f g : C(X, ℝ)) : clsC T.μ (f + g) = clsC T.μ f + clsC T.μ g :=
  map_add (ContinuousMap.toLp 2 T.μ ℝ) _ _

lemma clsC_smul (c : ℝ) (f : C(X, ℝ)) : clsC T.μ (c • f) = c • clsC T.μ f :=
  map_smul (ContinuousMap.toLp 2 T.μ ℝ) _ _

lemma fellerOp_add (t : ℝ≥0) (f g : C(X, ℝ)) :
    fellerOp hF t (f + g) = fellerOp hF t f + fellerOp hF t g := by
  apply clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← fellerOp_cls hF, clsC_add, map_add, fellerOp_cls hF, fellerOp_cls hF, clsC_add]

lemma fellerOp_smul (t : ℝ≥0) (c : ℝ) (f : C(X, ℝ)) :
    fellerOp hF t (c • f) = c • fellerOp hF t f := by
  apply clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← fellerOp_cls hF, clsC_smul, map_smul, fellerOp_cls hF, clsC_smul]

lemma fellerOp_zero (f : C(X, ℝ)) : fellerOp hF 0 f = f := by
  apply clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← fellerOp_cls hF, DiffusionTriple.semigroup_zero]; rfl

lemma fellerOp_add_time (s t : ℝ≥0) (f : C(X, ℝ)) :
    fellerOp hF (s + t) f = fellerOp hF s (fellerOp hF t f) := by
  apply clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← fellerOp_cls hF, ← fellerOp_cls hF, DiffusionTriple.semigroup_add]
  show T.semigroup s (T.semigroup t (clsC T.μ f)) = _
  rw [fellerOp_cls hF t f, fellerOp_cls hF]

lemma fellerOp_nonneg (t : ℝ≥0) {f : C(X, ℝ)} (hf : 0 ≤ f) : ∀ x, 0 ≤ fellerOp hF t f x := by
  have hu : 0 ≤ᵐ[T.μ] (clsC T.μ f : X → ℝ) := by
    filter_upwards [coeFn_clsC (μ := T.μ) f] with x hx
    rw [hx]; exact hf x
  have := T.semigroup_nonneg t hu
  refine cont_nonneg_of_ae (μ := T.μ) ?_
  filter_upwards [this, fellerOp_ae hF t f] with x h1 h2
  rw [← h2]; exact h1

lemma fellerOp_abs_le (t : ℝ≥0) (f : C(X, ℝ)) (x : X) : |fellerOp hF t f x| ≤ ‖f‖ := by
  refine cont_bound_of_ae (μ := T.μ) ?_ x
  filter_upwards [semigroup_cls_abs_le T t f, fellerOp_ae hF t f] with x h1 h2
  rwa [h2] at h1

/-- The positive linear functional `f ↦ (P_t f)(x)`. -/
noncomputable def fellerFun (t : ℝ≥0) (x : X) : C(X, ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => fellerOp hF t f x
      map_add' := fun f g => by simp [fellerOp_add hF]
      map_smul' := fun c f => by simp [fellerOp_smul hF] } 1
    (fun f => by
      simpa [Real.norm_eq_abs] using fellerOp_abs_le hF t f x)

lemma fellerFun_apply (t : ℝ≥0) (x : X) (f : C(X, ℝ)) : fellerFun hF t x f = fellerOp hF t f x := rfl

lemma fellerFun_pos (t : ℝ≥0) (x : X) : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ fellerFun hF t x f :=
  fun _ hf => fellerOp_nonneg hF t hf x

private lemma fellerMeasure_exists (t : ℝ≥0) (x : X) :
    ∃ m : Measure X, IsFiniteMeasure m ∧ ∀ f : C(X, ℝ), ∫ y, f y ∂m = fellerFun hF t x f :=
  exists_measure_of_pos _ (fellerFun_pos hF t x)

/-- The Riesz measure of the functional `f ↦ (P_t f)(x)`. -/
noncomputable def fellerMeasure (t : ℝ≥0) (x : X) : Measure X :=
  Classical.choose (fellerMeasure_exists hF t x)

instance fellerMeasure_finite (t : ℝ≥0) (x : X) : IsFiniteMeasure (fellerMeasure hF t x) :=
  (Classical.choose_spec (fellerMeasure_exists hF t x)).1

lemma integral_fellerMeasure (t : ℝ≥0) (x : X) (f : C(X, ℝ)) :
    ∫ y, f y ∂(fellerMeasure hF t x) = fellerOp hF t f x :=
  (Classical.choose_spec (fellerMeasure_exists hF t x)).2 f

/-- **The Feller kernels** (everywhere defined): `κ_t(x,·)` represents `f ↦ (P_t f)(x)`. -/
noncomputable def fellerKernel (t : ℝ≥0) : Kernel X X where
  toFun := fun x => fellerMeasure hF t x
  measurable' := measurable_of_integrals (κ := fun x => fellerMeasure hF t x) fun f => by
    simp_rw [integral_fellerMeasure]
    exact (fellerOp hF t f).continuous.measurable

lemma fellerKernel_apply (t : ℝ≥0) (x : X) : fellerKernel hF t x = fellerMeasure hF t x := rfl

instance fellerKernel_finite (t : ℝ≥0) (x : X) : IsFiniteMeasure (fellerKernel hF t x) :=
  fellerMeasure_finite hF t x

/-- **Pointwise representation, for all `x`.** -/
theorem integral_fellerKernel (t : ℝ≥0) (x : X) (f : C(X, ℝ)) :
    ∫ y, f y ∂(fellerKernel hF t x) = fellerOp hF t f x := integral_fellerMeasure hF t x f

theorem fellerKernel_subMarkov (t : ℝ≥0) (x : X) : fellerKernel hF t x Set.univ ≤ 1 := by
  have h1 : ∫ y, (1 : C(X, ℝ)) y ∂(fellerKernel hF t x) = (fellerKernel hF t x).real Set.univ := by
    simp
  have h2 := integral_fellerKernel hF t x 1
  have h3 : (fellerKernel hF t x).real Set.univ ≤ 1 := by
    rw [← h1, h2]
    exact (le_abs_self _).trans ((fellerOp_abs_le hF t 1 x).trans norm_one_le_one)
  have h4 : (fellerKernel hF t x Set.univ).toReal ≤ 1 := h3
  have hfin : fellerKernel hF t x Set.univ ≠ ∞ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  simpa using ENNReal.ofReal_le_ofReal h4

instance (t : ℝ≥0) : IsFiniteKernel (fellerKernel hF t) :=
  ⟨⟨1, ENNReal.one_lt_top, fellerKernel_subMarkov hF t⟩⟩

/-- `κ_0 = id` exactly. -/
theorem fellerKernel_zero : fellerKernel hF 0 = Kernel.id := by
  ext x : 1
  rw [Kernel.id_apply]
  refine measure_ext_C fun f => ?_
  rw [integral_fellerKernel, fellerOp_zero, integral_dirac]

/-- **Exact Chapman-Kolmogorov**: `κ_{s+t} = κ_t ∘ₖ κ_s` (for all `s, t` and all `x`). -/
theorem fellerKernel_add (s t : ℝ≥0) :
    fellerKernel hF (s + t) = fellerKernel hF t ∘ₖ fellerKernel hF s := by
  ext x : 1
  refine measure_ext_C fun f => ?_
  rw [Kernel.integral_comp (integrable_cont _ f)]
  simp_rw [integral_fellerKernel]
  rw [← integral_fellerKernel hF s x (fellerOp hF t f), fellerOp_add_time hF]
  exact (integral_fellerKernel hF s x _).symm ▸ rfl

/-- The exact sub-Markov kernel semigroup of a Feller triple. -/
noncomputable def fellerSemigroup : SubMarkovKernelSemigroup X where
  κ := fellerKernel hF
  subMarkov := fellerKernel_subMarkov hF
  zero := fellerKernel_zero hF
  add := fellerKernel_add hF

/-- Sub-invariance `μ.bind κ_t ≤ μ`. -/
theorem fellerKernel_bind_le (t : ℝ≥0) : T.μ.bind (fellerKernel hF t) ≤ T.μ := by
  refine bind_le_of_integral_le (fellerKernel hF t) (fellerKernel_subMarkov hF t) fun f hf => ?_
  have hu : 0 ≤ᵐ[T.μ] (clsC T.μ f : X → ℝ) := by
    filter_upwards [coeFn_clsC (μ := T.μ) f] with x hx
    rw [hx]; exact hf x
  have h1 := integral_semigroup_le T t _ hu
  have e1 : ∫ x, ∫ y, f y ∂(fellerKernel hF t x) ∂T.μ
      = ∫ x, (T.semigroup t (clsC T.μ f) : X → ℝ) x ∂T.μ := by
    simp_rw [integral_fellerKernel]
    exact (integral_congr_ae (fellerOp_ae hF t f)).symm
  have e2 : ∫ x, (clsC T.μ f : X → ℝ) x ∂T.μ = ∫ x, f x ∂T.μ :=
    integral_congr_ae (coeFn_clsC (μ := T.μ) f)
  rw [e1]; exact h1.trans e2.le

/-- **Representation on all bounded measurable `L²` functions** (a.e.; BGL Sect. 1.2.2). -/
theorem fellerKernel_rep (t : ℝ≥0) (g : X → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 T.μ) :
    (T.semigroup t (hL.toLp g) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(fellerKernel hF t x) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  refine kernelRep_of_dense (D := Set.range (fun g : C(X, ℝ) => (g : X → ℝ))) (fellerKernel hF)
    (fellerKernel_subMarkov hF) (fellerKernel_bind_le hF) ?_ ?_ ?_ ?_ ?_ t g hg hb hL
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
    show (T.semigroup t (hL.toLp g) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(fellerKernel hF t x)
    rw [e]
    simp_rw [integral_fellerKernel]
    exact fellerOp_ae hF t g

/-- **Uniqueness (everywhere)**: any finite-measure kernel which is weakly continuous in `x` and represents
`P_t` on continuous functions a.e. coincides with `fellerKernel` at every point. -/
theorem fellerKernel_unique (t : ℝ≥0) (κ' : Kernel X X) [∀ x, IsFiniteMeasure (κ' x)]
    (hc : ∀ f : C(X, ℝ), Continuous fun x => ∫ y, f y ∂(κ' x))
    (hr : ∀ f : C(X, ℝ), (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ' x))
    (x : X) : κ' x = fellerKernel hF t x := by
  refine measure_ext_C fun f => ?_
  rw [integral_fellerKernel]
  have h : (fun x => ∫ y, f y ∂(κ' x)) = ⇑(fellerOp hF t f) := by
    have := ((hc f).ae_eq_iff_eq T.μ (fellerOp hF t f).continuous).1
      ((hr f).symm.trans (fellerOp_ae hF t f))
    exact this
  exact congrFun h x

/-! ### Conservative case -/

section Conservative

variable (hcons : ∀ t, T.semigroup t T.one2 = T.one2)
include hcons

theorem fellerOp_one (t : ℝ≥0) : fellerOp hF t 1 = 1 := by
  apply clsC_injective (T := T)
  show clsC T.μ _ = clsC T.μ _
  rw [← fellerOp_cls hF]
  have : clsC T.μ (1 : C(X, ℝ)) = T.one2 :=
    Lp.ext ((coeFn_clsC (μ := T.μ) (1 : C(X, ℝ))).trans T.coeFn_one2.symm)
  rw [this, hcons t]

theorem fellerKernel_isMarkov (t : ℝ≥0) (x : X) : fellerKernel hF t x Set.univ = 1 := by
  have h1 := integral_fellerKernel hF t x 1
  rw [fellerOp_one hF hcons] at h1
  have hfin : fellerKernel hF t x Set.univ ≠ ∞ := measure_ne_top _ _
  have h2 : (fellerKernel hF t x).real Set.univ = 1 := by simpa using h1
  rw [Measure.real] at h2
  exact (ENNReal.toReal_eq_one_iff _).1 h2

/-- **Equality invariance** `μ.bind κ_t = μ` (conservative + symmetric). -/
theorem fellerKernel_bind (t : ℝ≥0) : T.μ.bind (fellerKernel hF t) = T.μ := by
  have : IsFiniteKernel (fellerKernel hF t) := inferInstance
  refine measure_ext_C fun f => ?_
  have e : T.μ.bind (fellerKernel hF t) = ((fellerKernel hF t) ∘ₖ (Kernel.const Unit T.μ)) () := by
    rw [Kernel.comp_apply, Kernel.const_apply]
  have hfin : IsFiniteMeasure (T.μ.bind (fellerKernel hF t)) := inferInstance
  rw [e, Kernel.integral_comp (integrable_cont _ f)]
  simp_rw [Kernel.const_apply, integral_fellerKernel]
  rw [← integral_congr_ae (fellerOp_ae hF t f), integral_semigroup_eq T t (hcons t)]
  exact integral_congr_ae (coeFn_clsC (μ := T.μ) f)

/-- **The exact bridge**: for a conservative Feller triple with full-support `μ` on a compact metrizable space,
the Feller kernels form a `KernelBridge` (exact CK, `κ_0 = id`, invariance, representation). -/
noncomputable def fellerBridge : KernelBridge T where
  toSubMarkovKernelSemigroup := fellerSemigroup hF
  rep := fun t g hg hb hL => fellerKernel_rep hF t g hg hb hL
  invariant := fun t => fellerKernel_bind hF hcons t

theorem fellerBridge_κ : (fellerBridge hF hcons).κ = fellerKernel hF := rfl

theorem fellerBridge_isMarkov : (fellerBridge hF hcons).toSubMarkovKernelSemigroup.IsMarkov :=
  fun t x => fellerKernel_isMarkov hF hcons t x

end Conservative

end WithFull

end Feller

end MarkovTriple.Stochastic
