import Mathlib
import MarkovTriple.Stochastic.RepExtend
import MarkovTriple.Stochastic.RieszKernel
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Frozen.CompactTriple

/-!
# Stochastic layer, part 9: `KernelRepresentation` for every triple on a compact metrizable space

For a `DiffusionTriple T` on a compact metrizable Borel space `X` with `T.μ` finite, the `L²(μ)` semigroup
`P_t` is positivity preserving and sub-Markov (theorems of the repo: `semigroup_nonneg`,
`semigroup_le_one`), so `RieszKernel.lean` (Riesz-Markov-Kakutani) provides sub-Markov kernels `κ_t` with
`P_t [f] = κ_t f` a.e. for `f ∈ C(X)`.  Then:

* sub-invariance `μ.bind κ_t ≤ μ` (classical: `∫ P_t u = ⟨u, P_t 1⟩ ≤ ∫ u` for `u ≥ 0`, by symmetry of `P_t` and
  `P_t 1 ≤ 1`; passing from continuous functions to closed sets by `HasOuterApproxClosed` and to Borel sets by
  inner regularity of finite measures on metrizable spaces) gives `L²`-contractivity of `κ_t`;
* `kernelRep_of_dense` with `D = C(X)` (dense in `L²(μ)`) extends `rep` to all bounded measurable `L²` functions.

Result: `rieszKernelRep T : KernelRepresentation T`, and `CompactTriple.kernelRep`.
Scope: chapman-Kolmogorov is only the `μ`-a.e. consequence `KernelRepresentation.ck_ae` (no exact CK).
-/

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

section SubInv

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- **Sub-invariance from integrals of continuous functions**: if `∫∫ f dκ dμ ≤ ∫ f dμ` for continuous
`f ≥ 0`, then `μ.bind κ ≤ μ`. -/
theorem bind_le_of_integral_le {μ : Measure X} [IsFiniteMeasure μ] (κ : Kernel X X)
    (hsub : ∀ x, κ x Set.univ ≤ 1)
    (h : ∀ f : C(X, ℝ), 0 ≤ f → ∫ x, ∫ y, f y ∂(κ x) ∂μ ≤ ∫ x, f x ∂μ) : μ.bind κ ≤ μ := by
  have : IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, fun x => hsub x⟩⟩
  have hfin : IsFiniteMeasure (μ.bind κ) := inferInstance
  have hclosed : ∀ K : Set X, IsClosed K → μ.bind κ K ≤ μ K := by
    intro K hK
    have h1 := HasOuterApproxClosed.tendsto_lintegral_apprSeq hK (μ.bind κ)
    have h2 := HasOuterApproxClosed.tendsto_lintegral_apprSeq hK μ
    refine le_of_tendsto_of_tendsto' h1 h2 fun n => ?_
    let ap : C(X, ℝ) := ⟨fun y => ((hK.apprSeq n y : ℝ≥0) : ℝ),
      (NNReal.continuous_coe.comp (hK.apprSeq n).continuous)⟩
    have hap0 : 0 ≤ ap := fun y => NNReal.coe_nonneg _
    have hb : ∀ y, ‖ap y‖ ≤ 1 := fun y => by
      simp only [ap, ContinuousMap.coe_mk, Real.norm_eq_abs, NNReal.abs_eq]
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hK n y
    have hcoe : ∀ y, (hK.apprSeq n y : ℝ≥0∞) = ENNReal.ofReal (ap y) := fun y => by
      simp [ap]
    simp_rw [hcoe]
    have hint : ∀ (m : Measure X) [IsFiniteMeasure m], Integrable ap m := fun m _ =>
      Integrable.of_bound ap.continuous.aestronglyMeasurable 1
        (Filter.Eventually.of_forall hb)
    have hintx : ∀ x, Integrable ap (κ x) := fun x => by
      have : IsFiniteMeasure (κ x) := ⟨lt_of_le_of_lt (hsub x) ENNReal.one_lt_top⟩
      exact hint _
    have hmeasf : Measurable fun x => ∫ y, ap y ∂(κ x) :=
      (ap.continuous.measurable.stronglyMeasurable.integral_kernel (κ := κ)).measurable
    have hgi : Integrable (fun x => ∫ y, ap y ∂(κ x)) μ := by
      refine Integrable.of_bound hmeasf.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
      have : IsFiniteMeasure (κ x) := ⟨lt_of_le_of_lt (hsub x) ENNReal.one_lt_top⟩
      calc ‖∫ y, ap y ∂(κ x)‖ ≤ 1 * (κ x).real Set.univ :=
            norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hb)
        _ ≤ 1 * 1 := by
            gcongr
            simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top (hsub x)
        _ = 1 := one_mul _
    have hmeas : Measurable fun y => ENNReal.ofReal (ap y) := by fun_prop
    rw [Measure.lintegral_bind (Kernel.aemeasurable κ) hmeas.aemeasurable]
    calc ∫⁻ x, ∫⁻ y, ENNReal.ofReal (ap y) ∂(κ x) ∂μ
        = ∫⁻ x, ENNReal.ofReal (∫ y, ap y ∂(κ x)) ∂μ := by
          refine lintegral_congr fun x => ?_
          rw [ofReal_integral_eq_lintegral_ofReal (hintx x)
            (Filter.Eventually.of_forall hap0)]
      _ = ENNReal.ofReal (∫ x, ∫ y, ap y ∂(κ x) ∂μ) := by
          rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun x =>
            integral_nonneg fun y => hap0 y)]
      _ ≤ ENNReal.ofReal (∫ x, ap x ∂μ) := ENNReal.ofReal_le_ofReal (h ap hap0)
      _ = ∫⁻ x, ENNReal.ofReal (ap x) ∂μ :=
          ofReal_integral_eq_lintegral_ofReal (hint μ) (Filter.Eventually.of_forall hap0)
  refine Measure.le_iff.2 fun A hA => ?_
  rw [hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top _ _)]
  exact iSup_le fun K => iSup_le fun hKA => iSup_le fun hKc =>
    (hclosed K hKc).trans (measure_mono hKA)

end SubInv

section Semigroup

variable {X : Type*} [MeasurableSpace X] (T : DiffusionTriple X) [IsFiniteMeasure T.μ]

/-- **Mass is non-increasing** for nonnegative `u ∈ L²`: `∫ P_t u ≤ ∫ u`
(symmetry of `P_t` and `P_t 1 ≤ 1`). -/
theorem integral_semigroup_le (t : ℝ≥0) (u : Lp ℝ 2 T.μ) (hu : 0 ≤ᵐ[T.μ] u) :
    ∫ x, (T.semigroup t u : X → ℝ) x ∂T.μ ≤ ∫ x, (u : X → ℝ) x ∂T.μ := by
  have hone := T.coeFn_one2
  have hPone : (T.semigroup t T.one2 : X → ℝ) ≤ᵐ[T.μ] 1 :=
    T.semigroup_le_one t _ (hone.le)
  have hsa : IsSelfAdjoint (T.semigroup t) := T.semigroup_isSelfAdjoint t
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa) u T.one2
  have e1 : ∫ x, (T.semigroup t u : X → ℝ) x ∂T.μ = inner ℝ (T.semigroup t u) T.one2 := by
    rw [L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [hone] with x hx
    rw [hx, mul_one]
  have e2 : inner ℝ u (T.semigroup t T.one2) = ∫ x, (u : X → ℝ) x * (T.semigroup t T.one2 : X → ℝ) x ∂T.μ :=
    L2_inner_eq _ _
  have hi1 : Integrable (fun x => (u : X → ℝ) x * (T.semigroup t T.one2 : X → ℝ) x) T.μ := by
    have := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) u (T.semigroup t T.one2)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_comm]
  have hi2 : Integrable (fun x => (u : X → ℝ) x) T.μ :=
    (Lp.memLp u).integrable (by norm_num)
  have hsym' : inner ℝ (T.semigroup t u) T.one2 = inner ℝ u (T.semigroup t T.one2) := hsym
  rw [e1, hsym', e2]
  refine integral_mono_ae hi1 hi2 ?_
  filter_upwards [hu, hPone] with x h1 h2
  have h1' : 0 ≤ (u : X → ℝ) x := h1
  calc (u : X → ℝ) x * (T.semigroup t T.one2 : X → ℝ) x ≤ (u : X → ℝ) x * 1 := mul_le_mul_of_nonneg_left h2 h1'
    _ = (u : X → ℝ) x := mul_one _

end Semigroup

section Construction

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (T : DiffusionTriple X) [IsFiniteMeasure T.μ]

lemma rieszKernel_exists (t : ℝ≥0) :
    ∃ κ : Kernel X X, (∀ x, κ x Set.univ ≤ 1) ∧
      ∀ f : C(X, ℝ), (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ x) :=
  exists_kernel_of_posContraction (T.semigroup t) (fun _ hu => T.semigroup_nonneg t hu)
    (fun u hu => T.semigroup_le_one t u hu)

/-- The **Riesz kernels** of the semigroup of `T`: `κ_t(x,·)` represents `f ↦ P_t [f](x)`. -/
noncomputable def rieszKernel (t : ℝ≥0) : Kernel X X := Classical.choose (rieszKernel_exists T t)

theorem rieszKernel_subMarkov (t : ℝ≥0) (x : X) : rieszKernel T t x Set.univ ≤ 1 :=
  (Classical.choose_spec (rieszKernel_exists T t)).1 x

/-- **The kernels represent `P_t` on continuous functions**: `P_t [f] = (x ↦ ∫ f dκ_t(x,·))` a.e. -/
theorem rieszKernel_continuous (t : ℝ≥0) (f : C(X, ℝ)) :
    (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(rieszKernel T t x) :=
  (Classical.choose_spec (rieszKernel_exists T t)).2 f

/-- **Sub-invariance**: `μ.bind κ_t ≤ μ`. -/
theorem rieszKernel_subInvariant (t : ℝ≥0) : T.μ.bind (rieszKernel T t) ≤ T.μ := by
  refine bind_le_of_integral_le (rieszKernel T t) (rieszKernel_subMarkov T t) fun f hf => ?_
  have hu : 0 ≤ᵐ[T.μ] (clsC T.μ f : Lp ℝ 2 T.μ) := by
    filter_upwards [coeFn_clsC (μ := T.μ) f] with x hx
    rw [hx]; exact hf x
  have h1 := integral_semigroup_le T t _ hu
  have e1 : ∫ x, ∫ y, f y ∂(rieszKernel T t x) ∂T.μ
      = ∫ x, (T.semigroup t (clsC T.μ f) : X → ℝ) x ∂T.μ :=
    (integral_congr_ae (rieszKernel_continuous T t f)).symm
  have e2 : ∫ x, (clsC T.μ f : X → ℝ) x ∂T.μ = ∫ x, f x ∂T.μ :=
    integral_congr_ae (coeFn_clsC (μ := T.μ) f)
  rw [e1]; exact h1.trans e2.le

/-- **Full kernel representation of the semigroup of any triple on a compact metrizable space**
(finite `μ`): `P_t [g] = (x ↦ ∫ g dκ_t(x,·))` `μ`-a.e. for every bounded measurable `g ∈ L²(μ)`. -/
noncomputable def rieszKernelRep : KernelRepresentation T where
  κ := rieszKernel T
  subMarkov := rieszKernel_subMarkov T
  rep := by
    have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
    refine kernelRep_of_dense (D := Set.range (fun g : C(X, ℝ) => (g : X → ℝ))) (rieszKernel T)
      (rieszKernel_subMarkov T) (rieszKernel_subInvariant T)
      ?_ ?_ ?_ ?_ ?_
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
      show (T.semigroup t (hL.toLp g) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(rieszKernel T t x)
      rw [e]
      exact rieszKernel_continuous T t g

theorem rieszKernelRep_κ (t : ℝ≥0) : (rieszKernelRep T).κ t = rieszKernel T t := rfl

/-- Continuous-function form of the representation, with an arbitrary representative `u` of `[f]`. -/
theorem rieszKernelRep_continuous (t : ℝ≥0) (f : C(X, ℝ)) (u : Lp ℝ 2 T.μ)
    (hu : (u : X → ℝ) =ᵐ[T.μ] f) :
    (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂((rieszKernelRep T).κ t x) := by
  have : u = clsC T.μ f := Lp.ext (hu.trans (coeFn_clsC f).symm)
  rw [this]
  exact rieszKernel_continuous T t f

theorem rieszKernelRep_subInvariant (t : ℝ≥0) :
    T.μ.bind ((rieszKernelRep T).κ t) ≤ T.μ := rieszKernel_subInvariant T t

end Construction

/-! ### Compact triples -/

/-- For a `CompactTriple` (`𝒜 = 𝒜₀`, unital), `1 ∈ 𝒜₀ ⊂ L¹(μ)`, hence `μ` is finite. -/
theorem compactTriple_isFiniteMeasure {E : Type*} [MeasurableSpace E] (T : CompactTriple E) :
    IsFiniteMeasure T.μ := by
  have h1 : (1 : E → ℝ) ∈ T.A₀ := (T.A_eq 1).1 T.A.one_mem
  have h2 : Integrable (fun _ : E => (1 : ℝ)) T.μ :=
    memLp_one_iff_integrable.1 (T.memLp 1 h1 1 le_rfl ENNReal.one_ne_top)
  rcases integrable_const_iff.1 h2 with h | h
  · exact absurd h one_ne_zero
  · exact h

/-- **Every `CompactTriple` on a compact metrizable Borel space has a kernel representation of its
semigroup** (Riesz-Markov-Kakutani construction). -/
noncomputable def compactTripleKernelRep {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    (T : CompactTriple X) : KernelRepresentation T.toDiffusionTriple :=
  haveI := compactTriple_isFiniteMeasure T
  rieszKernelRep T.toDiffusionTriple

end MarkovTriple.Stochastic
