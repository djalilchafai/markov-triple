import Mathlib
import MarkovTriple.Stochastic.R28.GoCompact
import MarkovTriple.Stochastic.MarkovProcessInterface

/-!
# Round 28 (M), part 6: Markov kernels and a `MarkovProcessBridge` for `goFullTriple`

* `goKernelI t`: the Riesz-Markov (Feller) kernels of the transported semigroup `goSG` on the compact interval `GI = [-1,1]`:
  Markov, exact Chapman-Kolmogorov, `κ_0 = id`, `goμI` invariant, jointly measurable.
* `goKernel t`: the kernel on `ℝ`: from `x ∈ [-1,1]` it is `(goKernelI t x).map val`; points `x ∉ [-1,1]` (a `goμ`-null set) are frozen
  (`δ_x`), which is forced by `κ_0 = id` on all of `ℝ`.
* `goMarkovProcessBridge : MarkovProcessBridge goFullTriple.toDiffusionTriple`.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R28

open MarkovTriple.BGL MarkovTriple.BGL.Instances.GegenbauerOpen MarkovTriple.Stochastic MarkovTriple.Stochastic.R27

/-- the Riesz-Markov kernels on `[-1,1]` of the transported semigroup -/
noncomputable def goKernelI (t : ℝ≥0) : Kernel GI GI := sgKernel goI_isFeller t

theorem goKernelI_isMarkov (t : ℝ≥0) (x : GI) : goKernelI t x Set.univ = 1 :=
  sgKernel_isMarkov goI_isFeller goSG_one t x

instance (t : ℝ≥0) (x : GI) : IsProbabilityMeasure (goKernelI t x) := ⟨goKernelI_isMarkov t x⟩

instance (t : ℝ≥0) : IsMarkovKernel (goKernelI t) := ⟨fun _ => inferInstance⟩

theorem goKernelI_zero : goKernelI 0 = Kernel.id := sgKernel_zero goI_isFeller

theorem goKernelI_add (s t : ℝ≥0) : goKernelI (s + t) = (goKernelI t).comp (goKernelI s) :=
  sgKernel_add goI_isFeller s t

theorem goKernelI_bind (t : ℝ≥0) : goμI.bind (goKernelI t) = goμI :=
  sgKernel_bind goI_isFeller goSG_one t

theorem goKernelI_measurable : Measurable fun p : ℝ≥0 × GI => goKernelI p.1 p.2 :=
  sgKernel_measurable_joint goI_isFeller

theorem goKernelI_rep (t : ℝ≥0) (g : GI → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 goμI) :
    (goSemigroupI t (hL.toLp g) : GI → ℝ) =ᵐ[goμI] fun x => ∫ y, g y ∂(goKernelI t x) :=
  sgKernel_rep goI_isFeller t g hg hb hL

/-- the kernel on `ℝ`: `(goKernelI t x).map val` on `[-1,1]`, frozen outside -/
noncomputable def goKernel (t : ℝ≥0) : Kernel ℝ ℝ :=
  Kernel.piecewise (measurableSet_Icc (a := (-1 : ℝ)) (b := 1))
    (((goKernelI t).comap goRetr continuous_goRetr.measurable).map Subtype.val) Kernel.id

lemma goKernel_of_mem (t : ℝ≥0) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    goKernel t x = (goKernelI t ⟨x, hx⟩).map Subtype.val := by
  have e : goRetr x = ⟨x, hx⟩ := goRetr_val ⟨x, hx⟩
  simp [goKernel, Kernel.piecewise_apply, hx, Kernel.map_apply _ measurable_subtype_coe, Kernel.comap_apply, e]

lemma goKernel_of_not_mem (t : ℝ≥0) {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) :
    goKernel t x = Measure.dirac x := by
  simp [goKernel, Kernel.piecewise_apply, hx, Kernel.id_apply]

instance (t : ℝ≥0) (x : ℝ) : IsProbabilityMeasure (goKernel t x) := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [goKernel_of_mem t hx]
    exact ⟨by rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]; simp⟩
  · rw [goKernel_of_not_mem t hx]; infer_instance

lemma goKernel_apply_set (t : ℝ≥0) (x : GI) {A : Set ℝ} (hA : MeasurableSet A) :
    goKernel t x.1 A = goKernelI t x (Subtype.val ⁻¹' A) := by
  rw [goKernel_of_mem t x.2, Measure.map_apply measurable_subtype_coe hA]

theorem goKernel_isMarkov (t : ℝ≥0) (x : ℝ) : goKernel t x Set.univ = 1 := measure_univ

theorem goKernel_zero : goKernel 0 = Kernel.id := by
  ext x : 1
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · rw [goKernel_of_mem 0 hx, goKernelI_zero, Kernel.id_apply, Measure.map_dirac' measurable_subtype_coe,
      Kernel.id_apply]
  · rw [goKernel_of_not_mem 0 hx, Kernel.id_apply]

theorem goKernel_add (s t : ℝ≥0) : goKernel (s + t) = (goKernel t).comp (goKernel s) := by
  ext x : 1
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · refine Measure.ext fun A hA => ?_
    have hA' : MeasurableSet (Subtype.val ⁻¹' A : Set GI) := measurable_subtype_coe hA
    have h1 : goKernel (s + t) x A = ∫⁻ z, goKernelI t z (Subtype.val ⁻¹' A) ∂(goKernelI s ⟨x, hx⟩) := by
      rw [goKernel_of_mem (s + t) hx, Measure.map_apply measurable_subtype_coe hA, goKernelI_add]
      exact Kernel.comp_apply' _ _ _ hA'
    have h2 : ((goKernel t).comp (goKernel s)) x A = ∫⁻ z, goKernelI t z (Subtype.val ⁻¹' A) ∂(goKernelI s ⟨x, hx⟩) := by
      rw [Kernel.comp_apply' _ _ _ hA, goKernel_of_mem s hx,
        lintegral_map (Kernel.measurable_coe _ hA) measurable_subtype_coe]
      exact lintegral_congr fun z => goKernel_apply_set t z hA
    rw [h1, h2]
  · rw [goKernel_of_not_mem (s + t) hx, Kernel.comp_apply, goKernel_of_not_mem s hx,
      Measure.dirac_bind (goKernel t).measurable, goKernel_of_not_mem t hx]

lemma goKernel_apply_eq (t : ℝ≥0) (x : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    goKernel t x A = if x ∈ Icc (-1 : ℝ) 1 then goKernelI t (goRetr x) (Subtype.val ⁻¹' A)
      else A.indicator (fun _ => (1 : ℝ≥0∞)) x := by
  by_cases hx : x ∈ Icc (-1 : ℝ) 1
  · have e : goRetr x = ⟨x, hx⟩ := goRetr_val ⟨x, hx⟩
    simp only [hx, ↓reduceIte]
    rw [e]
    exact goKernel_apply_set t ⟨x, hx⟩ hA
  · simp only [hx, ↓reduceIte]
    rw [goKernel_of_not_mem t hx, Measure.dirac_apply' _ hA]
    rfl

lemma goKernel_measurable : Measurable fun p : ℝ≥0 × ℝ => goKernel p.1 p.2 := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hA' : MeasurableSet (Subtype.val ⁻¹' A : Set GI) := measurable_subtype_coe hA
  have hc : Measurable fun p : ℝ≥0 × ℝ => goKernelI p.1 (goRetr p.2) (Subtype.val ⁻¹' A) := by
    have hA2 : Measurable fun p : ℝ≥0 × ℝ => ((p.1, goRetr p.2) : ℝ≥0 × GI) :=
      measurable_fst.prodMk (continuous_goRetr.measurable.comp measurable_snd)
    let KJ : Kernel (ℝ≥0 × GI) GI := ⟨fun p => goKernelI p.1 p.2, goKernelI_measurable⟩
    have hB : Measurable fun p : ℝ≥0 × GI => goKernelI p.1 p.2 (Subtype.val ⁻¹' A) :=
      Kernel.measurable_coe KJ hA'
    have hC := hB.comp hA2
    exact hC
  have hd : Measurable fun p : ℝ≥0 × ℝ => A.indicator (fun _ => (1 : ℝ≥0∞)) p.2 :=
    (measurable_const.indicator hA).comp measurable_snd
  have e : (fun p : ℝ≥0 × ℝ => goKernel p.1 p.2 A) = fun p =>
      if p.2 ∈ Icc (-1 : ℝ) 1 then goKernelI p.1 (goRetr p.2) (Subtype.val ⁻¹' A)
        else A.indicator (fun _ => (1 : ℝ≥0∞)) p.2 := funext fun p => goKernel_apply_eq p.1 p.2 hA
  rw [e]
  exact Measurable.ite (measurableSet_Icc.preimage measurable_snd) hc hd

/-- **Representation** on bounded measurable `L²(goμ)` functions -/
theorem goKernel_rep (t : ℝ≥0) (g : ℝ → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 goμ) :
    (goFullTriple.toDiffusionTriple.semigroup t (hL.toLp g) : ℝ → ℝ) =ᵐ[goμ]
      fun x => ∫ y, g y ∂(goKernel t x) := by
  have hL' : MemLp (g ∘ Subtype.val) 2 goμI := hL.comp_measurePreserving measurePreserving_gj
  have hb' : ∃ C, ∀ x : GI, |(g ∘ Subtype.val) x| ≤ C := by
    obtain ⟨C, hC⟩ := hb; exact ⟨C, fun x => hC x.1⟩
  have h1 := goKernelI_rep t (g ∘ Subtype.val) (hg.comp measurable_subtype_coe) hb' hL'
  have e : hL'.toLp (g ∘ Subtype.val) = goRestr (hL.toLp g) := by
    refine Lp.ext ?_
    filter_upwards [hL'.coeFn_toLp, coeFn_goRestr (hL.toLp g),
      (ae_goμ_iff (p := fun x => (hL.toLp g : ℝ → ℝ) x = g x)).1 hL.coeFn_toLp] with x a b c
    rw [a, b]; exact c.symm
  rw [e, goSemigroupI_restr] at h1
  refine (ae_goμ_iff (p := fun x => (goFullTriple.toDiffusionTriple.semigroup t (hL.toLp g) : ℝ → ℝ) x
    = ∫ y, g y ∂(goKernel t x))).2 ?_
  filter_upwards [h1, coeFn_goRestr (goFullTriple.toDiffusionTriple.semigroup t (hL.toLp g))] with x a b
  rw [goKernel_of_mem t x.2, integral_map measurable_subtype_coe.aemeasurable hg.aestronglyMeasurable]
  have hh := b.symm.trans a
  exact hh

/-- **invariance** `goμ.bind κ_t = goμ` -/
theorem goKernel_bind (t : ℝ≥0) : goμ.bind (goKernel t) = goμ := by
  refine Measure.ext fun A hA => ?_
  rw [Measure.bind_apply hA (goKernel t).aemeasurable, ← map_gj,
    lintegral_map (Kernel.measurable_coe _ hA) measurable_subtype_coe]
  have e : ∀ z : GI, goKernel t z.1 A = goKernelI t z (Subtype.val ⁻¹' A) := fun z => goKernel_apply_set t z hA
  simp_rw [e]
  have : (goμI.bind (goKernelI t)) (Subtype.val ⁻¹' A) = goμI (Subtype.val ⁻¹' A) := by
    rw [goKernelI_bind]
  rw [Measure.bind_apply (measurable_subtype_coe hA) (goKernelI t).aemeasurable] at this
  rw [this, Measure.map_apply measurable_subtype_coe hA]

/-- **A `MarkovProcessBridge` for `goFullTriple`** (on `X = ℝ`): jointly measurable Markov kernels, exact Chapman-Kolmogorov,
`κ_0 = id`, `goμ` invariant, representing `P_t` on bounded measurable `L²(goμ)` functions. -/
noncomputable def goMarkovProcessBridge : MarkovProcessBridge goFullTriple.toDiffusionTriple where
  kernel := goKernel
  measurable_kernel := goKernel_measurable
  kernel_zero := goKernel_zero
  kernel_add := goKernel_add
  isSubMarkovKernel := fun t x => (goKernel_isMarkov t x).le
  rep := fun t g hg hb hL => goKernel_rep t g hg hb hL
  invariant := fun t => goKernel_bind t

theorem goMarkovProcessBridge_kernel_of_mem (t : ℝ≥0) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    goMarkovProcessBridge.kernel t x = (goKernelI t ⟨x, hx⟩).map Subtype.val := goKernel_of_mem t hx

theorem goMarkovProcessBridge_kernel_of_not_mem (t : ℝ≥0) {x : ℝ} (hx : x ∉ Icc (-1 : ℝ) 1) :
    goMarkovProcessBridge.kernel t x = Measure.dirac x := goKernel_of_not_mem t hx

theorem goMarkovProcessBridge_isMarkov : ∀ t x, goMarkovProcessBridge.kernel t x Set.univ = 1 :=
  goKernel_isMarkov

/-- the kernels from `x ∈ [-1,1]` are carried by `[-1,1]` -/
theorem goMarkovProcessBridge_support (t : ℝ≥0) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    goMarkovProcessBridge.kernel t x (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [goMarkovProcessBridge_kernel_of_mem t hx, Measure.map_apply measurable_subtype_coe
    measurableSet_Icc.compl]
  have : (Subtype.val : GI → ℝ) ⁻¹' (Icc (-1 : ℝ) 1)ᶜ = ∅ := by
    ext y; simp
  rw [this]; simp

/-- the bridge yields an exact `KernelBridge` for `goFullTriple` -/
noncomputable def goKernelBridge : KernelBridge goFullTriple.toDiffusionTriple :=
  goMarkovProcessBridge.toKernelBridge

end MarkovTriple.Stochastic.R28
