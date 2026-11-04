import Mathlib
import MarkovTriple.Stochastic.RieszMarkov
import MarkovTriple.Stochastic.ExactCK
import MarkovTriple.Stochastic.R22.OnePointCountable

/-!
# Round 22 (E3), part (iii): Riesz-Markov kernels on a non-compact state space, finite `μ`

`X` locally compact, `T2`, second countable, Borel, `μ` finite.  Reduction to the compact case
(`exists_kernel_of_posContraction`, R15) by the one-point compactification `X⁺ = OnePoint X`,
`muP = μ.map (↑)`; `L²(muP) ≃ L²(μ)` (the point `∞` is `μ⁺`-null).  The kernel on `X` is the
restriction (`Measure.comap (↑)`) of the Riesz kernel on `X⁺`: mass sent to `∞` is lost, so the kernel
is only sub-Markov.  Representation holds for `f ∈ C₀(X)`; by density of `C_c ⊆ C₀` in `L²(μ)`
(finite Radon `μ`) it extends to all bounded measurable `L²` functions (`kernelRep_of_dense`).
See `STATEMENTS_R22_E3.md`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty

namespace MarkovTriple.Stochastic.R22

open MarkovTriple.BGL MarkovTriple.Stochastic

section Compactify

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- Borel structure on the one-point compactification (local instance). -/
local instance ncMeas : MeasurableSpace (OnePoint X) := borel (OnePoint X)
local instance ncBorel : BorelSpace (OnePoint X) := ⟨rfl⟩

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma measurableEmbedding_coe : MeasurableEmbedding ((↑) : X → OnePoint X) :=
  OnePoint.isOpenEmbedding_coe.measurableEmbedding

variable (μ : Measure X) [IsFiniteMeasure μ]

/-- the transported measure on `X⁺` -/
noncomputable abbrev muP : Measure (OnePoint X) := μ.map ((↑) : X → OnePoint X)

omit [IsFiniteMeasure μ] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma measurePreserving_coe : MeasurePreserving ((↑) : X → OnePoint X) μ (muP μ) :=
  ⟨measurableEmbedding_coe.measurable, rfl⟩

instance : IsFiniteMeasure (muP μ) := inferInstanceAs (IsFiniteMeasure (μ.map _))

/-- `L²(muP) ≃ L²(μ)` by composition with `(↑)`. -/
noncomputable def Uequiv : Lp ℝ 2 (muP μ) ≃ₗᵢ[ℝ] Lp ℝ 2 μ :=
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℝ ((↑) : X → OnePoint X)
    (measurePreserving_coe μ)) (by
      intro u
      classical
      let e : X → OnePoint X := (↑)
      let g : OnePoint X → ℝ := Function.extend e (u : X → ℝ) 0
      have hg : g ∘ e = (u : X → ℝ) := funext fun x =>
        measurableEmbedding_coe.injective.extend_apply _ _ x
      have hgL : MemLp g 2 (muP μ) := by
        rw [measurableEmbedding_coe.memLp_map_measure_iff, hg]
        exact Lp.memLp u
      refine ⟨hgL.toLp g, ?_⟩
      refine Lp.ext ?_
      refine (Lp.coeFn_compMeasurePreserving (hgL.toLp g) (measurePreserving_coe μ)).trans ?_
      have h1 := (measurePreserving_coe μ).quasiMeasurePreserving.ae_eq_comp hgL.coeFn_toLp
      exact h1.trans (Filter.EventuallyEq.of_eq hg))

omit [IsFiniteMeasure μ] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma Uequiv_ae (w : Lp ℝ 2 (muP μ)) : (Uequiv μ w : X → ℝ) =ᵐ[μ] (w : OnePoint X → ℝ) ∘ ((↑) : X → OnePoint X) :=
  Lp.coeFn_compMeasurePreserving w (measurePreserving_coe μ)

omit [IsFiniteMeasure μ] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma ae_Uequiv (w : Lp ℝ 2 (muP μ)) (p : ℝ → Prop) :
    (∀ᵐ y ∂(muP μ), p (w y)) ↔ ∀ᵐ x ∂μ, p (Uequiv μ w x) := by
  rw [measurableEmbedding_coe.ae_map_iff]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · filter_upwards [h, Uequiv_ae μ w] with x hx hx2
    rw [hx2]; exact hx
  · filter_upwards [h, Uequiv_ae μ w] with x hx hx2
    rw [hx2] at hx; exact hx

omit [IsFiniteMeasure μ] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma integral_Uequiv (w : Lp ℝ 2 (muP μ)) : ∫ x, (Uequiv μ w : X → ℝ) x ∂μ = ∫ y, (w : OnePoint X → ℝ) y ∂(muP μ) := by
  rw [measurableEmbedding_coe.integral_map]
  exact integral_congr_ae (Uequiv_ae μ w)

/-- the conjugated operator on `L²(muP)` -/
noncomputable def Pplus (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) : Lp ℝ 2 (muP μ) →L[ℝ] Lp ℝ 2 (muP μ) :=
  (Uequiv μ).symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L P ∘L
    (Uequiv μ).toContinuousLinearEquiv.toContinuousLinearMap

omit [IsFiniteMeasure μ] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma U_Pplus (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) (w : Lp ℝ 2 (muP μ)) :
    Uequiv μ (Pplus μ P w) = P (Uequiv μ w) := by
  simp [Pplus]

/-- continuous extension by `0` of a `C₀` function -/
noncomputable def extC0 (f : C₀(X, ℝ)) : C(OnePoint X, ℝ) where
  toFun := fun a => OnePoint.rec 0 (fun x => f x) a
  continuous_toFun := by
    rw [OnePoint.continuous_iff]
    refine ⟨?_, f.continuous⟩
    rw [Filter.coclosedCompact_eq_cocompact]
    exact f.zero_at_infty'


omit [IsFiniteMeasure μ] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma mass_Pplus (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hmass : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → ∫ x, (P u : X → ℝ) x ∂μ ≤ ∫ x, (u : X → ℝ) x ∂μ)
    (w : Lp ℝ 2 (muP μ)) (hw : 0 ≤ᵐ[muP μ] w) :
    ∫ y, (Pplus μ P w : OnePoint X → ℝ) y ∂(muP μ) ≤ ∫ y, (w : OnePoint X → ℝ) y ∂(muP μ) := by
  rw [← integral_Uequiv μ, ← integral_Uequiv μ, U_Pplus]
  exact hmass _ ((ae_Uequiv μ w (fun r => 0 ≤ r)).1 hw)

omit [IsFiniteMeasure μ] [LocallyCompactSpace X] [SecondCountableTopology X] in
lemma integral_comap_extC0 (ν : Measure (OnePoint X)) (f : C₀(X, ℝ)) :
    ∫ y, f y ∂(ν.comap ((↑) : X → OnePoint X)) = ∫ a, extC0 f a ∂ν := by
  have hι := measurableEmbedding_coe (X := X)
  have h1 : ∫ y, f y ∂(ν.comap ((↑) : X → OnePoint X))
      = ∫ y, extC0 f (y : OnePoint X) ∂(ν.comap ((↑) : X → OnePoint X)) := rfl
  rw [h1, ← hι.integral_map, hι.map_comap]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero fun a ha => ?_
  induction a using OnePoint.rec with
  | infty => rfl
  | coe x => exact absurd ⟨x, rfl⟩ ha

/-- **Riesz-Markov kernel on a non-compact space, finite `μ`.** -/
theorem exists_kernel_of_posContraction_noncompact (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] P u)
    (hle : ∀ u : Lp ℝ 2 μ, (u : X → ℝ) ≤ᵐ[μ] 1 → (P u : X → ℝ) ≤ᵐ[μ] 1)
    (hmass : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] u → ∫ x, (P u : X → ℝ) x ∂μ ≤ ∫ x, (u : X → ℝ) x ∂μ) :
    ∃ κ : Kernel X X, (∀ x, κ x Set.univ ≤ 1) ∧ μ.bind κ ≤ μ ∧
      ∀ (f : C₀(X, ℝ)) (u : Lp ℝ 2 μ), (u : X → ℝ) =ᵐ[μ] f →
        (P u : X → ℝ) =ᵐ[μ] fun x => ∫ y, f y ∂(κ x) := by
  have hpos' : ∀ u' : Lp ℝ 2 (muP μ), 0 ≤ᵐ[muP μ] u' → 0 ≤ᵐ[muP μ] Pplus μ P u' := by
    intro u' h
    have h2 := (ae_Uequiv μ u' (fun r => 0 ≤ r)).1 h
    have h3 := hpos (Uequiv μ u') h2
    exact (ae_Uequiv μ (Pplus μ P u') (fun r => 0 ≤ r)).2 (by rw [U_Pplus]; exact h3)
  have hle' : ∀ u' : Lp ℝ 2 (muP μ), (u' : OnePoint X → ℝ) ≤ᵐ[muP μ] 1 →
      (Pplus μ P u' : OnePoint X → ℝ) ≤ᵐ[muP μ] 1 := by
    intro u' h
    have h2 := (ae_Uequiv μ u' (fun r => r ≤ 1)).1 h
    have h3 := hle (Uequiv μ u') h2
    exact (ae_Uequiv μ (Pplus μ P u') (fun r => r ≤ 1)).2 (by rw [U_Pplus]; exact h3)
  obtain ⟨κ', hsub', hrep'⟩ := exists_kernel_of_posContraction (μ := muP μ) (Pplus μ P) hpos' hle'
  have hbind' : (muP μ).bind κ' ≤ muP μ := by
    refine bind_le_of_integral_le κ' hsub' fun f hf => ?_
    have hu : 0 ≤ᵐ[muP μ] (clsC (muP μ) f : Lp ℝ 2 (muP μ)) := by
      filter_upwards [coeFn_clsC (μ := muP μ) f] with y hy
      rw [hy]; exact hf y
    have e1 : ∫ x, ∫ y, f y ∂(κ' x) ∂(muP μ)
        = ∫ x, (Pplus μ P (clsC (muP μ) f) : OnePoint X → ℝ) x ∂(muP μ) :=
      (integral_congr_ae (hrep' f)).symm
    have e2 : ∫ x, (clsC (muP μ) f : OnePoint X → ℝ) x ∂(muP μ) = ∫ x, f x ∂(muP μ) :=
      integral_congr_ae (coeFn_clsC (μ := muP μ) f)
    rw [e1]; exact (mass_Pplus μ P hmass _ hu).trans e2.le
  let ι : X → OnePoint X := (↑)
  have hι := measurableEmbedding_coe (X := X)
  let κ : Kernel X X :=
    ⟨fun x => (κ' (ι x)).comap ι, by
      refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
      have : ∀ x, (κ' (ι x)).comap ι A = κ' (ι x) (ι '' A) := fun x => hι.comap_apply _ _
      simp_rw [this]
      exact (κ'.measurable_coe (hι.measurableSet_image.2 hA)).comp hι.measurable⟩
  have hκ : ∀ x A, κ x A = κ' (ι x) (ι '' A) := fun x A => hι.comap_apply _ _
  refine ⟨κ, fun x => ?_, ?_, ?_⟩
  · rw [hκ]; exact (measure_mono (Set.subset_univ _)).trans (hsub' _)
  · rw [Measure.le_iff]
    intro A hA
    rw [Measure.bind_apply hA κ.aemeasurable]
    simp_rw [hκ]
    have h1 : ∫⁻ x, κ' (ι x) (ι '' A) ∂μ = ((muP μ).bind κ') (ι '' A) := by
      rw [Measure.bind_apply (hι.measurableSet_image.2 hA) κ'.aemeasurable,
        hι.lintegral_map (fun y => κ' y (ι '' A))]
    rw [h1]
    refine (hbind' _).trans ?_
    rw [Measure.map_apply hι.measurable (hι.measurableSet_image.2 hA),
      Set.preimage_image_eq _ hι.injective]
  · intro f u hu
    set f' := extC0 f with hf'
    set u' := (Uequiv μ).symm u with hu'
    have hUu' : Uequiv μ u' = u := (Uequiv μ).apply_symm_apply u
    have hcls : u' = clsC (muP μ) f' := by
      apply (Uequiv μ).injective
      rw [hUu']
      refine Lp.ext ?_
      have h1 := Uequiv_ae μ (clsC (muP μ) f')
      have h2 : ((clsC (muP μ) f' : Lp ℝ 2 (muP μ)) : OnePoint X → ℝ) ∘ ι =ᵐ[μ] f' ∘ ι :=
        (measurePreserving_coe μ).quasiMeasurePreserving.ae_eq_comp (coeFn_clsC (μ := muP μ) f')
      refine hu.trans ?_
      refine EventuallyEq.symm (h1.trans (h2.trans ?_))
      exact Eventually.of_forall fun x => rfl
    have e1 : (P u : X → ℝ) =ᵐ[μ] (Pplus μ P u' : OnePoint X → ℝ) ∘ ι := by
      rw [← hUu', ← U_Pplus]
      exact Uequiv_ae μ _
    have e2 : (Pplus μ P u' : OnePoint X → ℝ) ∘ ι =ᵐ[μ] fun x => ∫ a, f' a ∂(κ' (ι x)) := by
      rw [hcls]
      exact (measurePreserving_coe μ).quasiMeasurePreserving.ae_eq_comp (hrep' f')
    refine e1.trans (e2.trans (Eventually.of_forall fun x => ?_))
    show _ = ∫ y, f y ∂((κ' (ι x)).comap ι)
    rw [integral_comap_extC0]


lemma c0_bdd {Y : Type*} [TopologicalSpace Y] (f : C₀(Y, ℝ)) : ∃ C, ∀ x, |(f : Y → ℝ) x| ≤ C :=
  ⟨‖f.toBCF‖, fun x => by simpa [Real.norm_eq_abs] using f.toBCF.norm_coe_le_norm x⟩

section Triple

variable (T : DiffusionTriple X) [IsFiniteMeasure T.μ]

lemma ncKernel_exists (t : ℝ≥0) :
    ∃ κ : Kernel X X, (∀ x, κ x Set.univ ≤ 1) ∧ T.μ.bind κ ≤ T.μ ∧
      ∀ (f : C₀(X, ℝ)) (u : Lp ℝ 2 T.μ), (u : X → ℝ) =ᵐ[T.μ] f →
        (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ x) :=
  exists_kernel_of_posContraction_noncompact T.μ (T.semigroup t)
    (fun _ hu => T.semigroup_nonneg t hu) (fun u hu => T.semigroup_le_one t u hu)
    (fun u hu => integral_semigroup_le T t u hu)

/-- The (non-compact) Riesz kernels of the semigroup of `T` (finite `μ`). -/
noncomputable def ncKernel (t : ℝ≥0) : Kernel X X := Classical.choose (ncKernel_exists T t)

theorem ncKernel_subMarkov (t : ℝ≥0) (x : X) : ncKernel T t x Set.univ ≤ 1 :=
  (Classical.choose_spec (ncKernel_exists T t)).1 x

theorem ncKernel_subInvariant (t : ℝ≥0) : T.μ.bind (ncKernel T t) ≤ T.μ :=
  (Classical.choose_spec (ncKernel_exists T t)).2.1

theorem ncKernel_C0 (t : ℝ≥0) (f : C₀(X, ℝ)) (u : Lp ℝ 2 T.μ) (hu : (u : X → ℝ) =ᵐ[T.μ] f) :
    (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(ncKernel T t x) :=
  (Classical.choose_spec (ncKernel_exists T t)).2.2 f u hu

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma c0_memLp (f : C₀(X, ℝ)) : MemLp (f : X → ℝ) 2 T.μ := by
  obtain ⟨C, hC⟩ := c0_bdd f
  exact MemLp.of_bound f.continuous.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

/-- compactly supported continuous functions are dense in `L²(μ)`, and they are in `C₀`. -/
lemma c0_dense :
    Dense {u : Lp ℝ 2 T.μ | ∃ f ∈ Set.range (fun g : C₀(X, ℝ) => (g : X → ℝ)),
      (u : X → ℝ) =ᵐ[T.μ] f} := by
  rw [Metric.dense_iff]
  intro u r hr
  obtain ⟨g, hgc, hg1, hgcont, hgL⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le
    (μ := T.μ) (p := 2) (by norm_num) (ε := ENNReal.ofReal (r / 2)) (by simpa using by positivity)
  let g0 : C₀(X, ℝ) := ⟨⟨g, hgcont⟩, hgc.is_zero_at_infty⟩
  refine ⟨hgL.toLp g, ?_, g0, ⟨g0, rfl⟩, hgL.coeFn_toLp⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm, Lp.norm_def]
  have e : eLpNorm (⇑(u - hgL.toLp g)) 2 T.μ = eLpNorm ((u : X → ℝ) - g) 2 T.μ := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub u (hgL.toLp g), hgL.coeFn_toLp] with x h1 h2
    rw [h1]; simp [h2]
  rw [e]
  have hle : eLpNorm ((u : X → ℝ) - g) 2 T.μ ≤ ENNReal.ofReal (r / 2) := hg1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  linarith

/-- **Full kernel representation on a non-compact space** (finite `μ`). -/
noncomputable def ncKernelRep : KernelRepresentation T where
  κ := ncKernel T
  subMarkov := ncKernel_subMarkov T
  rep := by
    refine kernelRep_of_dense (D := Set.range (fun g : C₀(X, ℝ) => (g : X → ℝ))) (ncKernel T)
      (ncKernel_subMarkov T) (ncKernel_subInvariant T) ?_ ?_ ?_ (c0_dense T) ?_
    · rintro _ ⟨g, rfl⟩; exact g.continuous.measurable
    · rintro _ ⟨g, rfl⟩; exact c0_bdd g
    · rintro _ ⟨g, rfl⟩; exact c0_memLp T g
    · rintro t _ ⟨g, rfl⟩
      exact ncKernel_C0 T t g _ (c0_memLp T g).coeFn_toLp

theorem ncKernelRep_κ (t : ℝ≥0) : (ncKernelRep T).κ t = ncKernel T t := rfl

theorem ncKernelRep_subInvariant (t : ℝ≥0) : T.μ.bind ((ncKernelRep T).κ t) ≤ T.μ :=
  ncKernel_subInvariant T t

theorem ncKernelRep_C0 (t : ℝ≥0) (f : C₀(X, ℝ)) (u : Lp ℝ 2 T.μ) (hu : (u : X → ℝ) =ᵐ[T.μ] f) :
    (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂((ncKernelRep T).κ t x) :=
  ncKernel_C0 T t f u hu

/-- **Exact Chapman-Kolmogorov for countably many times** for the non-compact kernels. -/
theorem nc_exists_exact_ck (S : Set ℝ≥0) (hS : S.Countable) :
    ∃ G : Set X, MeasurableSet G ∧ T.μ Gᶜ = 0 ∧
      (∀ x ∈ G, ∀ s ∈ S, (ncKernelRep T).κ s x Gᶜ = 0) ∧
      (∀ x ∈ G, ∀ s ∈ S, ∀ t ∈ S, (ncKernelRep T).κ (s + t) x
          = ((ncKernelRep T).κ t ∘ₖ (ncKernelRep T).κ s) x) ∧
      (0 ∈ S → ∀ x ∈ G, (ncKernelRep T).κ 0 x = Measure.dirac x) :=
  (ncKernelRep T).exists_exact_ck S hS (ncKernelRep_subInvariant T)

end Triple

end Compactify

end MarkovTriple.Stochastic.R22
