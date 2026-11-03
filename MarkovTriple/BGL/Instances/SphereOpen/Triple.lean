import Mathlib
import MarkovTriple.BGL.Instances.SphereOpen.LpTransport
import MarkovTriple.BGL.Instances.Sphere.Triple

/-!
# The open zonal sphere as a `DiffusionTriple` (D1-D8; R17 Noncompact, N3)

State space `ZonO = (-1,1)` (non-compact), `μO` the restriction of `μZ`, test algebra
`𝒜₀ = {f ∘ val | f ∈ 𝒜_Z}`, `L (f ∘ val) = (L_Z f) ∘ val`, `Γ (f ∘ val)(g ∘ val) = (Γ_Z f g) ∘ val`
(`L_Z f = (1-x²) f'' - 3 x f'`, `Γ_Z f g = (1-x²) f' g'`).  The lift `f' ↦ f` (`liftO`) is unique since
`(-1,1)` is dense in `[-1,1]` and the elements of `𝒜_Z` are continuous.
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal
open MarkovTriple.BGL (pderiv pderiv₂)

namespace MarkovTriple.BGL.Instances.SphereOpen

open MarkovTriple.BGL.Instances.Sphere

/-- the extended algebra `{f ∘ val | f ∈ 𝒜_Z}`. -/
def AO : Subalgebra ℝ (ZonO → ℝ) where
  carrier := {f' | ∃ f ∈ AZ, f' = f ∘ jO}
  add_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, add_mem hf hg, rfl⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, mul_mem hf hg, rfl⟩
  algebraMap_mem' := fun r => ⟨algebraMap ℝ (Zon → ℝ) r, AZ.algebraMap_mem r, rfl⟩

lemma mem_AO {f' : ZonO → ℝ} : f' ∈ AO ↔ ∃ f ∈ AZ, f' = f ∘ jO := Iff.rfl

lemma comp_mem_AO {f : Zon → ℝ} (hf : f ∈ AZ) : f ∘ jO ∈ AO := ⟨f, hf, rfl⟩

/-- the non-unital test algebra. -/
def A0O : NonUnitalSubalgebra ℝ (ZonO → ℝ) := AO.toNonUnitalSubalgebra

lemma mem_A0O {f' : ZonO → ℝ} : f' ∈ A0O ↔ f' ∈ AO := Iff.rfl

/-- elements of `𝒜_Z` are determined by their restriction to `(-1,1)`. -/
lemma eq_of_comp_eq {f g : Zon → ℝ} (hf : f ∈ AZ) (hg : g ∈ AZ) (h : f ∘ jO = g ∘ jO) : f = g :=
  (continuous_of_mem hf).ext_on dense_ZonOSet (continuous_of_mem hg)
    (fun x hx => congrFun h ⟨x, hx⟩)

open Classical in
/-- a chosen extension to `[-1,1]` of an element of `𝒜` (junk `0` outside). -/
noncomputable def liftO (f' : ZonO → ℝ) : Zon → ℝ :=
  if h : f' ∈ AO then h.choose else 0

lemma liftO_spec {f' : ZonO → ℝ} (h : f' ∈ AO) : liftO f' ∈ AZ ∧ liftO f' ∘ jO = f' := by
  unfold liftO
  simp only [h, ↓reduceDIte]
  exact ⟨h.choose_spec.1, h.choose_spec.2.symm⟩

lemma liftO_comp {f : Zon → ℝ} (hf : f ∈ AZ) : liftO (f ∘ jO) = f :=
  eq_of_comp_eq (liftO_spec (comp_mem_AO hf)).1 hf (liftO_spec (comp_mem_AO hf)).2

/-- `Γ` of the open triple. -/
noncomputable def GO (f' g' : ZonO → ℝ) : ZonO → ℝ := GZ (liftO f') (liftO g') ∘ jO

/-- `L` of the open triple. -/
noncomputable def LO (f' : ZonO → ℝ) : ZonO → ℝ := LZ (liftO f') ∘ jO

lemma GO_comp {f g : Zon → ℝ} (hf : f ∈ AZ) (hg : g ∈ AZ) :
    GO (f ∘ jO) (g ∘ jO) = GZ f g ∘ jO := by
  simp only [GO, liftO_comp hf, liftO_comp hg]

lemma LO_comp {f : Zon → ℝ} (hf : f ∈ AZ) : LO (f ∘ jO) = LZ f ∘ jO := by
  simp only [LO, liftO_comp hf]

lemma LO_mem {f' : ZonO → ℝ} (h : f' ∈ AO) : LO f' ∈ AO := by
  obtain ⟨f, hf, rfl⟩ := h
  rw [LO_comp hf]
  exact comp_mem_AO (LZ_mem hf)

lemma GO_mem {f' g' : ZonO → ℝ} (hf : f' ∈ AO) (hg : g' ∈ AO) : GO f' g' ∈ AO := by
  obtain ⟨f, hf, rfl⟩ := hf
  obtain ⟨g, hg, rfl⟩ := hg
  rw [GO_comp hf hg]
  exact comp_mem_AO (GZ_mem hf hg)

lemma comp_mem_AO' {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    {f : Fin k → ZonO → ℝ} (hf : ∀ i, f i ∈ AO) : (fun x => ψ (fun i => f i x)) ∈ AO := by
  choose g hg hgf using hf
  have : f = fun i => g i ∘ jO := funext hgf
  subst this
  exact comp_mem_AO (comp_mem_AZ ψ hψ hg)

/-- the restriction as a continuous linear map `L^p(μZ) → L^p(μO)`. -/
lemma continuous_restrL (p : ℝ≥0∞) [Fact (1 ≤ p)] : Continuous (restrL p) := by
  have : Isometry (restrL p) := AddMonoidHomClass.isometry_of_norm _ (norm_restrL p)
  exact this.continuous

/-- **The open zonal sphere as a Diffusion Markov Triple.** -/
noncomputable abbrev oT : MarkovTriple.BGL.DiffusionTriple ZonO where
  μ := μO
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := A0O
  measurable := fun f hf => by
    obtain ⟨g, hg, rfl⟩ := (mem_A0O.1 hf)
    exact ((continuous_of_mem hg).comp continuous_jO).measurable
  bounded := fun f hf => by
    obtain ⟨g, hg, rfl⟩ := (mem_A0O.1 hf)
    obtain ⟨C, hC⟩ := bounded_of_mem hg
    exact ⟨C, fun x => hC _⟩
  memLp := fun f hf p _ _ => by
    obtain ⟨g, hg, rfl⟩ := (mem_A0O.1 hf)
    obtain ⟨C, hC⟩ := bounded_of_mem hg
    exact MemLp.of_bound (((continuous_of_mem hg).comp continuous_jO).aestronglyMeasurable) C
      (Eventually.of_forall fun x => by simpa using hC _)
  dense := fun p hp hp' => by
    have h1 := dense_Lp p hp'
    have h2 := (restrL_surjective p).denseRange.dense_image (continuous_restrL p) h1
    refine h2.mono ?_
    rintro _ ⟨u, ⟨f, hf, huf⟩, rfl⟩
    refine ⟨f ∘ jO, comp_mem_AO hf, ?_⟩
    filter_upwards [coeFn_restrL p u, ae_comap_jO huf] with x h1 h2
    rw [h1]; exact h2
  comp_mem := fun k ψ hψ _ f hf => comp_mem_AO' ψ hψ (fun i => mem_A0O.1 (hf i))
  exhaustion := ⟨fun _ _ => 1, fun _ => AO.one_mem,
    fun _ => Filter.Eventually.of_forall fun _ => le_refl _,
    Filter.Eventually.of_forall fun _ => tendsto_const_nhds⟩
  Γ := GO
  L := LO
  Γ_mem := fun f hf g hg => GO_mem (mem_A0O.1 hf) (mem_A0O.1 hg)
  L_mem := fun f hf => LO_mem (mem_A0O.1 hf)
  Γ_symm := fun f hf_ g hg_ => by
    obtain ⟨f, hf, rfl⟩ := mem_A0O.1 hf_
    obtain ⟨g, hg, rfl⟩ := mem_A0O.1 hg_
    exact Filter.Eventually.of_forall fun x => by
      rw [GO_comp hf hg, GO_comp hg hf]; simp only [Function.comp_apply, GZ_symm]
  Γ_add := fun f hf_ f' hf'_ g hg_ => by
    obtain ⟨f, hf, rfl⟩ := mem_A0O.1 hf_
    obtain ⟨f', hf', rfl⟩ := mem_A0O.1 hf'_
    obtain ⟨g, hg, rfl⟩ := mem_A0O.1 hg_
    have e : (f ∘ jO) + (f' ∘ jO) = (f + f') ∘ jO := rfl
    exact Filter.Eventually.of_forall fun x => by
      rw [e, GO_comp (add_mem hf hf') hg]
      show GZ (f + f') g (jO x) = GO (f ∘ jO) (g ∘ jO) x + GO (f' ∘ jO) (g ∘ jO) x
      rw [GO_comp hf hg, GO_comp hf' hg]
      exact GZ_add hf hf' _
  Γ_smul := fun c f hf_ g hg_ => by
    obtain ⟨f, hf, rfl⟩ := mem_A0O.1 hf_
    obtain ⟨g, hg, rfl⟩ := mem_A0O.1 hg_
    have e : c • (f ∘ jO) = (c • f) ∘ jO := rfl
    exact Filter.Eventually.of_forall fun x => by
      rw [e, GO_comp (AZ.smul_mem hf c) hg]
      show GZ (c • f) g (jO x) = c * GO (f ∘ jO) (g ∘ jO) x
      rw [GO_comp hf hg]
      exact GZ_smul c hf _
  Γ_nonneg := fun f hf_ => by
    obtain ⟨f, hf, rfl⟩ := mem_A0O.1 hf_
    exact Filter.Eventually.of_forall fun x => by
      rw [GO_comp hf hf]
      simp only [Function.comp_apply, GZ_apply, dG, Pi.zero_apply]
      exact mul_self_nonneg _
  diffusion := fun k ψ hψ _ f hf_ g hg_ => by
    choose f0 hf0 hff using fun i => mem_A0O.1 (hf_ i)
    obtain ⟨g, hg, rfl⟩ := mem_A0O.1 hg_
    have ef : f = fun i => f0 i ∘ jO := funext hff
    subst ef
    have e : (fun x => ψ (fun i => (f0 i ∘ jO) x)) = (fun y => ψ (fun i => f0 i y)) ∘ jO := rfl
    exact Filter.Eventually.of_forall fun x => by
      show GO (fun x => ψ (fun i => (f0 i ∘ jO) x)) (g ∘ jO) x = _
      rw [e, GO_comp (comp_mem_AZ ψ hψ hf0) hg]
      simp only [Function.comp_apply]
      rw [GZ_comp ψ hψ hf0 g (jO x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [GO_comp (hf0 i) hg]
      rfl
  ibp := fun f hf_ g hg_ => by
    obtain ⟨f, hf, rfl⟩ := mem_A0O.1 hf_
    obtain ⟨g, hg, rfl⟩ := mem_A0O.1 hg_
    have e1 : (fun x => (g ∘ jO) x * LO (f ∘ jO) x) = fun x => (fun y => g y * LZ f y) (jO x) := by
      funext x; rw [LO_comp hf]; rfl
    have e2 : GO (f ∘ jO) (g ∘ jO) = fun x => GZ f g (jO x) := by
      rw [GO_comp hf hg]; rfl
    show ∫ x, (g ∘ jO) x * LO (f ∘ jO) x ∂μO = -∫ x, GO (f ∘ jO) (g ∘ jO) x ∂μO
    rw [e1, e2, integral_comp_jO (fun y => g y * LZ f y), integral_comp_jO (GZ f g)]
    exact ibpZ hf hg
  integral_L := fun f hf_ => by
    obtain ⟨f, hf, rfl⟩ := mem_A0O.1 hf_
    have e : LO (f ∘ jO) = fun x => LZ f (jO x) := by rw [LO_comp hf]; rfl
    show ∫ x, LO (f ∘ jO) x ∂μO = 0
    rw [e, integral_comp_jO (LZ f)]
    exact integral_LZ hf

end MarkovTriple.BGL.Instances.SphereOpen
