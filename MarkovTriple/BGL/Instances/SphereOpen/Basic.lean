import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Curvature

/-!
# The open zonal sphere: state space `(-1,1)`, measure, `L^p` restriction (R17 Noncompact, N1-N2)

`ZonO = {x ∈ [-1,1] | -1 < x < 1}` (a non-compact space, homeomorphic to the open interval), `μO` the
restriction of the zonal probability measure `μZ` (the two poles are null).  `restrL p : L^p(μZ) → L^p(μO)`,
`u ↦ u ∘ val`, is a linear isometry, onto (so `L^p(μZ) ≅ L^p(μO)`).
Statements: `STATEMENTS_R17_Noncompact.md`.
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.SphereOpen

open MarkovTriple.BGL.Instances.Sphere

/-- the open interval inside `Zon = [-1,1]`. -/
def ZonOSet : Set Zon := {x | -1 < x.1 ∧ x.1 < 1}

/-- the non-compact state space `(-1,1)`. -/
abbrev ZonO : Type := ↥ZonOSet

/-- the inclusion `(-1,1) ⊂ [-1,1]`. -/
def jO : ZonO → Zon := Subtype.val

lemma measurableSet_ZonOSet : MeasurableSet ZonOSet := by
  have : ZonOSet = (Subtype.val ⁻¹' Ioo (-1 : ℝ) 1) := rfl
  rw [this]
  exact measurable_subtype_coe measurableSet_Ioo

lemma continuous_jO : Continuous jO := continuous_subtype_val

lemma measurableEmbedding_jO : MeasurableEmbedding jO :=
  MeasurableEmbedding.subtype_coe measurableSet_ZonOSet

lemma jO_injective : Function.Injective jO := Subtype.val_injective

lemma range_jO : Set.range jO = ZonOSet := Subtype.range_coe

/-- `(-1,1)` is dense in `[-1,1]`. -/
lemma dense_ZonOSet : Dense ZonOSet := by
  intro x
  have h1 : (Subtype.val '' ZonOSet : Set ℝ) = Ioo (-1) 1 := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩; exact hz
    · intro hy
      exact ⟨⟨y, hy.1.le, hy.2.le⟩, hy, rfl⟩
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, h1, closure_Ioo (by norm_num)]
  exact ⟨x.2.1, x.2.2⟩

/-- **The state space is not compact** (N1). -/
theorem not_compactSpace_ZonO : ¬ CompactSpace ZonO := by
  intro hc
  have h1 : IsCompact (Set.range jO) := isCompact_range continuous_jO
  have h2 : IsClosed ZonOSet := by rw [← range_jO]; exact h1.isClosed
  have h3 : ZonOSet = Set.univ := by
    have := dense_ZonOSet.closure_eq
    rwa [h2.closure_eq] at this
  have h4 : (⟨1, by norm_num, le_rfl⟩ : Zon) ∈ ZonOSet := by rw [h3]; trivial
  exact lt_irrefl _ h4.2

/-- the reference measure of the open triple: restriction of `μZ` to `(-1,1)`. -/
noncomputable def μO : Measure ZonO := μZ.comap jO

lemma ν_absolutelyContinuous : ν ≪ (volume : Measure ℝ) := by
  unfold ν
  exact (withDensity_absolutelyContinuous _ _).trans
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)

/-- the two poles are `μZ`-null. -/
lemma μZ_compl : μZ ZonOSetᶜ = 0 := by
  have hm : MeasurableSet (ZonOSetᶜ) := measurableSet_ZonOSet.compl
  unfold μZ
  rw [Measure.map_apply continuous_cosZ.measurable hm]
  refine ν_absolutelyContinuous ?_
  refine Set.Countable.measure_zero ?_ _
  refine (Set.countable_range (fun k : ℤ => (k : ℝ) * π)).mono ?_
  intro θ hθ
  have hθ' : ¬ (-1 < cos θ ∧ cos θ < 1) := hθ
  have hsin : sin θ = 0 := by
    have h := sin_sq_add_cos_sq θ
    have hc : cos θ ^ 2 = 1 := by
      by_cases h1 : -1 < cos θ
      · have : 1 ≤ cos θ := by by_contra h2; exact hθ' ⟨h1, not_le.1 h2⟩
        have h3 := cos_le_one θ
        have : cos θ = 1 := le_antisymm h3 this
        rw [this]; norm_num
      · have : cos θ ≤ -1 := not_lt.1 h1
        have h3 := neg_one_le_cos θ
        have : cos θ = -1 := le_antisymm this h3
        rw [this]; norm_num
    have : sin θ ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this
  obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.1 hsin
  exact ⟨k, hk⟩

lemma ae_mem_ZonOSet : ∀ᵐ x ∂μZ, x ∈ ZonOSet := by
  rw [ae_iff]; exact μZ_compl

lemma measurePreserving_jO : MeasurePreserving jO μO μZ := by
  refine ⟨measurableEmbedding_jO.measurable, ?_⟩
  unfold μO
  rw [measurableEmbedding_jO.map_comap, range_jO]
  exact Measure.restrict_eq_self_of_ae_mem ae_mem_ZonOSet

instance : IsProbabilityMeasure μO := by
  refine ⟨?_⟩
  have := measurePreserving_jO.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simpa using this

/-- `a.e.` statements for `μZ` pull back to `μO`. -/
lemma ae_comap_jO {p : Zon → Prop} (h : ∀ᵐ x ∂μZ, p x) : ∀ᵐ x ∂μO, p (jO x) :=
  measurePreserving_jO.quasiMeasurePreserving.ae h

/-- integrals transfer. -/
lemma integral_comp_jO (f : Zon → ℝ) : ∫ x, f (jO x) ∂μO = ∫ y, f y ∂μZ :=
  measurePreserving_jO.integral_comp measurableEmbedding_jO f

end MarkovTriple.BGL.Instances.SphereOpen
