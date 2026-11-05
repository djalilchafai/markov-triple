import Mathlib
import MarkovTriple.Stochastic.R28.FellerSGMeasurable
import MarkovTriple.Stochastic.R27.GoFeller

/-!
# Round 28 (M), part 4: restriction of `goFullTriple` to the compact interval `[-1,1]`

`goμ` lives on `[-1,1] ⊂ ℝ`.  On the compact subtype `GI = Icc (-1) 1` the measure `goμI = goμ.comap val` has full support
(unlike `goμ` on `ℝ`, R27 `goμ_not_isOpenPos`), and restriction `u ↦ u ∘ val` is a linear isometry equivalence
`L²(goμ) ≃ L²(goμI)`.  Conjugating the semigroup of `goFullTriple` by it gives `SGData GI` (`goSG`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R28

open MarkovTriple.BGL MarkovTriple.BGL.Instances.GegenbauerOpen MarkovTriple.Stochastic MarkovTriple.Stochastic.R27

/-- the compact interval `[-1,1]` as a type -/
abbrev GI : Type := Set.Icc (-1 : ℝ) 1

/-- `goμ` restricted to `[-1,1]` -/
noncomputable abbrev goμI : Measure GI := goμ.comap Subtype.val

lemma measurableEmbedding_gj : MeasurableEmbedding (Subtype.val : GI → ℝ) :=
  MeasurableEmbedding.subtype_coe measurableSet_Icc

lemma ae_mem_Icc_go : ∀ᵐ x ∂goμ, x ∈ Icc (-1 : ℝ) 1 :=
  ae_go fun _ hx => Ioo_subset_Icc_self hx

lemma measurePreserving_gj : MeasurePreserving (Subtype.val : GI → ℝ) goμI goμ := by
  refine ⟨measurableEmbedding_gj.measurable, ?_⟩
  rw [measurableEmbedding_gj.map_comap, Subtype.range_coe]
  exact Measure.restrict_eq_self_of_ae_mem ae_mem_Icc_go

lemma map_gj : goμI.map Subtype.val = goμ := measurePreserving_gj.map_eq

instance : IsProbabilityMeasure goμI := by
  refine ⟨?_⟩
  have := measurePreserving_gj.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet
  simpa using this

/-- a.e. statements transfer between `goμ` and `goμI` -/
lemma ae_goμ_iff {p : ℝ → Prop} : (∀ᵐ x ∂goμ, p x) ↔ ∀ᵐ x ∂goμI, p x.1 := by
  conv_lhs => rw [← map_gj]
  exact measurableEmbedding_gj.ae_map_iff

/-- `goμ` charges every open subset of `(-1,1)` -/
lemma goμ_pos_of_isOpen {W : Set ℝ} (hW : IsOpen W) (hne : (W ∩ Ioo (-1 : ℝ) 1).Nonempty) :
    0 < goμ (W ∩ Ioo (-1 : ℝ) 1) := by
  by_contra hcon
  have h0 : goμ (W ∩ Ioo (-1 : ℝ) 1) = 0 := le_antisymm (not_lt.1 hcon) bot_le
  have h1 := (withDensity_apply_eq_zero' (μ := volume.restrict (Ioo (-1 : ℝ) 1))
    measurable_goρ.aemeasurable (s := W ∩ Ioo (-1 : ℝ) 1)).1 h0
  have hpos : 0 < volume (W ∩ Ioo (-1 : ℝ) 1) := (hW.inter isOpen_Ioo).measure_pos volume hne
  have h2 : volume (W ∩ Ioo (-1 : ℝ) 1) = 0 := by
    refine measure_mono_null ?_ (by rwa [Measure.restrict_apply' measurableSet_Ioo] at h1)
    intro y hy
    refine ⟨⟨?_, hy⟩, hy.2⟩
    show ENNReal.ofReal (3 / 4 * (1 - y ^ 2)) ≠ 0
    exact (ENNReal.ofReal_pos.2 (by nlinarith [hy.2.1, hy.2.2])).ne'
  exact hpos.ne' h2

/-- **Full support of `goμI`** -/
instance : goμI.IsOpenPosMeasure := ⟨fun U hU hne h0 => by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨W, hW, rfl⟩ := isOpen_induced_iff.1 hU
  have hmem : x.1 ∈ closure (Ioo (-1 : ℝ) 1) := by
    rw [closure_Ioo (by norm_num)]; exact x.2
  obtain ⟨y, hyW, hyI⟩ := mem_closure_iff.1 hmem W hW hx
  have hpos := goμ_pos_of_isOpen hW ⟨y, hyW, hyI⟩
  have hsub : W ∩ Ioo (-1 : ℝ) 1 ⊆ Subtype.val '' (Subtype.val ⁻¹' W : Set GI) := by
    rintro z ⟨hzW, hzI⟩
    exact ⟨⟨z, Ioo_subset_Icc_self hzI⟩, hzW, rfl⟩
  have : goμI (Subtype.val ⁻¹' W) = goμ (Subtype.val '' (Subtype.val ⁻¹' W : Set GI)) :=
    measurableEmbedding_gj.comap_apply _ _
  have h1 : goμ (Subtype.val '' (Subtype.val ⁻¹' W : Set GI)) = 0 := this ▸ h0
  exact hpos.ne' (measure_mono_null hsub h1)⟩

/-- restriction `u ↦ u ∘ val`, as a linear isometry `L²(goμ) → L²(goμI)` -/
noncomputable def goRestrL : Lp ℝ 2 goμ →ₗᵢ[ℝ] Lp ℝ 2 goμI :=
  Lp.compMeasurePreservingₗᵢ ℝ Subtype.val measurePreserving_gj

lemma coeFn_goRestrL (u : Lp ℝ 2 goμ) : (goRestrL u : GI → ℝ) =ᵐ[goμI] (u : ℝ → ℝ) ∘ Subtype.val :=
  Lp.coeFn_compMeasurePreserving u measurePreserving_gj

lemma goRestrL_surjective : Function.Surjective goRestrL := by
  intro v
  have hvm : StronglyMeasurable (v : GI → ℝ) := Lp.stronglyMeasurable v
  set g : ℝ → ℝ := Function.extend Subtype.val (v : GI → ℝ) 0 with hg
  have hgm : Measurable g :=
    measurableEmbedding_gj.measurable_extend hvm.measurable measurable_const
  have hgj : g ∘ Subtype.val = (v : GI → ℝ) := funext fun x => Subtype.val_injective.extend_apply _ _ x
  have hmem : MemLp g 2 goμ := by
    have h := (Lp.memLp v)
    rw [← hgj] at h
    rw [← map_gj]
    exact (memLp_map_measure_iff (by rw [map_gj]; exact hgm.aestronglyMeasurable)
      measurableEmbedding_gj.measurable.aemeasurable).2 h
  refine ⟨hmem.toLp g, ?_⟩
  refine Lp.ext ?_
  filter_upwards [coeFn_goRestrL (hmem.toLp g),
    (ae_goμ_iff (p := fun x => (hmem.toLp g : ℝ → ℝ) x = g x)).1 hmem.coeFn_toLp] with x h1 h2
  rw [h1]
  show (hmem.toLp g : ℝ → ℝ) x.1 = _
  rw [h2, ← hgj]
  rfl

/-- **`L²(goμ) ≃ L²(goμI)` by restriction** -/
noncomputable def goRestr : Lp ℝ 2 goμ ≃ₗᵢ[ℝ] Lp ℝ 2 goμI :=
  LinearIsometryEquiv.ofSurjective goRestrL goRestrL_surjective

lemma goRestr_apply (u : Lp ℝ 2 goμ) : goRestr u = goRestrL u := rfl

lemma coeFn_goRestr (u : Lp ℝ 2 goμ) : (goRestr u : GI → ℝ) =ᵐ[goμI] (u : ℝ → ℝ) ∘ Subtype.val :=
  coeFn_goRestrL u

lemma goRestr_nonneg_iff (u : Lp ℝ 2 goμ) : 0 ≤ᵐ[goμI] (goRestr u : GI → ℝ) ↔ 0 ≤ᵐ[goμ] (u : ℝ → ℝ) := by
  have e := ae_goμ_iff (p := fun x => 0 ≤ (u : ℝ → ℝ) x)
  constructor
  · intro h
    refine e.2 ?_
    filter_upwards [h, coeFn_goRestr u] with x h1 h2
    rw [h2] at h1; exact h1
  · intro h
    filter_upwards [e.1 h, coeFn_goRestr u] with x h1 h2
    rw [h2]; exact h1

lemma goRestr_le_one_iff (u : Lp ℝ 2 goμ) :
    (goRestr u : GI → ℝ) ≤ᵐ[goμI] (1 : GI → ℝ) ↔ (u : ℝ → ℝ) ≤ᵐ[goμ] (1 : ℝ → ℝ) := by
  have e := ae_goμ_iff (p := fun x => (u : ℝ → ℝ) x ≤ 1)
  constructor
  · intro h
    refine e.2 ?_
    filter_upwards [h, coeFn_goRestr u] with x h1 h2
    rw [h2] at h1; exact h1
  · intro h
    filter_upwards [e.1 h, coeFn_goRestr u] with x h1 h2
    rw [h2]; exact h1

/-- the semigroup of `goFullTriple` on `L²(goμ)` -/
noncomputable abbrev goP (t : ℝ≥0) : Lp ℝ 2 goμ →L[ℝ] Lp ℝ 2 goμ :=
  goFullTriple.toDiffusionTriple.semigroup t

lemma goP_zero : goP 0 = 1 := goFullTriple.toDiffusionTriple.semigroup_zero

lemma goP_add (s t : ℝ≥0) : goP (s + t) = goP s * goP t := goFullTriple.toDiffusionTriple.semigroup_add s t

/-- the transported semigroup on `L²(goμI)` -/
noncomputable def goSemigroupI (t : ℝ≥0) : Lp ℝ 2 goμI →L[ℝ] Lp ℝ 2 goμI :=
  (goRestr.toContinuousLinearEquiv : Lp ℝ 2 goμ →L[ℝ] Lp ℝ 2 goμI).comp
    ((goP t).comp (goRestr.symm.toContinuousLinearEquiv : Lp ℝ 2 goμI →L[ℝ] Lp ℝ 2 goμ))

theorem goSemigroupI_apply (t : ℝ≥0) (u : Lp ℝ 2 goμI) : goSemigroupI t u = goRestr (goP t (goRestr.symm u)) := rfl

/-- **the transported semigroup is the conjugate of the original one** -/
theorem goSemigroupI_restr (t : ℝ≥0) (u : Lp ℝ 2 goμ) :
    goSemigroupI t (goRestr u) = goRestr (goFullTriple.toDiffusionTriple.semigroup t u) := by
  rw [goSemigroupI_apply, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- the semigroup data on the compact space -/
noncomputable def goSG : SGData GI where
  μ := goμI
  semigroup := goSemigroupI
  semigroup_zero := by
    ext u : 1
    rw [goSemigroupI_apply, goP_zero]
    simp
  semigroup_add := by
    intro s t
    ext u : 1
    show goRestr (goP (s + t) (goRestr.symm u)) = goRestr (goP s (goRestr.symm (goRestr (goP t (goRestr.symm u)))))
    rw [goP_add, LinearIsometryEquiv.symm_apply_apply]
    rfl
  continuous_semigroup_apply := fun u => by
    have := goFullTriple.toDiffusionTriple.continuous_semigroup_apply (goRestr.symm u)
    exact goRestr.continuous.comp this
  semigroup_isSelfAdjoint := fun t => by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro u v
    have hs := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      (goFullTriple.toDiffusionTriple.semigroup_isSelfAdjoint t)) (goRestr.symm u) (goRestr.symm v)
    show inner ℝ (goRestr (goP t (goRestr.symm u))) v = inner ℝ u (goRestr (goP t (goRestr.symm v)))
    conv_lhs => rw [← goRestr.apply_symm_apply v]
    conv_rhs => rw [← goRestr.apply_symm_apply u]
    rw [goRestr.inner_map_map, goRestr.inner_map_map]
    exact hs
  semigroup_nonneg := fun t u hu => by
    have h1 : 0 ≤ᵐ[goμ] ((goRestr.symm u : Lp ℝ 2 goμ) : ℝ → ℝ) :=
      (goRestr_nonneg_iff _).1 (by simpa using hu)
    have h2 : 0 ≤ᵐ[goμ] ((goP t (goRestr.symm u) : Lp ℝ 2 goμ) : ℝ → ℝ) :=
      goFullTriple.toDiffusionTriple.semigroup_nonneg t h1
    rw [goSemigroupI_apply]
    exact (goRestr_nonneg_iff _).2 h2
  semigroup_le_one := fun t u hu => by
    have h1 : ((goRestr.symm u : Lp ℝ 2 goμ) : ℝ → ℝ) ≤ᵐ[goμ] (1 : ℝ → ℝ) :=
      (goRestr_le_one_iff _).1 (by simpa using hu)
    have h2 : ((goP t (goRestr.symm u) : Lp ℝ 2 goμ) : ℝ → ℝ) ≤ᵐ[goμ] (1 : ℝ → ℝ) :=
      goFullTriple.toDiffusionTriple.semigroup_le_one t _ h1
    rw [goSemigroupI_apply]
    exact (goRestr_le_one_iff _).2 h2
  norm_semigroup_apply_le := fun t u => by
    show ‖goRestr (goP t (goRestr.symm u))‖ ≤ ‖u‖
    rw [goRestr.norm_map]
    have h : ‖goP t (goRestr.symm u)‖ ≤ ‖goRestr.symm u‖ := goFullTriple.toDiffusionTriple.norm_semigroup_apply_le t _
    exact h.trans (le_of_eq (goRestr.symm.norm_map u))

instance : IsFiniteMeasure goSG.μ := (inferInstance : IsFiniteMeasure goμI)

instance : goSG.μ.IsOpenPosMeasure := (inferInstance : goμI.IsOpenPosMeasure)

/-- the clamp retraction `ℝ → [-1,1]` -/
noncomputable def goRetr (x : ℝ) : GI := ⟨clamp1 x, clamp1_mem x⟩

lemma continuous_goRetr : Continuous goRetr := continuous_clamp1.subtype_mk _

lemma goRetr_val (x : GI) : goRetr x.1 = x := Subtype.ext (clamp1_eq x.2)

end MarkovTriple.Stochastic.R28
