import Mathlib
import MarkovTriple.BGL.Instances.SphereOpen.Basic

/-!
# `L^p(μZ) ≅ L^p(μO)` by restriction (R17 Noncompact, N2)
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.SphereOpen

open MarkovTriple.BGL.Instances.Sphere

section
variable (p : ℝ≥0∞)

/-- restriction `u ↦ u ∘ val`, `L^p(μZ) → L^p(μO)`, as a real-linear map. -/
noncomputable def restrL : Lp ℝ p μZ →ₗ[ℝ] Lp ℝ p μO where
  toFun u := Lp.compMeasurePreserving jO measurePreserving_jO u
  map_add' u v := map_add (Lp.compMeasurePreserving jO measurePreserving_jO) u v
  map_smul' c u := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_compMeasurePreserving (c • u) measurePreserving_jO,
      ae_comap_jO (Lp.coeFn_smul c u),
      Lp.coeFn_smul c (Lp.compMeasurePreserving jO measurePreserving_jO u),
      Lp.coeFn_compMeasurePreserving u measurePreserving_jO] with x h1 h2 h3 h4
    simp only [RingHom.id_apply]
    rw [h3]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1]
    simp only [Function.comp_apply]
    rw [h2]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h4]
    rfl

lemma coeFn_restrL (u : Lp ℝ p μZ) : (restrL p u : ZonO → ℝ) =ᵐ[μO] (u : Zon → ℝ) ∘ jO :=
  Lp.coeFn_compMeasurePreserving u measurePreserving_jO

lemma norm_restrL (u : Lp ℝ p μZ) : ‖restrL p u‖ = ‖u‖ :=
  Lp.norm_compMeasurePreserving u measurePreserving_jO

lemma restrL_toLp {f : Zon → ℝ} (hf : MemLp f p μZ) (hf' : MemLp (f ∘ jO) p μO) :
    restrL p (hf.toLp f) = hf'.toLp (f ∘ jO) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_restrL p (hf.toLp f), ae_comap_jO hf.coeFn_toLp, hf'.coeFn_toLp] with x h1 h2 h3
  rw [h1, h3]
  exact h2

/-- the restriction is onto (every `p`): the poles are null. -/
lemma restrL_surjective : Function.Surjective (restrL p) := by
  intro v
  have hvm : StronglyMeasurable (v : ZonO → ℝ) := Lp.stronglyMeasurable v
  set g : Zon → ℝ := Function.extend jO (v : ZonO → ℝ) 0 with hg
  have hgm : Measurable g :=
    measurableEmbedding_jO.measurable_extend hvm.measurable measurable_const
  have hgj : g ∘ jO = (v : ZonO → ℝ) := funext fun x => jO_injective.extend_apply _ _ x
  have hmap : Measure.map jO μO = μZ := measurePreserving_jO.map_eq
  have hmem : MemLp g p μZ := by
    have h := (Lp.memLp v)
    rw [← hgj] at h
    rw [← hmap]
    exact (memLp_map_measure_iff (by rw [hmap]; exact hgm.aestronglyMeasurable)
      measurableEmbedding_jO.measurable.aemeasurable).2 h
  refine ⟨hmem.toLp g, ?_⟩
  refine Lp.ext ?_
  filter_upwards [coeFn_restrL p (hmem.toLp g), ae_comap_jO hmem.coeFn_toLp] with x h1 h2
  rw [h1]
  show (hmem.toLp g : Zon → ℝ) (jO x) = _
  rw [h2, ← hgj]
  rfl

end

end MarkovTriple.BGL.Instances.SphereOpen
