import Mathlib
import MarkovTriple.BGL.Instances.SphereOpen.Basic

/-!
# Full support of `μO` (R17 Noncompact, N9): every non-empty open subset of `(-1,1)` has positive measure,
so the reference measure is not concentrated on a smaller set (the instance is not degenerate).
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.SphereOpen

open MarkovTriple.BGL.Instances.Sphere

lemma ν_pos_of_open {W : Set ℝ} (hW : IsOpen W) {θ₀ : ℝ} (hθ₀ : θ₀ ∈ W) (h0 : 0 < θ₀)
    (hπ : θ₀ < π) : 0 < ν W := by
  by_contra hcon
  have hz : ν W = 0 := le_antisymm (not_lt.1 hcon) bot_le
  unfold ν at hz
  rw [withDensity_apply_eq_zero' measurable_wθ.aemeasurable] at hz
  set O : Set ℝ := W ∩ Ioo 0 π with hO
  have hOo : IsOpen O := hW.inter isOpen_Ioo
  have hOpos : 0 < volume O := hOo.measure_pos volume ⟨θ₀, hθ₀, h0, hπ⟩
  have hsub : O ⊆ {x | wθ x ≠ 0} ∩ W ∩ Ioc 0 π := by
    intro θ hθ
    refine ⟨⟨?_, hθ.1⟩, ⟨hθ.2.1, hθ.2.2.le⟩⟩
    have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi hθ.2.1 hθ.2.2
    show wθ θ ≠ 0
    unfold wθ
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have hm : MeasurableSet {x | wθ x ≠ 0} := measurable_wθ (measurableSet_singleton 0).compl
  have h1 : (volume.restrict (Ioc 0 π)) ({x | wθ x ≠ 0} ∩ W) = 0 := hz
  rw [Measure.restrict_apply (hm.inter hW.measurableSet)] at h1
  have h2 : volume O ≤ volume (({x | wθ x ≠ 0} ∩ W) ∩ Ioc 0 π) := measure_mono hsub
  rw [h1] at h2
  exact absurd hOpos (not_lt.2 (le_of_le_of_eq h2 (by rfl)))

/-- **full support**: every non-empty open subset of `(-1,1)` has positive `μO`-measure. -/
theorem μO_pos_of_open {U : Set ZonO} (hU : IsOpen U) (hne : U.Nonempty) : 0 < μO U := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hS : IsOpen ZonOSet := by
    have : ZonOSet = Subtype.val ⁻¹' Ioo (-1 : ℝ) 1 := rfl
    rw [this]; exact isOpen_Ioo.preimage continuous_subtype_val
  have hV : IsOpen (jO '' U) := (hS.isOpenMap_subtype_val) U hU
  have e : μO U = μZ (jO '' U) := measurableEmbedding_jO.comap_apply μZ U
  rw [e]
  unfold μZ
  rw [Measure.map_apply continuous_cosZ.measurable hV.measurableSet]
  have hx : (x₀ : Zon).1 ∈ Ioo (-1 : ℝ) 1 := x₀.2
  refine ν_pos_of_open (hV.preimage continuous_cosZ) (θ₀ := arccos (x₀ : Zon).1) ?_ ?_ ?_
  · show cosZ (arccos (x₀ : Zon).1) ∈ jO '' U
    have : cosZ (arccos (x₀ : Zon).1) = jO x₀ := by
      refine Subtype.ext ?_
      show cos (arccos (x₀ : Zon).1) = (x₀ : Zon).1
      exact Real.cos_arccos (x₀ : Zon).2.1 (x₀ : Zon).2.2
    rw [this]; exact ⟨x₀, hx₀, rfl⟩
  · exact Real.arccos_pos.2 hx.2
  · exact Real.arccos_lt_pi.2 hx.1

end MarkovTriple.BGL.Instances.SphereOpen
