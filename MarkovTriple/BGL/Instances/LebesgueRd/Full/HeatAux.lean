import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDefs

/-!
# Heat flow on `ℝ^d`: auxiliary lemmas (Round 24, stream A, part H-a)

Generic (continuous, integrable / bounded) statements about `heatRd`, symmetry of `gam d`,
the density of `gam d`, and `L²`-norm formulas.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ ψ : (Fin d → ℝ) → ℝ}

lemma integrable_comp_gam (hc : Continuous φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C)
    (a : ℝ) (x : Fin d → ℝ) : Integrable (fun z => φ (x - a • z)) (gam d) :=
  Integrable.of_bound (C := C) (hc.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa using hC _)

lemma integrable_prod_comp_gam (hc : Continuous φ) (hi : Integrable φ volume) (a : ℝ) :
    Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => φ (p.1 - a • p.2)) (volume.prod (gam d)) := by
  have hm : AEStronglyMeasurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) => φ (p.1 - a • p.2))
      (volume.prod (gam d)) := (hc.comp (by fun_prop)).aestronglyMeasurable
  rw [integrable_prod_iff' hm]
  refine ⟨ae_of_all _ fun z => hi.comp_sub_right (a • z), ?_⟩
  have : (fun z : Fin d → ℝ => ∫ x, ‖φ (x - a • z)‖) = fun _ => ∫ x, ‖φ x‖ := by
    funext z
    exact integral_sub_right_eq_self (fun x => ‖φ x‖) (a • z)
  simp only [this]
  exact integrable_const _

lemma integrable_heat_gen (hc : Continuous φ) (hi : Integrable φ volume) (a : ℝ) :
    Integrable (heatRd a φ) volume :=
  (integrable_prod_comp_gam hc hi a).integral_prod_left

lemma integral_heat_gen (hc : Continuous φ) (hi : Integrable φ volume) (a : ℝ) :
    ∫ x, heatRd a φ x = ∫ x, φ x := by
  have := integral_integral_swap (μ := (volume : Measure (Fin d → ℝ))) (ν := gam d)
    (f := fun x z => φ (x - a • z)) (integrable_prod_comp_gam hc hi a)
  unfold heatRd
  rw [this]
  simp only [integral_sub_right_eq_self φ]
  simp

lemma abs_heat_le {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (a : ℝ) (x : Fin d → ℝ) :
    |heatRd a φ x| ≤ C := by
  have := norm_integral_le_of_norm_le_const (μ := gam d)
    (f := fun z => φ (x - a • z)) (C := C) (ae_of_all _ fun z => by simpa using hC _)
  simpa [heatRd] using this

lemma abs_heat_le_heat_abs (a : ℝ)
    (x : Fin d → ℝ) : |heatRd a φ x| ≤ heatRd a (fun y => |φ y|) x := by
  unfold heatRd
  have := norm_integral_le_integral_norm (μ := gam d) (f := fun z => φ (x - a • z))
  simpa using this

lemma sq_heat_le (hc : Continuous φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (a : ℝ) (x : Fin d → ℝ) :
    (heatRd a φ x) ^ 2 ≤ heatRd a (fun y => φ y ^ 2) x := by
  have hm : MemLp (fun z => φ (x - a • z)) 2 (gam d) :=
    MemLp.of_bound (C := C) (hc.comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun z => by simpa using hC _)
  have h := variance_nonneg (fun z => φ (x - a • z)) (gam d)
  rw [variance_eq_sub hm] at h
  simp only [heatRd]
  have e : (fun z => φ (x - a • z)) ^ 2 = fun z => φ (x - a • z) ^ 2 := by
    funext z; simp
  rw [e] at h
  have e2 : (gam d)[fun z => φ (x - a • z)] = ∫ z, φ (x - a • z) ∂(gam d) := rfl
  rw [e2] at h
  linarith

lemma gam_neg_mp : MeasurePreserving (fun z : Fin d → ℝ => -z) (gam d) (gam d) := by
  have := measurePreserving_pi (fun _ : Fin d => gaussianReal 0 1) (fun _ : Fin d => gaussianReal 0 1)
    (f := fun _ => fun z : ℝ => -z)
    (fun _ => ⟨measurable_neg, by simpa using gaussianReal_map_neg (μ := 0) (v := 1)⟩)
  exact this

lemma integral_gam_neg (f : (Fin d → ℝ) → ℝ) :
    ∫ z, f (-z) ∂(gam d) = ∫ z, f z ∂(gam d) :=
  gam_neg_mp.integral_comp (MeasurableEquiv.neg _).measurableEmbedding f

lemma norm_sq_toLp {f : (Fin d → ℝ) → ℝ} (h : MemLp f 2 (volume : Measure (Fin d → ℝ))) :
    ‖h.toLp f‖ ^ 2 = ∫ x, f x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_toLp] with x hx
  simp [hx]

/-! ### Density of `gam d` -/

/-- the density of `gam d` with respect to Lebesgue measure. -/
noncomputable def gdens (x : Fin d → ℝ) : ℝ := ∏ i, gaussianPDFReal 0 1 (x i)

lemma gdens_nonneg (x : Fin d → ℝ) : 0 ≤ gdens x :=
  Finset.prod_nonneg fun _ _ => gaussianPDFReal_nonneg _ _ _

lemma pdf_le (z : ℝ) : gaussianPDFReal 0 1 z ≤ (√(2 * Real.pi))⁻¹ := by
  rw [gaussianPDFReal_def]
  have : Real.exp (-(z - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : 0 ≤ (z - 0) ^ 2 := sq_nonneg _
    simp only [NNReal.coe_one, mul_one]
    have : 0 ≤ (z - 0) ^ 2 / 2 := by positivity
    rw [neg_div]; linarith
  simp only [NNReal.coe_one, mul_one] at this ⊢
  calc _ ≤ (√(2 * Real.pi))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

lemma gdens_le (x : Fin d → ℝ) : gdens x ≤ ((√(2 * Real.pi))⁻¹) ^ d := by
  unfold gdens
  calc ∏ i, gaussianPDFReal 0 1 (x i) ≤ ∏ _i : Fin d, (√(2 * Real.pi))⁻¹ :=
        Finset.prod_le_prod₀ (fun _ _ => gaussianPDFReal_nonneg _ _ _) (fun i _ => pdf_le _)
    _ = _ := by simp

lemma measurable_gdens : Measurable (gdens : (Fin d → ℝ) → ℝ) :=
  Finset.measurable_prod _ fun i _ => (measurable_gaussianPDFReal 0 1).comp (measurable_pi_apply i)

lemma integrable_gdens : Integrable (gdens : (Fin d → ℝ) → ℝ) volume := by
  rw [volume_pi]
  exact Integrable.fintype_prod (f := fun _ => gaussianPDFReal 0 1)
    (μ := fun _ : Fin d => (volume : Measure ℝ)) fun _ =>
    integrable_gaussianPDFReal 0 1

lemma gam_eq_withDensity :
    gam d = volume.withDensity (fun x => ENNReal.ofReal (gdens x)) := by
  show Measure.pi (fun _ : Fin d => gaussianReal 0 1) = _
  refine Measure.pi_eq (μ := fun _ : Fin d => gaussianReal 0 1) ?_
  intro s hs
  have hS : MeasurableSet (Set.pi Set.univ s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hS, ← ofReal_integral_eq_lintegral_ofReal integrable_gdens.restrict
    (ae_of_all _ gdens_nonneg), ← integral_indicator hS]
  have e : (Set.pi Set.univ s).indicator gdens =
      fun x => ∏ i, (s i).indicator (gaussianPDFReal 0 1) (x i) := by
    funext x
    classical
    simp only [Set.indicator, Set.mem_pi, Set.mem_univ, true_implies, gdens]
    rw [Finset.prod_ite_zero]
    simp
  rw [e, volume_pi, integral_fintype_prod_eq_prod (fun i => (s i).indicator (gaussianPDFReal 0 1)),
    ENNReal.ofReal_prod_of_nonneg]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [integral_indicator (hs i), gaussianReal_apply_eq_integral 0 one_ne_zero]
  · intro i _
    exact integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => gaussianPDFReal_nonneg _ _ _) _

lemma gam_absolutelyContinuous : gam d ≪ (volume : Measure (Fin d → ℝ)) := by
  rw [gam_eq_withDensity]; exact withDensity_absolutelyContinuous _ _

/-- sup bound `|heatRd a φ| ≤ (2π)^{-d/2} |a|^{-d} ‖φ‖₁` for `a ≠ 0`. -/
lemma abs_heat_le_sup (hi : Integrable φ volume) {a : ℝ} (ha : a ≠ 0) (x : Fin d → ℝ) :
    |heatRd a φ x| ≤ ((√(2 * Real.pi))⁻¹) ^ d * (|(a ^ d)⁻¹| * ∫ y, |φ y|) := by
  have h1 : |heatRd a φ x| ≤ ∫ z, |φ (x - a • z)| ∂(gam d) := by
    simpa [heatRd] using norm_integral_le_integral_norm (μ := gam d) (f := fun z => φ (x - a • z))
  have hint : Integrable (fun z : Fin d → ℝ => |φ (x - a • z)|) volume := by
    have := ((hi.comp_sub_left x).norm).comp_smul ha
    simpa using this
  have hint2 : Integrable (fun z : Fin d → ℝ => gdens z * |φ (x - a • z)|) volume :=
    hint.bdd_mul (f := gdens) measurable_gdens.aestronglyMeasurable
      (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (gdens_nonneg z)]
        exact gdens_le z) |>.congr (ae_of_all _ fun z => rfl)
  have h2 : ∫ z, |φ (x - a • z)| ∂(gam d) = ∫ z, gdens z * |φ (x - a • z)| := by
    rw [gam_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
      measurable_gdens.ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp [ENNReal.toReal_ofReal (gdens_nonneg _)]
  have h3 : ∫ z, gdens z * |φ (x - a • z)| ≤ ∫ z, ((√(2 * Real.pi))⁻¹) ^ d * |φ (x - a • z)| :=
    integral_mono hint2 (hint.const_mul _) fun z =>
      mul_le_mul_of_nonneg_right (gdens_le z) (abs_nonneg _)
  have h4 : ∫ z, ((√(2 * Real.pi))⁻¹) ^ d * |φ (x - a • z)|
      = ((√(2 * Real.pi))⁻¹) ^ d * (|(a ^ d)⁻¹| * ∫ y, |φ y|) := by
    rw [integral_const_mul]
    congr 1
    have := Measure.integral_comp_smul (μ := (volume : Measure (Fin d → ℝ)))
      (fun y : Fin d → ℝ => |φ (x - y)|) a
    simp only [Module.finrank_fin_fun] at this
    rw [this, integral_sub_left_eq_self (μ := (volume : Measure (Fin d → ℝ))) (fun y => |φ y|) x]
    simp
  linarith

end MarkovTriple.BGL.LebesgueRd
