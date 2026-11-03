import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE1

/-!
# E2, infrastructure: `L²_loc` stability of difference quotients, `L²`-norm/integral conversions (R16, elliptic half)

Statement: `STATEMENTS_R16_E2.md`, E2 (preliminary lemmas).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- `L²_loc` is stable under difference quotients -/
lemma locL2_dq {f : (Fin d → ℝ) → ℝ} (hf : LocL2 f) (i : Fin d) (t : ℝ) : LocL2 (dq i t f) := by
  intro K hK
  set K' : Set (Fin d → ℝ) := Metric.cthickening |t| K with hK'
  have hK'c : IsCompact K' := hK.cthickening
  have h1 : MemLp (dq i t (K'.indicator f)) 2 volume := memLp_dq (hf.memLp_indicator hK'c) i t
  have h2 : MemLp (dq i t (K'.indicator f)) 2 (volume.restrict K) := h1.restrict K
  refine h2.ae_eq ?_
  refine (ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
  have hx' : x + t • (Pi.single i 1 : Fin d → ℝ) ∈ K' := by
    refine Metric.mem_cthickening_of_dist_le _ x _ _ hx ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_single_le i)
  have hx0 : x ∈ K' := Metric.self_subset_cthickening _ hx
  simp [dq, Set.indicator_of_mem hx', Set.indicator_of_mem hx0]

/-- `∫ f² = ‖f‖₂²` -/
lemma sq_integral_eq {μ : Measure (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x ^ 2 ∂μ = (eLpNorm f 2 μ).toReal ^ 2 := by
  have h := hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)
  have e : ∫ x, ‖f x‖ ^ (ENNReal.toReal 2) ∂μ = ∫ x, f x ^ 2 ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofNat]
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  have h0 : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => by positivity
  rw [h, e, ENNReal.toReal_ofReal (by positivity)]
  simp only [ENNReal.toReal_ofNat]
  rw [← Real.rpow_natCast, ← Real.rpow_mul h0]
  norm_num

lemma eLpNorm_le_of_sq {μ : Measure (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 μ) {C : ℝ}
    (hC : 0 ≤ C) (h : ∫ x, f x ^ 2 ∂μ ≤ C ^ 2) : eLpNorm f 2 μ ≤ ENNReal.ofReal C := by
  rw [sq_integral_eq hf] at h
  rw [← ENNReal.ofReal_toReal hf.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal (abs_le_of_sq_le_sq' h hC |>.2)

lemma sq_le_of_eLpNorm {μ : Measure (Fin d → ℝ)} {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 μ) {C : ℝ}
    (hC : 0 ≤ C) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal C) : ∫ x, f x ^ 2 ∂μ ≤ C ^ 2 := by
  rw [sq_integral_eq hf]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  rw [ENNReal.toReal_ofReal hC] at this
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg this 2

lemma pderiv_eq_zero_off {ζ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hx : x ∉ tsupport ζ) (j : Fin d) :
    pderiv ζ j x = 0 := by
  have : x ∉ tsupport (fderiv ℝ ζ) := fun h => hx (tsupport_fderiv_subset ℝ h)
  have h0 := image_eq_zero_of_notMem_tsupport this
  simp [pderiv, h0]

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
