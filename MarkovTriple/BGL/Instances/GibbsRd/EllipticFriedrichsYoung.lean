import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsKernel

/-!
# Young's inequality in `L²` for a non-negative `L¹` kernel (R16, Friedrichs step)

Statement Y1 of `STATEMENTS_R16_Friedrichs.md`: `∫ (k ⋆ G)² ≤ (∫ k)² ∫ G²` for `k ≥ 0` integrable and `G ≥ 0` continuous with
compact support (Cauchy–Schwarz against the measure `k(t) dt`, then Fubini; Gilbarg–Trudinger (7.?) / Evans §C.5 proof of Thm 7 (i)).
Only continuous compactly supported `G` is needed (so that every convolution integral exists).
-/

open MeasureTheory Filter Topology
open scoped ENNReal Convolution

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

variable {d : ℕ}

/-- Cauchy–Schwarz for the measure `k dt`: `(∫ k g)² ≤ (∫ k) (∫ k g²)`. -/
lemma cs_weighted {k g : (Fin d → ℝ) → ℝ} (hk0 : ∀ t, 0 ≤ k t) (hk : Integrable k)
    (h1 : Integrable (fun t => k t * g t)) (h2 : Integrable (fun t => k t * g t ^ 2)) :
    (∫ t, k t * g t) ^ 2 ≤ (∫ t, k t) * ∫ t, k t * g t ^ 2 := by
  set c := ∫ t, k t with hc
  set A1 := ∫ t, k t * g t with hA1
  set A2 := ∫ t, k t * g t ^ 2 with hA2
  have hc0 : 0 ≤ c := integral_nonneg hk0
  have hq : ∀ s : ℝ, 0 ≤ A2 - 2 * s * A1 + s ^ 2 * c := by
    intro s
    have e : (fun t => k t * (g t - s) ^ 2) = fun t => k t * g t ^ 2 - 2 * s * (k t * g t) + s ^ 2 * k t := by
      funext t; ring
    have i3 : Integrable (fun t => k t * (g t - s) ^ 2) := by
      rw [e]; exact (h2.sub (h1.const_mul _)).add (hk.const_mul _)
    have := integral_nonneg (μ := (volume : Measure (Fin d → ℝ))) (f := fun t => k t * (g t - s) ^ 2)
      (fun t => mul_nonneg (hk0 t) (sq_nonneg (g t - s)))
    have j1 : Integrable (fun t => k t * g t ^ 2 - 2 * s * (k t * g t)) := h2.sub (h1.const_mul _)
    have j2 : Integrable (fun t => s ^ 2 * k t) := hk.const_mul _
    have j3 : Integrable (fun t => 2 * s * (k t * g t)) := h1.const_mul _
    have k1 := integral_add j1 j2
    have k2 := integral_sub h2 j3
    have k3 : ∫ t, 2 * s * (k t * g t) = 2 * s * A1 := integral_const_mul _ _
    have k4 : ∫ t, s ^ 2 * k t = s ^ 2 * c := integral_const_mul _ _
    rw [e, k1, k2, k3, k4] at this
    linarith
  rcases hc0.eq_or_lt with h0 | hpos
  · have hz : k =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hk0 hk).1 h0.symm
    have : A1 = 0 := by
      rw [hA1]
      exact integral_eq_zero_of_ae (by filter_upwards [hz] with t ht; simp [ht])
    rw [this, ← h0]; simp
  · have := hq (A1 / c)
    have e : A2 - 2 * (A1 / c) * A1 + (A1 / c) ^ 2 * c = A2 - A1 ^ 2 / c := by field_simp; ring
    rw [e] at this
    have : A1 ^ 2 / c ≤ A2 := by linarith
    rw [div_le_iff₀ hpos] at this
    linarith

section
variable {k G : (Fin d → ℝ) → ℝ}

lemma conv_integrable (hk : Integrable k) (hG : Continuous G) (hGc : HasCompactSupport G) (x : Fin d → ℝ) :
    Integrable (fun t => k t * G (x - t)) := by
  have hb : Continuous (fun t => G (x - t)) := hG.comp (continuous_const.sub continuous_id)
  obtain ⟨C, hC⟩ := hG.bounded_above_of_compact_support hGc
  refine hk.mul_bdd (c := C) (hb.aestronglyMeasurable) (Eventually.of_forall fun t => ?_)
  simpa using hC (x - t)

/-- pointwise Jensen/Cauchy–Schwarz for `k ⋆ G` -/
lemma conv_sq_le (hk0 : ∀ t, 0 ≤ k t) (hk : Integrable k) (hG : Continuous G) (hGc : HasCompactSupport G)
    (x : Fin d → ℝ) :
    (∫ t, k t * G (x - t)) ^ 2 ≤ (∫ t, k t) * ∫ t, k t * G (x - t) ^ 2 := by
  have hG2 : Continuous (fun y => G y ^ 2) := hG.pow 2
  have hG2c : HasCompactSupport (fun y => G y ^ 2) := hGc.comp_left (g := fun z : ℝ => z ^ 2) (by simp)
  exact cs_weighted hk0 hk (conv_integrable hk hG hGc x) (conv_integrable hk hG2 hG2c x)

/-- **Y1**: `∫ (k ⋆ G)² ≤ (∫ k)² ∫ G²` bound for the pointwise square-function: the integral of the dominating function. -/
lemma integral_conv_sq (hk : Integrable k) (hG : Continuous G) (hGc : HasCompactSupport G) :
    Integrable (fun x => ∫ t, k t * G (x - t) ^ 2) ∧
      ∫ x, (∫ t, k t * G (x - t) ^ 2) = (∫ t, k t) * ∫ y, G y ^ 2 := by
  have hG2 : Continuous (fun y => G y ^ 2) := hG.pow 2
  have hG2c : HasCompactSupport (fun y => G y ^ 2) := hGc.comp_left (g := fun z : ℝ => z ^ 2) (by simp)
  have hGi : Integrable (fun y => G y ^ 2) := hG2.integrable_of_hasCompactSupport hG2c
  refine ⟨hk.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hGi, ?_⟩
  have := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) (μ := (volume : Measure (Fin d → ℝ)))
    (ν := volume) hk hGi
  simpa [convolution_def] using this

end

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
