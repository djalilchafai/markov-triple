import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Defs

/-!
# Solutions of `(1-x²)² U' = c`, `c ≠ 0`, are not in `L²(μ)` (R23-G2)

Weyl's limit-point mechanism at the endpoint `x = 1` for `λ = 3/2`: the second solution of `L u = 0` is
`U' = c/(1-x²)²`, so `U ≥ c/(8(1-x))` near `1` and `U² (1-x²) ≳ 1/(1-x)` is not integrable.
This gives ergodicity (S10) from interior regularity, without F10.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

lemma not_intervalIntegrable_inv_one_sub {ε : ℝ} (hε : 0 < ε) :
    ¬ IntervalIntegrable (fun x : ℝ => (1 - x)⁻¹) volume (1 - ε) 1 := by
  intro h
  have h' : IntervalIntegrable (fun x : ℝ => (fun y : ℝ => y⁻¹) (1 - x)) volume (1 - ε) 1 := h
  have e1 : (1 - ε) = 1 - ε := rfl
  have key := (IntervalIntegrable.comp_sub_left_iff (f := fun y : ℝ => y⁻¹) (a := ε) (b := 0) 1
    (by simp)).1 (by simpa using h')
  rw [intervalIntegrable_inv_iff] at key
  rcases key with h0 | h0
  · exact hε.ne' h0
  · exact h0 (by simp [hε.le])

/-- the `c > 0` case. -/
lemma go_not_integrable_sq_pos {U : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hU : ContDiffOn ℝ 1 U (Ioo (-1 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, (1 - x ^ 2) ^ 2 * deriv U x = c) :
    ¬ Integrable (fun x => U x ^ 2) goμ := by
  intro hint
  -- Step 1: `U - (c/4)/(1-x)` is monotone on `[0,1)`.
  set m : ℝ → ℝ := fun x => c / 4 * (1 - x)⁻¹ with hm
  have hUc : ContinuousOn U (Ioo (-1 : ℝ) 1) := hU.continuousOn
  have hUdiff : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt U (deriv U x) x := fun x hx =>
    ((hU.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hx)).hasDerivAt
  have hmd : ∀ x : ℝ, x ≠ 1 → HasDerivAt m (c / 4 * (1 - x)⁻¹ ^ 2) x := by
    intro x hx
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := by simpa using (hasDerivAt_id x).const_sub 1
    have h2 := h1.inv (sub_ne_zero.2 (Ne.symm hx))
    have h3 := h2.const_mul (c / 4)
    convert h3 using 1
    field_simp
  have hmono : MonotoneOn (fun x => U x - m x) (Ico 0 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico 0 1) ?_ ?_ ?_
    · refine ContinuousOn.sub (hUc.mono fun x hx => ⟨by linarith [hx.1], hx.2⟩) ?_
      intro x hx
      exact (hmd x hx.2.ne).continuousAt.continuousWithinAt
    · rw [interior_Ico]
      intro x hx
      exact ((hUdiff x ⟨by linarith [hx.1], hx.2⟩).sub (hmd x hx.2.ne)).differentiableAt.differentiableWithinAt
    · rw [interior_Ico]
      intro x hx
      have hx1 : x ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
      have e : deriv (fun x => U x - m x) x = deriv U x - c / 4 * (1 - x)⁻¹ ^ 2 :=
        ((hUdiff x hx1).sub (hmd x hx.2.ne)).deriv
      rw [e]
      have hpos : 0 < 1 - x := by linarith [hx.2]
      have hdx := hd x hx1
      have hw : 0 < (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
      have hder : deriv U x = c / (1 - x ^ 2) ^ 2 := by
        rw [eq_div_iff (by positivity)]; linarith
      rw [hder, sub_nonneg, inv_pow]
      have hle : (1 - x ^ 2) ^ 2 ≤ 4 * (1 - x) ^ 2 := by
        have : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
        rw [this, mul_pow]
        have : (1 + x) ^ 2 ≤ 4 := by nlinarith [hx.1, hx.2]
        nlinarith [sq_nonneg (1 - x)]
      calc c / 4 * ((1 - x) ^ 2)⁻¹ = c / (4 * (1 - x) ^ 2) := by field_simp
        _ ≤ c / (1 - x ^ 2) ^ 2 := by
          apply div_le_div_of_nonneg_left hc.le (by positivity) hle
  -- Step 2: the lower bound `U x ≥ (c/4)/(1-x) + U 0 - c/4` on `[0,1)`.
  have hlow : ∀ x ∈ Ico (0 : ℝ) 1, c / 4 * (1 - x)⁻¹ + (U 0 - c / 4) ≤ U x := by
    intro x hx
    have := hmono ⟨le_rfl, zero_lt_one⟩ hx hx.1
    simp only [hm] at this
    norm_num at this
    linarith
  -- Step 3: choose `ε`.
  set K : ℝ := c / 4 - U 0 with hK
  set ε : ℝ := min 1 (c / (8 * (|K| + 1))) with hε
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ c / (8 * (|K| + 1)) := min_le_right _ _
  have hbd : ∀ x ∈ Ioo (1 - ε) 1, c / 8 * (1 - x)⁻¹ ≤ U x := by
    intro x hx
    have hy : 0 < 1 - x := by linarith [hx.2]
    have hy2 : 1 - x < ε := by linarith [hx.1]
    have hl := hlow x ⟨by linarith [hx.1], hx.2⟩
    have h1 : (|K| + 1) ≤ c / (8 * ε) := by
      rw [le_div_iff₀ (by positivity)]
      rw [le_div_iff₀ (by positivity)] at hε2
      nlinarith
    have h2 : c / (8 * ε) ≤ c / (8 * (1 - x)) :=
      div_le_div_of_nonneg_left hc.le (by positivity) (by nlinarith)
    have h3 : K ≤ |K| := le_abs_self K
    have h4 : c / 8 * (1 - x)⁻¹ = c / (8 * (1 - x)) := by field_simp
    have h5 : c / 4 * (1 - x)⁻¹ = 2 * (c / 8 * (1 - x)⁻¹) := by ring
    rw [h5] at hl
    rw [h4] at hl ⊢
    nlinarith
  -- Step 4: integrability on `Ioo (1-ε) 1` of the density-weighted square.
  have hI : Integrable (fun x => (3 / 4 * (1 - x ^ 2)) * U x ^ 2)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    have h := (integrable_withDensity_iff_integrable_smul'
      (f := fun x : ℝ => ENNReal.ofReal (3 / 4 * (1 - x ^ 2))) (μ := volume.restrict (Ioo (-1 : ℝ) 1))
      measurable_goρ (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hint
    refine h.congr ?_
    refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
    have : 0 ≤ 3 / 4 * (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
    simp [ENNReal.toReal_ofReal this]
  have hJ : IntegrableOn (fun x => (3 / 4 * (1 - x ^ 2)) * U x ^ 2) (Ioo (1 - ε) 1) volume :=
    IntegrableOn.mono_set (s := Ioo (1 - ε) 1) (t := Ioo (-1 : ℝ) 1) hI (fun x hx => ⟨by linarith [hx.1], hx.2⟩)
  -- Step 5: comparison with `C/(1-x)`.
  set C : ℝ := 3 / 4 * (c / 8) ^ 2 with hC
  have hCpos : 0 < C := by positivity
  have hg : IntegrableOn (fun x : ℝ => C * (1 - x)⁻¹) (Ioo (1 - ε) 1) volume := by
    refine hJ.mono' ?_ ?_
    · exact (by fun_prop : Measurable fun x : ℝ => C * (1 - x)⁻¹).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
      have hy : 0 < 1 - x := by linarith [hx.2]
      have hx0 : 0 ≤ x := by linarith [hx.1]
      have hU1 := hbd x hx
      have hpos : 0 ≤ c / 8 * (1 - x)⁻¹ := by positivity
      have hsq : (c / 8 * (1 - x)⁻¹) ^ 2 ≤ U x ^ 2 := by nlinarith
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : 1 - x ≤ 1 - x ^ 2 := by nlinarith [hx.2]
      calc C * (1 - x)⁻¹ = 3 / 4 * (1 - x) * (c / 8 * (1 - x)⁻¹) ^ 2 := by
            rw [hC]; field_simp
        _ ≤ 3 / 4 * (1 - x ^ 2) * (c / 8 * (1 - x)⁻¹) ^ 2 := by gcongr
        _ ≤ 3 / 4 * (1 - x ^ 2) * U x ^ 2 := by
            apply mul_le_mul_of_nonneg_left hsq; nlinarith [hx.2]
  have hinv : IntegrableOn (fun x : ℝ => (1 - x)⁻¹) (Ioo (1 - ε) 1) volume := by
    have := hg.const_mul C⁻¹
    refine IntegrableOn.congr_fun this (fun x _ => ?_) measurableSet_Ioo
    rw [← mul_assoc, inv_mul_cancel₀ hCpos.ne', one_mul]
  have hii : IntervalIntegrable (fun x : ℝ => (1 - x)⁻¹) volume (1 - ε) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by linarith)).2 hinv
  exact not_intervalIntegrable_inv_one_sub hεpos hii

/-- `U` with `(1-x²)² U' = c ≠ 0` on `(-1,1)` is not in `L²(μ)` (`U²` is not `μ`-integrable). -/
theorem go_not_integrable_sq {U : ℝ → ℝ} {c : ℝ} (hc : c ≠ 0)
    (hU : ContDiffOn ℝ 1 U (Ioo (-1 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, (1 - x ^ 2) ^ 2 * deriv U x = c) :
    ¬ Integrable (fun x => U x ^ 2) goμ := by
  rcases lt_or_gt_of_ne hc with h | h
  · have hU' : ContDiffOn ℝ 1 (fun x => -U x) (Ioo (-1 : ℝ) 1) := hU.neg
    have := go_not_integrable_sq_pos (U := fun x => -U x) (c := -c) (by linarith) hU' (fun x hx => by
      have e : deriv (fun x => -U x) x = -deriv U x := deriv.neg
      rw [e, mul_neg, hd x hx])
    simpa using this
  · exact go_not_integrable_sq_pos h hU hd

end MarkovTriple.BGL.Instances.GegenbauerOpen
