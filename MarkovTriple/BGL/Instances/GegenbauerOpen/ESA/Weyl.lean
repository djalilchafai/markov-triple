import Mathlib

/-!
# Weyl limit-point argument for `(p v')' = W v`, `p = (1-x²)²`, `W = 1-x²`, on `(-1,1)`

See `STATEMENTS_R23_G1.md`.  Let `F = p v'`, so `F' = W v` and `Y = F v` has `Y' = W v² + F²/p ≥ 0`.
If `∫ W v² < ∞`, then `Y ≤ 0` on `(0,1)` (otherwise `v ≳ 1/(1-x)` and `W v²` is not integrable), and by the reflection
`x ↦ -x`, `Y ≥ 0`; so `Y = 0` and `v = 0`.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.ESA

lemma not_integrableOn_div_one_sub {r : ℝ} (hr : r < 1) {c : ℝ} (hc : 0 < c) :
    ¬ IntegrableOn (fun x : ℝ => c / (1 - x)) (Ioo r 1) := by
  intro h
  have h1 : IntervalIntegrable (fun x : ℝ => c / (1 - x)) volume r 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le hr.le).2 h
  have h2 : IntervalIntegrable (fun x : ℝ => (1 - x)⁻¹) volume r 1 := by
    have := h1.const_mul (c⁻¹)
    refine this.congr (fun x hx => ?_)
    by_cases h0 : 1 - x = 0
    · simp [h0]
    · field_simp
  have h3 := h2.comp_sub_left 1
  have h4 : IntervalIntegrable (fun x : ℝ => x⁻¹) volume (1 - r) 0 := by
    refine (by simpa using h3 : IntervalIntegrable (fun x : ℝ => (1 - (1 - x))⁻¹) volume (1 - r) 0).congr
      (fun x _ => ?_)
    simp [sub_sub_cancel]
  rcases intervalIntegrable_inv_iff.1 h4 with h5 | h5
  · linarith
  · apply h5
    rw [mem_uIcc]
    right
    exact ⟨le_rfl, by linarith⟩

/-- the core of the argument: positive `F v` on `[t₀,1)` with `F t₀ > 0` contradicts integrability. -/
lemma weyl_core (v F : ℝ → ℝ)
    (hv : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt v (F x / (1 - x ^ 2) ^ 2) x)
    (hF : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt F ((1 - x ^ 2) * v x) x)
    (hint : IntegrableOn (fun x => (1 - x ^ 2) * v x ^ 2) (Ioo (0:ℝ) 1))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0:ℝ) 1) (hF0 : 0 < F t₀)
    (hY : ∀ x ∈ Ico t₀ 1, 0 < F x * v x) : False := by
  have hsub : Ico t₀ 1 ⊆ Ioo (0:ℝ) 1 := fun x hx => ⟨ht₀.1.trans_le hx.1, hx.2⟩
  have hFc : ContinuousOn F (Ico t₀ 1) := fun x hx => (hF x (hsub hx)).continuousAt.continuousWithinAt
  have hvc : ContinuousOn v (Ico t₀ 1) := fun x hx => (hv x (hsub hx)).continuousAt.continuousWithinAt
  -- `F > 0` on `[t₀,1)`
  have hFpos : ∀ x ∈ Ico t₀ 1, 0 < F x := by
    intro x hx
    by_contra hneg
    push Not at hneg
    have hxt : t₀ < x := by
      rcases hx.1.eq_or_lt with h | h
      · rw [← h] at hneg; linarith
      · exact h
    have hcont : ContinuousOn F (Icc t₀ x) :=
      hFc.mono fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hx.2⟩
    obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hxt.le hcont ⟨hneg, hF0.le⟩
    have := hY c ⟨hc.1, lt_of_le_of_lt hc.2 hx.2⟩
    rw [hc0] at this; simp at this
  have hvpos : ∀ x ∈ Ico t₀ 1, 0 < v x := fun x hx =>
    (mul_pos_iff_of_pos_left (hFpos x hx)).1 (hY x hx)
  -- `F` is monotone on `[t₀,1)`
  have hFmono : MonotoneOn F (Ico t₀ 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico t₀ 1) hFc ?_ ?_
    · intro x hx
      rw [interior_Ico] at hx
      exact (hF x (hsub (Ioo_subset_Ico_self hx))).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      have hx' : x ∈ Ioo (0:ℝ) 1 := hsub (Ioo_subset_Ico_self hx)
      rw [(hF x hx').deriv]
      have := hvpos x (Ioo_subset_Ico_self hx)
      have : 0 ≤ 1 - x ^ 2 := by nlinarith [hx'.1, hx'.2]
      positivity
  set f₀ := F t₀ with hf₀
  have hFge : ∀ x ∈ Ico t₀ 1, f₀ ≤ F x := fun x hx =>
    hFmono ⟨le_rfl, ht₀.2⟩ hx hx.1
  -- `φ x = v x - (f₀/4)/(1-x)` is monotone
  set φ : ℝ → ℝ := fun x => v x - f₀ / 4 / (1 - x) with hφ
  have hφd : ∀ x ∈ Ioo t₀ 1, HasDerivAt φ (F x / (1 - x ^ 2) ^ 2 - f₀ / 4 / (1 - x) ^ 2) x := by
    intro x hx
    have hx0 : x ∈ Ioo (0:ℝ) 1 := hsub (Ioo_subset_Ico_self hx)
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1) x := (hasDerivAt_id x).const_sub 1
    have hne : (1 - x) ≠ 0 := by linarith [hx.2]
    have h2 := (h1.inv hne).const_mul (f₀ / 4)
    have h3 := (hv x hx0).sub h2
    refine h3.congr_deriv ?_
    field_simp
  have hφmono : MonotoneOn φ (Ico t₀ 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ico t₀ 1) ?_ ?_ ?_
    · intro x hx
      have hne : (1 - x) ≠ 0 := by linarith [hx.2]
      refine ((hvc x hx).sub ?_)
      exact (continuousAt_const.div (continuousAt_const.sub continuousAt_id)
        hne).continuousWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      exact (hφd x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Ico] at hx
      rw [(hφd x hx).deriv]
      have hx0 : x ∈ Ioo (0:ℝ) 1 := hsub (Ioo_subset_Ico_self hx)
      have hpos : 0 < 1 - x := by linarith [hx.2]
      have hp : (1 - x ^ 2) ^ 2 ≤ 4 * (1 - x) ^ 2 := by
        have : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
        rw [this, mul_pow]
        have : (1 + x) ^ 2 ≤ 4 := by nlinarith [hx0.1, hx0.2]
        nlinarith [sq_nonneg (1 - x)]
      have hp0 : 0 < (1 - x ^ 2) ^ 2 := by
        have : 0 < 1 - x ^ 2 := by nlinarith [hx0.1, hx0.2]
        positivity
      have hFx := hFge x (Ioo_subset_Ico_self hx)
      have hf0 : 0 < f₀ := hF0
      have : f₀ / 4 / (1 - x) ^ 2 ≤ f₀ / (1 - x ^ 2) ^ 2 := by
        rw [div_div, div_le_div_iff₀ (by positivity) hp0]
        nlinarith
      have h2 : f₀ / (1 - x ^ 2) ^ 2 ≤ F x / (1 - x ^ 2) ^ 2 :=
        div_le_div_of_nonneg_right hFx hp0.le
      linarith
  -- `v ≥ (f₀/8)/(1-x)` near `1`
  set K : ℝ := |φ t₀| + 1 with hK
  have hK0 : 0 < K := by positivity
  have hf0 : 0 < f₀ := hF0
  set r : ℝ := max t₀ (1 - f₀ / (8 * K)) with hr
  have hrt : t₀ ≤ r := le_max_left _ _
  have hr1 : r < 1 := by
    have : 0 < f₀ / (8 * K) := by positivity
    exact max_lt ht₀.2 (by linarith)
  have hlow : ∀ x ∈ Ioo r 1, f₀ / 8 / (1 - x) ≤ v x := by
    intro x hx
    have hxI : x ∈ Ico t₀ 1 := ⟨hrt.trans hx.1.le, hx.2⟩
    have h1 : φ t₀ ≤ φ x := hφmono ⟨le_rfl, ht₀.2⟩ hxI hxI.1
    have hpos : 0 < 1 - x := by linarith [hx.2]
    have h2 : 1 - x < f₀ / (8 * K) := by
      have := lt_of_le_of_lt (le_max_right t₀ (1 - f₀ / (8 * K))) hx.1
      linarith
    have h3 : K < f₀ / 8 / (1 - x) := by
      rw [lt_div_iff₀ hpos]
      have : (1 - x) * (8 * K) < f₀ := by
        rw [lt_div_iff₀ (by positivity)] at h2; linarith
      linarith
    have h4 : -|φ t₀| ≤ φ t₀ := neg_abs_le _
    simp only [hφ] at h1
    have h5 : f₀ / 4 / (1 - x) = 2 * (f₀ / 8 / (1 - x)) := by field_simp; ring
    simp only [hφ] at h4
    rw [h5] at h1
    linarith
  -- non-integrability
  have hc : 0 < (f₀ / 8) ^ 2 := by positivity
  apply not_integrableOn_div_one_sub hr1 hc
  have hint' : IntegrableOn (fun x => (1 - x ^ 2) * v x ^ 2) (Ioo r 1) :=
    hint.mono_set (fun x hx => ⟨ht₀.1.trans_le (hrt.trans hx.1.le), hx.2⟩)
  refine hint'.mono' ?_ ?_
  · exact (measurable_const.div (measurable_const.sub measurable_id)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hpos : 0 < 1 - x := by linarith [hx.2]
    have hx0 : 0 < x := ht₀.1.trans_le (hrt.trans hx.1.le)
    have hv1 := hlow x hx
    have hw : 1 - x ≤ 1 - x ^ 2 := by nlinarith [hx.2]
    have hv0 : 0 < f₀ / 8 / (1 - x) := by positivity
    have hsq : (f₀ / 8 / (1 - x)) ^ 2 ≤ v x ^ 2 := by
      exact pow_le_pow_left₀ hv0.le hv1 2
    rw [Real.norm_of_nonneg (by positivity)]
    calc (f₀ / 8) ^ 2 / (1 - x) = (1 - x) * (f₀ / 8 / (1 - x)) ^ 2 := by field_simp
      _ ≤ (1 - x ^ 2) * v x ^ 2 := by
        apply mul_le_mul hw hsq (by positivity) (by nlinarith [hx.2])

lemma Y_mono (v F : ℝ → ℝ) {a b : ℝ} (hs : Ioo a b ⊆ Ioo (-1:ℝ) 1)
    (hv : ∀ x ∈ Ioo a b, HasDerivAt v (F x / (1 - x ^ 2) ^ 2) x)
    (hF : ∀ x ∈ Ioo a b, HasDerivAt F ((1 - x ^ 2) * v x) x) :
    MonotoneOn (fun x => F x * v x) (Ioo a b) := by
  have hYd : ∀ x ∈ Ioo a b, HasDerivAt (fun x => F x * v x)
      ((1 - x ^ 2) * v x * v x + F x * (F x / (1 - x ^ 2) ^ 2)) x :=
    fun x hx => (hF x hx).mul (hv x hx)
  refine monotoneOn_of_deriv_nonneg (convex_Ioo a b) ?_ ?_ ?_
  · intro x hx; exact (hYd x hx).continuousAt.continuousWithinAt
  · intro x hx; rw [interior_Ioo] at hx
    exact (hYd x hx).differentiableAt.differentiableWithinAt
  · intro x hx; rw [interior_Ioo] at hx
    rw [(hYd x hx).deriv]
    have h1 : 0 < 1 - x ^ 2 := by
      have := hs hx; nlinarith [this.1, this.2]
    have : 0 ≤ F x * (F x / (1 - x ^ 2) ^ 2) := by
      rw [← mul_div_assoc]; exact div_nonneg (mul_self_nonneg _) (sq_nonneg _)
    nlinarith [mul_self_nonneg (v x)]

theorem weyl_end (v F : ℝ → ℝ)
    (hv : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt v (F x / (1 - x ^ 2) ^ 2) x)
    (hF : ∀ x ∈ Ioo (0:ℝ) 1, HasDerivAt F ((1 - x ^ 2) * v x) x)
    (hint : IntegrableOn (fun x => (1 - x ^ 2) * v x ^ 2) (Ioo (0:ℝ) 1)) :
    ∀ t ∈ Ioo (0:ℝ) 1, F t * v t ≤ 0 := by
  intro t₀ ht₀
  by_contra hcon
  push Not at hcon
  have hYmono := Y_mono v F (a := 0) (b := 1) (fun x hx => ⟨by linarith [hx.1], hx.2⟩) hv hF
  have hYge : ∀ x ∈ Ico t₀ 1, 0 < F x * v x := fun x hx =>
    hcon.trans_le (hYmono ht₀ ⟨ht₀.1.trans_le hx.1, hx.2⟩ hx.1)
  rcases lt_or_gt_of_ne (show F t₀ ≠ 0 by intro h; rw [h] at hcon; simp at hcon) with hneg | hpos
  · refine weyl_core (fun x => -v x) (fun x => -F x) ?_ ?_ ?_ ht₀ (by simpa using hneg) ?_
    · intro x hx; simpa [neg_div] using (hv x hx).fun_neg
    · intro x hx; simpa using (hF x hx).fun_neg
    · simpa using hint
    · intro x hx; simpa using hYge x hx
  · exact weyl_core v F hv hF hint ht₀ hpos hYge

theorem weyl (v F : ℝ → ℝ)
    (hv : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt v (F x / (1 - x ^ 2) ^ 2) x)
    (hF : ∀ x ∈ Ioo (-1:ℝ) 1, HasDerivAt F ((1 - x ^ 2) * v x) x)
    (hint : IntegrableOn (fun x => (1 - x ^ 2) * v x ^ 2) (Ioo (-1:ℝ) 1)) :
    ∀ x ∈ Ioo (-1:ℝ) 1, v x = 0 := by
  have hsub : Ioo (0:ℝ) 1 ⊆ Ioo (-1:ℝ) 1 := fun x hx => ⟨by linarith [hx.1], hx.2⟩
  -- positive end
  have h1 := weyl_end v F (fun x hx => hv x (hsub hx)) (fun x hx => hF x (hsub hx))
    (hint.mono_set hsub)
  -- reflected end
  have h2 := weyl_end (fun x => v (-x)) (fun x => -F (-x))
    (by
      intro x hx
      have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have := (hv (-x) hx').comp x (hasDerivAt_neg x)
      refine this.congr_deriv ?_
      simp [neg_div])
    (by
      intro x hx
      have hx' : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
      have := ((hF (-x) hx').comp x (hasDerivAt_neg x)).neg
      refine this.congr_deriv ?_
      simp)
    (by
      have h0 : IntegrableOn (fun x : ℝ => (1 - x ^ 2) * v x ^ 2) (Ioo (-1:ℝ) 0) :=
        hint.mono_set fun x hx => ⟨hx.1, by linarith [hx.2]⟩
      have := (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg
        (volume : Measure ℝ)) (Homeomorph.neg ℝ).measurableEmbedding).2 h0
      have e : (fun x : ℝ => -x) ⁻¹' Ioo (-1:ℝ) 0 = Ioo 0 1 := by
        ext x; simp only [mem_preimage, mem_Ioo]; constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      rw [e] at this
      simpa [Function.comp_def] using this)
  -- `Y = F v` is monotone and `= 0`
  have hYm := Y_mono v F (a := -1) (b := 1) subset_rfl hv hF
  have hY0 : ∀ x ∈ Ioo (-1:ℝ) 1, F x * v x = 0 := by
    intro x hx
    have hup : ∀ y ∈ Ioo (-1:ℝ) 1, F y * v y ≤ 0 := by
      intro y hy
      by_cases hy0 : 0 < y
      · exact h1 y ⟨hy0, hy.2⟩
      · push Not at hy0
        exact (hYm hy ⟨by norm_num, by norm_num⟩ (by linarith)).trans
          (h1 (1/2) ⟨by norm_num, by norm_num⟩)
    have hlo : ∀ y ∈ Ioo (-1:ℝ) 1, 0 ≤ F y * v y := by
      intro y hy
      by_cases hy0 : y < 0
      · have := h2 (-y) ⟨by linarith [hy.1], by linarith [hy.1, hy0]⟩
        have hh : 0 < -y := by linarith
        simp only [neg_neg] at this
        nlinarith
      · push Not at hy0
        have := h2 (1/2) ⟨by norm_num, by norm_num⟩
        have h3 := hYm (show (-(1/2):ℝ) ∈ Ioo (-1:ℝ) 1 from ⟨by norm_num, by norm_num⟩) hy
          (by linarith)
        nlinarith
    exact le_antisymm (hup x hx) (hlo x hx)
  intro x hx
  have hYd := (hF x hx).mul (hv x hx)
  have hz : HasDerivAt (fun x => F x * v x) 0 x := by
    have : (fun x => F x * v x) =ᶠ[𝓝 x] fun _ => (0:ℝ) :=
      Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hx) fun y hy => hY0 y hy
    exact (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq this
  have hu := hYd.unique hz
  have hw : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have h3 : 0 ≤ F x * (F x / (1 - x ^ 2) ^ 2) := by
    rw [← mul_div_assoc]; exact div_nonneg (mul_self_nonneg _) (sq_nonneg _)
  have h4 : (1 - x ^ 2) * (v x * v x) = 0 := by nlinarith [mul_self_nonneg (v x)]
  rcases mul_eq_zero.1 h4 with h | h
  · exact absurd h hw.ne'
  · exact mul_self_eq_zero.1 h

end MarkovTriple.BGL.Instances.GegenbauerOpen.ESA
