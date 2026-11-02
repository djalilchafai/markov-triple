import Mathlib

/-! # Bakry–Émery (Phase 4b): the real-variable Gronwall argument

If `e' = q` on `(0,∞)`, `q' ≥ -2ρ q` (i.e. the "Fisher information" `i = -q` satisfies
`i' ≤ -2ρ i`), `e, q` are continuous on `[0,∞)` and `e(t) → 0` as `t → ∞`, then
`i(s) ≤ e^{-2ρ s} i(0)` and `e(0) ≤ i(0)/(2ρ)`. -/

open Filter Topology Set

namespace MarkovTriple.BE

theorem fisher_decay {q : ℝ → ℝ} {ρ : ℝ}
    (hq0 : ContinuousOn q (Ici 0))
    (hdq : ∀ s, 0 < s → ∃ q', HasDerivAt q q' s ∧ -2 * ρ * q s ≤ q') :
    ∀ s, 0 ≤ s → -q s ≤ Real.exp (-2 * ρ * s) * (-q 0) := by
  set h : ℝ → ℝ := fun s => Real.exp (2 * ρ * s) * (-q s) with hh
  have hcont : ContinuousOn h (Ici 0) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn.mul hq0.neg
  have hder : ∀ s ∈ interior (Ici (0 : ℝ)), ∃ d, HasDerivAt h d s ∧ d ≤ 0 := by
    intro s hs
    rw [interior_Ici] at hs
    obtain ⟨q', hq', hle⟩ := hdq s hs
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (2 * ρ * s)) (Real.exp (2 * ρ * s) * (2 * ρ)) s := by
      have := ((hasDerivAt_id s).const_mul (2 * ρ)).exp
      simpa using this
    have h2 := h1.mul hq'.neg
    refine ⟨_, h2, ?_⟩
    have hp := Real.exp_pos (2 * ρ * s)
    have := mul_le_mul_of_nonneg_left hle hp.le
    simp only [Pi.neg_apply]
    nlinarith [this]
  have hdiff : DifferentiableOn ℝ h (interior (Ici (0 : ℝ))) := fun s hs =>
    (let ⟨_, hd, _⟩ := hder s hs; hd.differentiableAt.differentiableWithinAt)
  have hanti : AntitoneOn h (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) hcont hdiff ?_
    intro s hs
    obtain ⟨d, hd, hle⟩ := hder s hs
    rw [hd.deriv]; exact hle
  intro s hs
  have := hanti (a := 0) (b := s) (by simp) hs hs
  simp only [hh, mul_zero, Real.exp_zero, one_mul] at this
  have hp := Real.exp_pos (2 * ρ * s)
  have e1 : Real.exp (-2 * ρ * s) * Real.exp (2 * ρ * s) = 1 := by
    rw [← Real.exp_add]; simp
  calc -q s = Real.exp (-2 * ρ * s) * (Real.exp (2 * ρ * s) * (-q s)) := by
        rw [← mul_assoc, e1, one_mul]
    _ ≤ Real.exp (-2 * ρ * s) * (-q 0) :=
        mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

/-- **Entropy–Fisher inequality from the decay of the Fisher information.** -/
theorem ent_le_of_decay {e q : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (he : ContinuousOn e (Ici 0)) (hq0 : ContinuousOn q (Ici 0))
    (hde : ∀ s, 0 < s → HasDerivAt e (q s) s)
    (hdq : ∀ s, 0 < s → ∃ q', HasDerivAt q q' s ∧ -2 * ρ * q s ≤ q')
    (hlim : Tendsto e atTop (𝓝 0)) :
    e 0 ≤ -q 0 / (2 * ρ) := by
  have hdec := fisher_decay hq0 hdq
  set i0 : ℝ := -q 0 with hi0
  set g : ℝ → ℝ := fun s => e s - (i0 / (2 * ρ)) * Real.exp (-2 * ρ * s) with hg
  have hgc : ContinuousOn g (Ici 0) :=
    he.sub (continuousOn_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn)
  have hgd : ∀ s ∈ interior (Ici (0 : ℝ)), ∃ d, HasDerivAt g d s ∧ 0 ≤ d := by
    intro s hs
    rw [interior_Ici] at hs
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-2 * ρ * s)) (Real.exp (-2 * ρ * s) * (-2 * ρ)) s := by
      have := ((hasDerivAt_id s).const_mul (-2 * ρ)).exp
      simpa using this
    have h2 := (hde s hs).sub (h1.const_mul (i0 / (2 * ρ)))
    refine ⟨_, h2, ?_⟩
    have := hdec s hs.le
    have e1 : i0 / (2 * ρ) * (Real.exp (-2 * ρ * s) * (-2 * ρ)) = - (i0 * Real.exp (-2 * ρ * s)) := by
      field_simp
    rw [e1]
    linarith
  have hgm : MonotoneOn g (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) hgc ?_ ?_
    · exact fun s hs => (let ⟨_, hd, _⟩ := hgd s hs; hd.differentiableAt.differentiableWithinAt)
    · intro s hs
      obtain ⟨d, hd, hle⟩ := hgd s hs
      rw [hd.deriv]; exact hle
  have hT : Tendsto g atTop (𝓝 0) := by
    have h3 : Tendsto (fun s : ℝ => Real.exp (-2 * ρ * s)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      exact tendsto_id.const_mul_atTop_of_neg (by linarith)
    have := hlim.sub (h3.const_mul (i0 / (2 * ρ)))
    simp only [mul_zero, sub_zero] at this
    exact this
  have hle : g 0 ≤ 0 := by
    refine ge_of_tendsto hT ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact hgm (by simp) hs hs
  simp only [hg, mul_zero, Real.exp_zero, mul_one] at hle
  linarith

end MarkovTriple.BE
