import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Diffusion
import MarkovTriple.BGL.Frozen.Complete

/-!
# The Gegenbauer triple on `(-1,1)` with `C_c^∞((-1,1))` is NOT complete (S2a)

If `ζ ∈ 𝒜₀` and `(1-x²) ζ'(x)² ≤ c²` then `ζ' ≤ c/√(1-x²) = c · arcsin'`, so `c · arcsin - ζ` is monotone
and `ζ(x) ≤ c (arcsin x + π/2) ≤ c π`.  Hence `ζ_k ≤ π/(k+1) → 0`, contradicting `ζ_k → 1` a.e.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

lemma goΓ_continuous {ζ : ℝ → ℝ} (hζ : Lebesgue.Sm ζ) : Continuous (goΓ ζ ζ) := by
  have : Continuous (deriv ζ) := hζ.deriv'.continuous
  unfold goΓ
  fun_prop

/-- from `Γ ζ ≤ c²` a.e. to everywhere. -/
lemma goΓ_le_of_ae {ζ : ℝ → ℝ} (hζ : ζ ∈ goA₀) {c : ℝ}
    (hΓ : goΓ ζ ζ ≤ᵐ[goμ] fun _ => c ^ 2) : ∀ t, goΓ ζ ζ t ≤ c ^ 2 := by
  have h1 : ∀ᵐ t ∂(volume.restrict (Ioo (-1 : ℝ) 1)), goΓ ζ ζ t ≤ c ^ 2 := by
    have := (ae_withDensity_iff measurable_goρ).1 hΓ
    filter_upwards [this, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    exact ht (by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      nlinarith [hmem.1, hmem.2])
  have h2 : ∀ᵐ t ∂(volume : Measure ℝ), goΓ ζ ζ t ≤ c ^ 2 := by
    rw [ae_restrict_iff' measurableSet_Ioo] at h1
    filter_upwards [h1] with t ht
    by_cases hm : t ∈ Ioo (-1 : ℝ) 1
    · exact ht hm
    · have : deriv ζ t = 0 := zero_off_go (deriv_mem_goA₀ hζ) hm
      have hc : 0 ≤ c ^ 2 := sq_nonneg c
      simp only [goΓ, this]
      simpa using hc
  have hq : (fun t => max (goΓ ζ ζ t - c ^ 2) 0) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [h2] with t ht
    exact max_eq_right (by linarith)
  have hq' := (Continuous.ae_eq_iff_eq (volume : Measure ℝ)
    (((goΓ_continuous hζ.1).sub continuous_const).max continuous_const) continuous_const).1 hq
  intro t
  have := congrFun hq' t
  have h3 := le_max_left (goΓ ζ ζ t - c ^ 2) 0
  rw [Pi.sub_apply] at this
  linarith

/-- the key estimate: `ζ x ≤ c π`. -/
lemma go_le_of_Γ {ζ : ℝ → ℝ} (hζ : ζ ∈ goA₀) {c : ℝ} (hc : 0 ≤ c)
    (hΓ : ∀ t, goΓ ζ ζ t ≤ c ^ 2) (x : ℝ) : ζ x ≤ c * Real.pi := by
  have hpi := Real.pi_pos
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  swap
  · rw [zero_off_go hζ hx]; positivity
  have hζ0 : ζ (-1) = 0 := zero_off_go hζ (fun h => lt_irrefl _ h.1)
  set h : ℝ → ℝ := fun t => c * Real.arcsin t - ζ t with hh
  have hmono : MonotoneOn h (Icc (-1 : ℝ) x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (continuous_const.mul Real.continuous_arcsin |>.sub (goA₀_smooth hζ).continuous).continuousOn
    · rw [interior_Icc]
      intro t ht
      have hd : DifferentiableAt ℝ Real.arcsin t :=
        Real.differentiableAt_arcsin.2 ⟨by linarith [ht.1], by linarith [ht.2, hx.2]⟩
      exact ((hd.const_mul c).sub ((goA₀_smooth hζ).differentiable (by simp) t)).differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      have ht1 : t ∈ Ioo (-1 : ℝ) 1 := ⟨ht.1, ht.2.trans hx.2⟩
      have hd : DifferentiableAt ℝ Real.arcsin t :=
        Real.differentiableAt_arcsin.2 ⟨by linarith [ht.1], by linarith [ht.2, hx.2]⟩
      have hdζ : DifferentiableAt ℝ ζ t := (goA₀_smooth hζ).differentiable (by simp) t
      have : deriv h t = c * (1 / √(1 - t ^ 2)) - deriv ζ t := by
        rw [hh, deriv_fun_sub (hd.const_mul c) hdζ, deriv_const_mul _ hd, Real.deriv_arcsin]
      rw [this]
      have hs : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith [ht1.1, ht1.2])
      have hs2 : √(1 - t ^ 2) ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (by nlinarith [ht1.1, ht1.2])
      have hg := hΓ t
      simp only [goΓ] at hg
      have key : √(1 - t ^ 2) * deriv ζ t ≤ c := by
        by_contra hcon
        replace hcon := not_le.1 hcon
        nlinarith [mul_self_nonneg (deriv ζ t)]
      rw [mul_one_div, sub_nonneg, le_div_iff₀ hs]
      linarith
  have h1 := hmono ⟨le_refl _, by linarith [hx.1]⟩ ⟨by linarith [hx.1], le_refl _⟩ (by linarith [hx.1])
  simp only [hh, Real.arcsin_neg, Real.arcsin_one, hζ0] at h1
  have h2 := Real.arcsin_le_pi_div_two x
  nlinarith

/-- **S2a**: the Gegenbauer triple `(-1,1)`, `C_c^∞` is not complete (BGL Def. 3.3.9). -/
theorem go_not_complete : ¬ goDiff.IsComplete := by
  rintro ⟨ζ, hmem, -, -, hlim, hΓ⟩
  have hne : goμ ≠ 0 := IsProbabilityMeasure.ne_zero _
  have : (ae goμ).NeBot := ae_neBot.2 hne
  obtain ⟨x, hxlim⟩ := hlim.exists
  have hb : ∀ k : ℕ, ζ k x ≤ Real.pi * (1 / ((k : ℝ) + 1)) := fun k => by
    have := go_le_of_Γ (hmem k) (c := 1 / ((k : ℝ) + 1)) (by positivity)
      (goΓ_le_of_ae (hmem k) (hΓ k)) x
    linarith
  have hzero : Tendsto (fun k : ℕ => Real.pi * (1 / ((k : ℝ) + 1))) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul Real.pi
  have := le_of_tendsto_of_tendsto hxlim hzero (Filter.Eventually.of_forall hb)
  linarith

end MarkovTriple.BGL.Instances.GegenbauerOpen
