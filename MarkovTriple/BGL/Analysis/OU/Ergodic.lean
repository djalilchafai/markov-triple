import MarkovTriple.BGL.Analysis.OU.Esa

/-! # OU (Part 9): ergodicity -/

open MeasureTheory Filter Topology ProbabilityTheory Polynomial
open scoped ENNReal NNReal Real InnerProductSpace

namespace MarkovTriple.Sanity.OU

lemma hh_zero : hh 0 = fun _ => 1 := by
  funext x; simp [hh, He_zero]

/-- symmetric IBP for a Hermite function against a test function -/
lemma ibp_hh {g : ℝ → ℝ} (hg : g ∈ A₀) (m : ℕ) :
    ∫ x, g x * Lo (hh m) x ∂γ = ∫ x, hh m x * Lo g x ∂γ := by
  have h1 := ibp_cs_left (hh_sm m) hg
  have h2 := ibp_cs_right (hh_sm m) hg
  rw [h1, h2]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  ring

theorem ou_ergodic_aux : ∀ u : Lp ℝ 2 γ,
    (∃ f : ℕ → ℝ → ℝ, (∀ n, f n ∈ A₀) ∧
      Tendsto (fun n => eLpNorm (f n - (u : ℝ → ℝ)) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (Lo (f n)) 2 γ) atTop (𝓝 0)) →
    ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[γ] fun _ => c := by
  intro u ⟨f, hf, h1, h2⟩
  have hu := Lp.memLp u
  -- orthogonality to `hL m` for `m ≥ 1`
  have horth : ∀ m : ℕ, 1 ≤ m → ⟪hL m, u⟫_ℝ = 0 := by
    intro m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    set uf : ℕ → Lp ℝ 2 γ := fun n => (memLp_A₀ (hf n) 2).toLp (f n) with huf
    have hlim : Tendsto uf atTop (𝓝 u) := by
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
      refine h1.congr fun n => ?_
      exact eLpNorm_congr_ae ((((memLp_A₀ (hf n) 2).coeFn_toLp).sub (EventuallyEq.refl _ _)).symm)
    have ha : Tendsto (fun n => ⟪hL m, uf n⟫_ℝ) atTop (𝓝 ⟪hL m, u⟫_ℝ) :=
      ((continuous_const.inner continuous_id).tendsto u).comp hlim
    -- the same sequence tends to `0`
    set vL : ℕ → Lp ℝ 2 γ := fun n => (memLp_A₀ (A₀.Lo_mem (hf n)) 2).toLp (Lo (f n)) with hvL
    have hv0 : Tendsto (fun n => ‖vL n‖) atTop (𝓝 0) := by
      have : ∀ n, ‖vL n‖ = (eLpNorm (Lo (f n)) 2 γ).toReal := fun n => by
        simp [hvL, Lp.norm_toLp]
      simp_rw [this]
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
      simpa [Function.comp_def] using this
    have heq : ∀ n, ⟪hL m, uf n⟫_ℝ = -(1 / (m : ℝ)) * ⟪hL m, vL n⟫_ℝ := by
      intro n
      rw [huf, hvL]
      simp only []
      rw [hL, inner_toLp, inner_toLp]
      have := ibp_hh (hf n) m
      rw [Lo_hh] at this
      have e : ∫ x, hh m x * f n x ∂γ = -(1 / (m : ℝ)) * ∫ x, f n x * (-(m : ℝ) * hh m x) ∂γ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        field_simp
      rw [e, this]
    have hb : Tendsto (fun n => ⟪hL m, uf n⟫_ℝ) atTop (𝓝 0) := by
      have hn : ∀ n, |⟪hL m, uf n⟫_ℝ| ≤ (1 / (m : ℝ)) * (‖hL m‖ * ‖vL n‖) := by
        intro n
        rw [heq n, abs_mul, abs_neg, abs_of_pos (by positivity)]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (by positivity)
      have hz : Tendsto (fun n => (1 / (m : ℝ)) * (‖hL m‖ * ‖vL n‖)) atTop (𝓝 0) := by
        simpa using (hv0.const_mul ‖hL m‖).const_mul (1 / (m : ℝ))
      exact squeeze_zero_norm (fun n => by simpa using hn n) hz
    exact tendsto_nhds_unique ha hb
  -- the constant
  set c : ℝ := ⟪hL 0, u⟫_ℝ with hc
  refine ⟨c, ?_⟩
  have hw : u - c • hL 0 = 0 := by
    refine eq_zero_of_orth_hL fun n => ?_
    rw [inner_sub_right, inner_smul_right]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hc, real_inner_self_eq_norm_sq, orthonormal_hL.1 0]; simp
    · rw [horth n hn, orthonormal_hL.inner_eq_zero (by omega : n ≠ 0)]; simp
  have hae : (u : ℝ → ℝ) =ᵐ[γ] ⇑(c • hL 0) := by
    have := congrArg (fun w : Lp ℝ 2 γ => (w : ℝ → ℝ)) (sub_eq_zero.1 hw)
    exact Filter.EventuallyEq.of_eq (by simpa using this) |> fun h => h
  filter_upwards [hae, Lp.coeFn_smul c (hL 0), (hh_memLp 0).coeFn_toLp] with x h1 h2 h3
  rw [h1, h2, Pi.smul_apply, hL, h3, hh_zero]; simp

end MarkovTriple.Sanity.OU
