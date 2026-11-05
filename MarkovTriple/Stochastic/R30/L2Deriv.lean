import Mathlib

/-!
# Round 30 (S), part 4: an `L²`-derivative from a pointwise derivative with a Lipschitz domination

If `σ ↦ G σ x` has derivative `D x` at `s` for a.e. `x`, with `|G σ x - G s x| ≤ bnd x |σ - s|` near `s`, `|D x| ≤ bnd x` and
`bnd ∈ L²(μ)`, then `σ ↦ [G σ] ∈ L²(μ)` has the strong derivative `[D]` at `s`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.Stochastic.R30

variable {α : Type*} [MeasurableSpace α]

lemma norm_toLp_sq' {μ : Measure α} {f : α → ℝ} (h : MemLp f 2 μ) :
    ‖h.toLp f‖ ^ 2 = ∫ x, f x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_toLp] with x hx
  simp [hx]

lemma norm_sq_eq_integral_coe {μ : Measure α} (v : Lp ℝ 2 μ) (g : α → ℝ) (hv : (v : α → ℝ) =ᵐ[μ] g) :
    ‖v‖ ^ 2 = ∫ x, g x ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hv] with x hx
  simp [hx]

theorem hasDerivAt_toLp {μ : Measure α} {G : ℝ → α → ℝ} {D bnd : α → ℝ} {s : ℝ}
    (hG : ∀ σ, MemLp (G σ) 2 μ) (hD : MemLp D 2 μ) (hbnd : Integrable (fun x => bnd x ^ 2) μ)
    (hpt : ∀ᵐ x ∂μ, HasDerivAt (fun σ => G σ x) (D x) s)
    (hlip : ∀ᶠ σ in 𝓝 s, ∀ᵐ x ∂μ, |G σ x - G s x| ≤ bnd x * |σ - s|)
    (hDb : ∀ᵐ x ∂μ, |D x| ≤ bnd x) :
    HasDerivAt (fun σ => (hG σ).toLp (G σ)) (hD.toLp D) s := by
  rw [hasDerivAt_iff_tendsto_slope_zero, tendsto_iff_norm_sub_tendsto_zero]
  set g : ℝ → α → ℝ := fun t x => t⁻¹ * (G (s + t) x - G s x) - D x with hg
  have hgmem : ∀ t, MemLp (g t) 2 μ := fun t => (((hG (s + t)).sub (hG s)).const_mul t⁻¹).sub hD
  have hsq : ∀ t : ℝ, ‖t⁻¹ • ((hG (s + t)).toLp (G (s + t)) - (hG s).toLp (G s)) - hD.toLp D‖ ^ 2 =
      ∫ x, g t x ^ 2 ∂μ := by
    intro t
    refine norm_sq_eq_integral_coe _ _ ?_
    filter_upwards [Lp.coeFn_sub (t⁻¹ • ((hG (s + t)).toLp (G (s + t)) - (hG s).toLp (G s))) (hD.toLp D),
      Lp.coeFn_smul t⁻¹ ((hG (s + t)).toLp (G (s + t)) - (hG s).toLp (G s)),
      Lp.coeFn_sub ((hG (s + t)).toLp (G (s + t))) ((hG s).toLp (G s)),
      (hG (s + t)).coeFn_toLp, (hG s).coeFn_toLp, hD.coeFn_toLp] with x h1 h2 h3 h4 h5 h6
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, h6]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h3]
    simp only [Pi.sub_apply]
    rw [h4, h5]
  have hint : Tendsto (fun t : ℝ => ∫ x, g t x ^ 2 ∂μ) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝[≠] (0 : ℝ))
      (F := fun t x => g t x ^ 2) (f := fun _ => (0 : ℝ)) (fun x => 4 * bnd x ^ 2)
      (Eventually.of_forall fun t => ((hgmem t).aestronglyMeasurable.pow 2))
      ?_ (hbnd.const_mul 4) ?_
    · simpa using this
    · -- domination
      have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), ∀ᵐ x ∂μ, |G (s + t) x - G s x| ≤ bnd x * |t| := by
        have : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ᵐ x ∂μ, |G (s + t) x - G s x| ≤ bnd x * |t| := by
          have h0 : Tendsto (fun t : ℝ => s + t) (𝓝 0) (𝓝 s) := by
            have := (tendsto_const_nhds (x := s) (f := 𝓝 (0 : ℝ))).add (tendsto_id (x := 𝓝 (0 : ℝ)))
            simpa using this
          filter_upwards [h0.eventually hlip] with t ht
          filter_upwards [ht] with x hx
          simpa using hx
        exact this.filter_mono nhdsWithin_le_nhds
      filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
      filter_upwards [ht, hDb] with x hx hDx
      have ht0' : t ≠ 0 := ht0
      have hpos : 0 < |t| := abs_pos.2 ht0'
      have h1 : |t⁻¹ * (G (s + t) x - G s x)| ≤ bnd x := by
        rw [abs_mul, abs_inv]
        calc |t|⁻¹ * |G (s + t) x - G s x| ≤ |t|⁻¹ * (bnd x * |t|) :=
              mul_le_mul_of_nonneg_left hx (by positivity)
          _ = bnd x := by field_simp
      have h2 : |g t x| ≤ 2 * bnd x := by
        simp only [hg]
        calc |t⁻¹ * (G (s + t) x - G s x) - D x| ≤ |t⁻¹ * (G (s + t) x - G s x)| + |D x| := abs_sub _ _
          _ ≤ 2 * bnd x := by linarith
      rw [Real.norm_eq_abs, abs_pow]
      calc |g t x| ^ 2 ≤ (2 * bnd x) ^ 2 := by
            apply pow_le_pow_left₀ (abs_nonneg _) h2
        _ = 4 * bnd x ^ 2 := by ring
    · filter_upwards [hpt] with x hx
      have h1 := (hasDerivAt_iff_tendsto_slope_zero.1 hx)
      have h2 : Tendsto (fun t : ℝ => g t x) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
        have := h1.sub_const (D x)
        simpa [hg, smul_eq_mul] using this
      simpa using h2.pow 2
  have hnorm : Tendsto (fun t : ℝ => ‖t⁻¹ • ((hG (s + t)).toLp (G (s + t)) - (hG s).toLp (G s)) -
      hD.toLp D‖) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h2 := (Real.continuous_sqrt.tendsto 0).comp hint
    rw [Real.sqrt_zero] at h2
    refine h2.congr fun t => ?_
    simp only [Function.comp]
    rw [← hsq t, Real.sqrt_sq (norm_nonneg _)]
  exact hnorm

/-- continuity of `σ ↦ [G σ] ∈ L²(μ)` from pointwise continuity and an `L²` domination -/
theorem continuousAt_toLp {μ : Measure α} {G : ℝ → α → ℝ} {bnd : α → ℝ} {s : ℝ}
    (hG : ∀ σ, MemLp (G σ) 2 μ) (hbnd : Integrable (fun x => bnd x ^ 2) μ)
    (hpt : ∀ᵐ x ∂μ, ContinuousAt (fun σ => G σ x) s)
    (hb : ∀ σ, ∀ᵐ x ∂μ, |G σ x| ≤ bnd x) :
    ContinuousAt (fun σ => (hG σ).toLp (G σ)) s := by
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have hsq : ∀ σ : ℝ, ‖(hG σ).toLp (G σ) - (hG s).toLp (G s)‖ ^ 2 = ∫ x, (G σ x - G s x) ^ 2 ∂μ := by
    intro σ
    refine norm_sq_eq_integral_coe _ _ ?_
    filter_upwards [Lp.coeFn_sub ((hG σ).toLp (G σ)) ((hG s).toLp (G s)), (hG σ).coeFn_toLp,
      (hG s).coeFn_toLp] with x h1 h2 h3
    rw [h1]
    simp only [Pi.sub_apply]
    rw [h2, h3]
  have hint : Tendsto (fun σ : ℝ => ∫ x, (G σ x - G s x) ^ 2 ∂μ) (𝓝 s) (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := 𝓝 s)
      (F := fun σ x => (G σ x - G s x) ^ 2) (f := fun _ => (0 : ℝ)) (fun x => 4 * bnd x ^ 2)
      (Eventually.of_forall fun σ => (((hG σ).sub (hG s)).aestronglyMeasurable.pow 2))
      ?_ (hbnd.const_mul 4) ?_
    · simpa using this
    · refine Eventually.of_forall fun σ => ?_
      filter_upwards [hb σ, hb s] with x h1 h2
      rw [Real.norm_eq_abs, abs_pow]
      calc |G σ x - G s x| ^ 2 ≤ (2 * bnd x) ^ 2 := by
            apply pow_le_pow_left₀ (abs_nonneg _)
            calc |G σ x - G s x| ≤ |G σ x| + |G s x| := abs_sub _ _
              _ ≤ 2 * bnd x := by linarith
        _ = 4 * bnd x ^ 2 := by ring
    · filter_upwards [hpt] with x hx
      have := (hx.tendsto.sub_const (G s x)).pow 2
      simpa using this
  have h2 := (Real.continuous_sqrt.tendsto 0).comp hint
  rw [Real.sqrt_zero] at h2
  refine h2.congr fun σ => ?_
  simp only [Function.comp]
  rw [← hsq σ, Real.sqrt_sq (norm_nonneg _)]

end MarkovTriple.Stochastic.R30
