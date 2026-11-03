import Mathlib
import MarkovTriple.BGL.Theory.Interp.Nemytskii

/-!
# Product rule for `r ↦ ∫ k_r ψ(u_r)` (proof of BGL Thm 3.3.18, p. 164)
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

namespace MarkovTriple.BGL

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {ψ ψ' : ℝ → ℝ}

lemma inner_eq_integral (f : Lp ℝ 2 μ) {g : α → ℝ} (hg : MemLp g 2 μ) :
    ⟪f, hg.toLp g⟫_ℝ = ∫ x, f x * g x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hg.coeFn_toLp] with x hx
  rw [hx]; simp [mul_comm]

/-- **Differentiation of `r ↦ ∫ k_r ψ(u_r)`** (the product rule used in the proof of Thm 3.3.18, p. 164):
`k` is `L²`-differentiable, `u ≥ 0` is `L¹`-differentiable, `k_s` is bounded. -/
theorem hasDerivAt_pair {K1 K2 : ℝ} (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2)
    (hψm : Measurable ψ) (hψ'm : Measurable ψ') (hψ0 : ψ 0 = 0)
    (hψ' : ∀ a, 0 ≤ a → |ψ' a| ≤ K1)
    (hrem : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      |ψ b - ψ a - ψ' a * (b - a)| ≤ |b - a| * min (K2 * |b - a|) (2 * K1))
    (hH : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (ψ b - ψ a) ^ 2 ≤ |b - a|)
    {u : ℝ → Lp ℝ 1 μ} {u' : Lp ℝ 1 μ} {s : ℝ} (hu : HasDerivAt u u' s)
    (hnn : ∀ r, 0 ≤ᵐ[μ] (u r : α → ℝ))
    {k : ℝ → Lp ℝ 2 μ} {k' : Lp ℝ 2 μ} (hk : HasDerivAt k k' s)
    {M : ℝ} (hM : 0 ≤ M) (hkb : ∀ᵐ x ∂μ, |(k s : α → ℝ) x| ≤ M) :
    HasDerivAt (fun r => ∫ x, k r x * ψ (u r x) ∂μ)
      ((∫ x, k' x * ψ (u s x) ∂μ) + ∫ x, k s x * (ψ' (u s x) * u' x) ∂μ) s := by
  have mΨ : ∀ r, MemLp (fun x => ψ (u r x)) 2 μ := fun r => memLp_two_comp hψm hψ0 hH (u r) (hnn r)
  set Ψ : ℝ → Lp ℝ 2 μ := fun r => psiCls hψm hψ0 hH (u r) (hnn r) with hΨ
  have hΨc : Tendsto Ψ (𝓝 s) (𝓝 (Ψ s)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun r => ‖u r - u s‖) (𝓝 s) (𝓝 0) := by
      simpa using tendsto_iff_norm_sub_tendsto_zero.1 hu.continuousAt.tendsto
    have h1 : Tendsto (fun r => Real.sqrt ‖u r - u s‖) (𝓝 s) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h0
      simpa [Function.comp_def] using this
    exact squeeze_zero (fun r => norm_nonneg _)
      (fun r => norm_psiCls_sub_le hψm hψ0 hH (u r) (u s) (hnn r) (hnn s)) h1
  have hB := hasDerivAt_integral_comp (ψ := ψ) hK1 hK2 hψm hψ'm hψ0 hψ' hrem hu hnn (k := k s) hM
    (Lp.aestronglyMeasurable (k s)) hkb
  set A : ℝ → ℝ := fun r => ∫ x, (k r x - k s x) * ψ (u r x) ∂μ with hA
  have hAr : ∀ r, A r = ⟪k r - k s, Ψ r⟫_ℝ := by
    intro r
    rw [hA]
    show _ = ⟪k r - k s, (mΨ r).toLp _⟫_ℝ
    rw [inner_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (k r) (k s)] with x hx
    rw [hx]; simp
  have hA0 : A s = 0 := by rw [hAr]; simp
  have hAd : HasDerivAt A (∫ x, k' x * ψ (u s x) ∂μ) s := by
    rw [hasDerivAt_iff_tendsto_slope]
    have hks := hasDerivAt_iff_tendsto_slope.1 hk
    have : Tendsto (fun r => ⟪(r - s)⁻¹ • (k r - k s), Ψ r⟫_ℝ) (𝓝[≠] s) (𝓝 ⟪k', Ψ s⟫_ℝ) := by
      have hΨ' : Tendsto Ψ (𝓝[≠] s) (𝓝 (Ψ s)) := hΨc.mono_left nhdsWithin_le_nhds
      refine Tendsto.inner ?_ hΨ'
      refine hks.congr' ?_
      filter_upwards with r
      simp [slope_def_module]
    have e : ⟪k', Ψ s⟫_ℝ = ∫ x, k' x * ψ (u s x) ∂μ := by
      show ⟪k', (mΨ s).toLp _⟫_ℝ = _
      rw [inner_eq_integral]
    rw [← e]
    refine this.congr' ?_
    filter_upwards with r
    rw [slope_def_module, hA0, sub_zero, hAr, inner_smul_left]
    simp
  have hsum : (fun r => ∫ x, k r x * ψ (u r x) ∂μ) =
      fun r => A r + ∫ x, k s x * ψ (u r x) ∂μ := by
    funext r
    rw [hA, ← integral_add]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only; ring
    · exact ((Lp.memLp (k r)).sub (Lp.memLp (k s))).integrable_mul (mΨ r)
    · exact (Lp.memLp (k s)).integrable_mul (mΨ r)
  rw [hsum]
  exact hAd.add hB


/-- continuity of `r ↦ ∫ k_r ψ(u_r)` (end points of `[0,t]` in the proof of Thm 3.3.18). -/
theorem continuous_pair (hψm : Measurable ψ) (hψ0 : ψ 0 = 0)
    (hH : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (ψ b - ψ a) ^ 2 ≤ |b - a|)
    {u : ℝ → Lp ℝ 1 μ} (hu : Continuous u) (hnn : ∀ r, 0 ≤ᵐ[μ] (u r : α → ℝ))
    {k : ℝ → Lp ℝ 2 μ} (hk : Continuous k) :
    Continuous (fun r => ∫ x, k r x * ψ (u r x) ∂μ) := by
  have mΨ : ∀ r, MemLp (fun x => ψ (u r x)) 2 μ := fun r => memLp_two_comp hψm hψ0 hH (u r) (hnn r)
  have hΨ : Continuous (fun r => psiCls hψm hψ0 hH (u r) (hnn r)) := by
    rw [continuous_iff_continuousAt]
    intro s
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Tendsto (fun r => ‖u r - u s‖) (𝓝 s) (𝓝 0) := by
      simpa using tendsto_iff_norm_sub_tendsto_zero.1 (hu.tendsto s)
    have h1 : Tendsto (fun r => Real.sqrt ‖u r - u s‖) (𝓝 s) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp h0
      simpa [Function.comp_def] using this
    exact squeeze_zero (fun r => norm_nonneg _)
      (fun r => norm_psiCls_sub_le hψm hψ0 hH (u r) (u s) (hnn r) (hnn s)) h1
  have : (fun r => ∫ x, k r x * ψ (u r x) ∂μ) =
      fun r => ⟪k r, psiCls hψm hψ0 hH (u r) (hnn r)⟫_ℝ := by
    funext r
    exact (inner_eq_integral (k r) (mΨ r)).symm
  rw [this]
  exact hk.inner hΨ

end MarkovTriple.BGL
