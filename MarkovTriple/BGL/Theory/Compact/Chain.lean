import Mathlib
import MarkovTriple.BGL.Theory.Compact.Product

/-!
# Differentiation of `r ↦ ∫ F(G_r) V_r` for `F ∈ C^{1,1}_b` (chain rule against a bounded factor)

For `G, V : ℝ → L²(μ)` (finite `μ`) `L²`-differentiable at `s`, `V` uniformly essentially bounded,
and `F` bounded with bounded derivative `F'` and quadratic Taylor remainder, the function
`J(r) = ∫ F(G_r) V_r dμ` is differentiable at `s` with derivative
`∫ F'(G_s) G' V_s + ∫ F(G_s) V'`.  (`F ∘ G_r` itself is *not* `L²`-differentiable in general, so the
remainder is controlled in `L¹` against the bounded factor `V_r`.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace MarkovTriple.BGL.Compact

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ]

/-- the class of `F ∘ u` for bounded continuous `F`. -/
noncomputable def cmp (F : ℝ → ℝ) (hF : Continuous F) {K : ℝ} (hb : ∀ y, |F y| ≤ K)
    (u : Lp ℝ 2 μ) : Lp ℝ 2 μ :=
  (MemLp.of_bound (p := 2) (hF.comp_aestronglyMeasurable (Lp.aestronglyMeasurable u)) K
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hb (u x))).toLp _

lemma coeFn_cmp (F : ℝ → ℝ) (hF : Continuous F) {K : ℝ} (hb : ∀ y, |F y| ≤ K) (u : Lp ℝ 2 μ) :
    (cmp F hF hb u : E → ℝ) =ᵐ[μ] fun x => F (u x) := MemLp.coeFn_toLp _

lemma bdd_cmp (F : ℝ → ℝ) (hF : Continuous F) {K : ℝ} (hb : ∀ y, |F y| ≤ K) (u : Lp ℝ 2 μ) :
    Bdd K (cmp F hF hb u) := by
  filter_upwards [coeFn_cmp F hF hb u] with x hx
  rw [hx]; exact hb _

lemma integral_sq_eq (u : Lp ℝ 2 μ) : ∫ x, ((u : E → ℝ) x) ^ 2 ∂μ = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [sq]

lemma integrable_Lp_mul_bdd {M : ℝ} {c : Lp ℝ 2 μ} (hc : Bdd M c) (a : Lp ℝ 2 μ) :
    Integrable (fun x => (a : E → ℝ) x * (c : E → ℝ) x) μ :=
  ((Lp.memLp a).integrable (by norm_num)).mul_bdd (c := M) (Lp.aestronglyMeasurable c)
    (hc.mono fun x hx => by simpa using hx)

theorem hasDerivAt_pair {F F' : ℝ → ℝ} {K0 K1 K2 M : ℝ} (hFc : Continuous F)
    (hF'c : Continuous F') (hb0 : ∀ y, |F y| ≤ K0) (hb1 : ∀ y, |F' y| ≤ K1) (hK2 : 0 ≤ K2)
    (htay : ∀ x y, |F y - F x - F' x * (y - x)| ≤ K2 * (y - x) ^ 2) (hM : 0 ≤ M)
    (hK1 : 0 ≤ K1) {G V : ℝ → Lp ℝ 2 μ} {G' V' : Lp ℝ 2 μ} {s : ℝ}
    (hG : HasDerivAt G G' s) (hV : HasDerivAt V V' s) (hVb : ∀ r, Bdd M (V r)) :
    HasDerivAt (fun r => ∫ x, F ((G r : E → ℝ) x) * (V r : E → ℝ) x ∂μ)
      (∫ x, F' ((G s : E → ℝ) x) * (G' : E → ℝ) x * (V s : E → ℝ) x ∂μ +
        ∫ x, F ((G s : E → ℝ) x) * (V' : E → ℝ) x ∂μ) s := by
  set a := cmp F hFc hb0 (G s) with ha
  set b := cmp F' hF'c hb1 (G s) with hb
  set M' := max M K1 with hM'
  have hMM : M ≤ M' := le_max_left _ _
  have hKM : K1 ≤ M' := le_max_right _ _
  have hM'0 : 0 ≤ M' := hM.trans hMM
  have hVb' : ∀ r, Bdd M' (V r) := fun r => (hVb r).mono fun x hx => hx.trans hMM
  have hbb : Bdd M' b := (bdd_cmp F' hF'c hb1 (G s)).mono fun x hx => hx.trans hKM
  rw [hasDerivAt_iff_tendsto_slope]
  -- decomposition of the slope
  set R : ℝ → E → ℝ := fun r x => F ((G r : E → ℝ) x) - F ((G s : E → ℝ) x) -
    F' ((G s : E → ℝ) x) * ((G r : E → ℝ) x - (G s : E → ℝ) x) with hR
  have intJ : ∀ (u v : Lp ℝ 2 μ), Bdd M' v →
      Integrable (fun x => F ((u : E → ℝ) x) * (v : E → ℝ) x) μ := by
    intro u v hv
    refine (integrable_Lp_mul_bdd hv (cmp F hFc hb0 u)).congr ?_
    filter_upwards [coeFn_cmp F hFc hb0 u] with x hx
    rw [hx]
  have hf2 : ∀ r, Integrable (fun x => F' ((G s : E → ℝ) x) *
      ((G r : E → ℝ) x - (G s : E → ℝ) x) * (V r : E → ℝ) x) μ := by
    intro r
    refine (tri_integrable (hVb' r) (G r - G s) b).congr ?_
    filter_upwards [Lp.coeFn_sub (G r) (G s), coeFn_cmp F' hF'c hb1 (G s)] with x h1 h2
    rw [h1, h2]; simp only [Pi.sub_apply]; ring
  have hslope : ∀ r, r ≠ s → slope (fun r => ∫ x, F ((G r : E → ℝ) x) * (V r : E → ℝ) x ∂μ) s r =
      tri (slope G s r) b (V r) + inner ℝ a (slope V s r) +
        (r - s)⁻¹ * ∫ x, R r x * (V r : E → ℝ) x ∂μ := by
    intro r hr
    have f1 : Integrable (fun x => F ((G s : E → ℝ) x) * ((V r : E → ℝ) x - (V s : E → ℝ) x)) μ := by
      have := (intJ (G s) (V r) (hVb' r)).sub (intJ (G s) (V s) (hVb' s))
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]; ring
    have f3 : Integrable (fun x => R r x * (V r : E → ℝ) x) μ := by
      have := ((intJ (G r) (V r) (hVb' r)).sub (intJ (G s) (V r) (hVb' r))).sub (hf2 r)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply, hR]; ring
    have key : (∫ x, F ((G r : E → ℝ) x) * (V r : E → ℝ) x ∂μ) -
        ∫ x, F ((G s : E → ℝ) x) * (V s : E → ℝ) x ∂μ =
        (∫ x, F ((G s : E → ℝ) x) * ((V r : E → ℝ) x - (V s : E → ℝ) x) ∂μ) +
        (∫ x, F' ((G s : E → ℝ) x) * ((G r : E → ℝ) x - (G s : E → ℝ) x) * (V r : E → ℝ) x ∂μ) +
        ∫ x, R r x * (V r : E → ℝ) x ∂μ := by
      have h12 : Integrable (fun x => F ((G s : E → ℝ) x) * ((V r : E → ℝ) x - (V s : E → ℝ) x) +
          F' ((G s : E → ℝ) x) * ((G r : E → ℝ) x - (G s : E → ℝ) x) * (V r : E → ℝ) x) μ :=
        f1.add (hf2 r)
      rw [← integral_sub (intJ (G r) (V r) (hVb' r)) (intJ (G s) (V s) (hVb' s)),
        integral_add f1 (hf2 r) |>.symm, integral_add h12 f3 |>.symm]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [hR]; ring
    have e1 : inner ℝ a (slope V s r) =
        (r - s)⁻¹ * ∫ x, F ((G s : E → ℝ) x) * ((V r : E → ℝ) x - (V s : E → ℝ) x) ∂μ := by
      rw [slope_def_module, real_inner_smul_right, L2.inner_def (𝕜 := ℝ)]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [coeFn_cmp F hFc hb0 (G s), Lp.coeFn_sub (V r) (V s)] with x h1 h2
      rw [h2, ha, h1]; simp only [Pi.sub_apply]; simp [mul_comm]
    have e2 : tri (slope G s r) b (V r) =
        (r - s)⁻¹ * ∫ x, F' ((G s : E → ℝ) x) * ((G r : E → ℝ) x - (G s : E → ℝ) x) *
          (V r : E → ℝ) x ∂μ := by
      rw [slope_def_module, tri_smul_left (hVb' r)]
      congr 1
      unfold tri
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (G r) (G s), coeFn_cmp F' hF'c hb1 (G s)] with x h1 h2
      rw [h1, hb, h2]; simp only [Pi.sub_apply]; ring
    rw [slope_def_module, smul_eq_mul, e1, e2, key]; ring
  have hGt : Tendsto (slope G s) (𝓝[≠] s) (𝓝 G') := hasDerivAt_iff_tendsto_slope.1 hG
  have hVt : Tendsto V (𝓝[≠] s) (𝓝 (V s)) := hV.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hVs : Tendsto (slope V s) (𝓝[≠] s) (𝓝 V') := hasDerivAt_iff_tendsto_slope.1 hV
  have t1 := tri_tendsto hM'0 hGt (tendsto_const_nhds (x := b)) hVt (Eventually.of_forall hVb') hbb
  have t2 : Tendsto (fun r => inner ℝ a (slope V s r)) (𝓝[≠] s) (𝓝 (inner ℝ a V')) :=
    (tendsto_const_nhds (x := a)).inner hVs
  have t3 : Tendsto (fun r => (r - s)⁻¹ * ∫ x, R r x * (V r : E → ℝ) x ∂μ) (𝓝[≠] s) (𝓝 0) := by
    have hbound : ∀ᶠ r in 𝓝[≠] s, ‖(r - s)⁻¹ * ∫ x, R r x * (V r : E → ℝ) x ∂μ‖ ≤
        |r - s| * (K2 * M' * ‖slope G s r‖ ^ 2) := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hrs : r - s ≠ 0 := sub_ne_zero.2 hr
      have hnorm : ‖G r - G s‖ = |r - s| * ‖slope G s r‖ := by
        rw [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv, ← mul_assoc,
          mul_inv_cancel₀ (abs_pos.2 hrs).ne', one_mul]
      have hint : |∫ x, R r x * (V r : E → ℝ) x ∂μ| ≤ K2 * M' * ‖G r - G s‖ ^ 2 := by
        refine (abs_integral_le_integral_abs).trans ?_
        have hsq : Integrable (fun x => ((G r - G s : Lp ℝ 2 μ) : E → ℝ) x ^ 2) μ :=
          (Lp.memLp (G r - G s)).integrable_sq
        have : ∫ x, |R r x * (V r : E → ℝ) x| ∂μ ≤
            ∫ x, K2 * M' * (((G r - G s : Lp ℝ 2 μ) : E → ℝ) x ^ 2) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            (hsq.const_mul _) ?_
          filter_upwards [Lp.coeFn_sub (G r) (G s), hVb' r] with x h1 h2
          rw [abs_mul]
          have h3 := htay ((G s : E → ℝ) x) ((G r : E → ℝ) x)
          have h4 : |R r x| ≤ K2 * (((G r - G s : Lp ℝ 2 μ) : E → ℝ) x) ^ 2 := by
            rw [h1]; simp only [Pi.sub_apply]; exact h3
          calc |R r x| * |(V r : E → ℝ) x| ≤ (K2 * (((G r - G s : Lp ℝ 2 μ) : E → ℝ) x) ^ 2) * M' :=
                mul_le_mul h4 h2 (abs_nonneg _) (by positivity)
            _ = K2 * M' * (((G r - G s : Lp ℝ 2 μ) : E → ℝ) x ^ 2) := by ring
        rw [integral_const_mul, integral_sq_eq] at this
        exact this
      rw [norm_mul, norm_inv, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |r - s|⁻¹ * |∫ x, R r x * (V r : E → ℝ) x ∂μ| ≤
          |r - s|⁻¹ * (K2 * M' * ‖G r - G s‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hint (by positivity)
        _ = |r - s| * (K2 * M' * ‖slope G s r‖ ^ 2) := by
            rw [hnorm]
            have : |r - s| ≠ 0 := (abs_pos.2 hrs).ne'
            field_simp
    have hlim : Tendsto (fun r => |r - s| * (K2 * M' * ‖slope G s r‖ ^ 2)) (𝓝[≠] s) (𝓝 0) := by
      have h1 : Tendsto (fun r : ℝ => |r - s|) (𝓝[≠] s) (𝓝 0) := by
        have : Tendsto (fun r : ℝ => |r - s|) (𝓝 s) (𝓝 0) := by
          have hc : Continuous fun r : ℝ => |r - s| := (continuous_id.sub continuous_const).abs
          simpa using hc.tendsto s
        exact this.mono_left nhdsWithin_le_nhds
      have h2 := ((tendsto_const_nhds (x := K2 * M')).mul (hGt.norm.pow 2))
      simpa using h1.mul h2
    exact squeeze_zero_norm' hbound hlim
  have tt := (t1.add t2).add t3
  have e3 : tri G' b (V s) = ∫ x, F' ((G s : E → ℝ) x) * (G' : E → ℝ) x * (V s : E → ℝ) x ∂μ := by
    unfold tri
    refine integral_congr_ae ?_
    filter_upwards [coeFn_cmp F' hF'c hb1 (G s)] with x hx
    rw [hb, hx]; ring
  have e4 : inner ℝ a V' = ∫ x, F ((G s : E → ℝ) x) * (V' : E → ℝ) x ∂μ := by
    rw [L2.inner_def (𝕜 := ℝ)]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_cmp F hFc hb0 (G s)] with x hx
    rw [ha, hx]; simp [mul_comm]
  rw [e3, e4, add_zero] at tt
  refine tt.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hslope r hr).symm


/-- continuity of `r ↦ ∫ F(G_r) V_r` for Lipschitz bounded `F`. -/
theorem continuousAt_pair {F : ℝ → ℝ} {K0 K1 : ℝ} (hFc : Continuous F) (hb0 : ∀ y, |F y| ≤ K0)
    (hlip : ∀ x y, |F y - F x| ≤ K1 * |y - x|) {G V : ℝ → Lp ℝ 2 μ} {s : ℝ}
    (hG : ContinuousAt G s) (hV : ContinuousAt V s) :
    ContinuousAt (fun r => ∫ x, F ((G r : E → ℝ) x) * (V r : E → ℝ) x ∂μ) s := by
  have hc : ContinuousAt (fun r => cmp F hFc hb0 (G r)) s := by
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ r, ‖cmp F hFc hb0 (G r) - cmp F hFc hb0 (G s)‖ ≤ K1 * ‖G r - G s‖ := by
      intro r
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [Lp.coeFn_sub (cmp F hFc hb0 (G r)) (cmp F hFc hb0 (G s)),
        coeFn_cmp F hFc hb0 (G r), coeFn_cmp F hFc hb0 (G s), Lp.coeFn_sub (G r) (G s)]
        with x h1 h2 h3 h4
      rw [h1, h4]; simp only [Pi.sub_apply, h2, h3, Real.norm_eq_abs]
      exact hlip _ _
    have h0 := tendsto_iff_norm_sub_tendsto_zero.1 hG
    have := (tendsto_const_nhds (x := K1)).mul h0
    rw [mul_zero] at this
    exact squeeze_zero (fun r => norm_nonneg _) hb this
  have : ContinuousAt (fun r => inner ℝ (cmp F hFc hb0 (G r)) (V r)) s := hc.inner hV
  refine this.congr (Eventually.of_forall fun r => ?_)
  show inner ℝ _ _ = _
  rw [L2.inner_def (𝕜 := ℝ)]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_cmp F hFc hb0 (G r)] with x hx
  rw [hx]; simp [mul_comm]

end MarkovTriple.BGL.Compact
