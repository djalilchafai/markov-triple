import Mathlib

/-!
# A trilinear form on `L²` and its product rule (analytic tool for the compact flow)

For `a b c ∈ L²(μ)` with `c` essentially bounded, `tri a b c = ∫ a b c dμ` is a well defined
trilinear quantity, `|tri a b c| ≤ M ‖a‖ ‖b‖` if `|c| ≤ M`.  We prove the Leibniz rule for
`r ↦ tri (A r) (B r) (C r)` when `A, B, C : ℝ → L²` are `L²`-differentiable and uniformly
essentially bounded (no regularity of the derivatives in `L^∞` is needed), and continuity.
-/

open MeasureTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace MarkovTriple.BGL.Compact

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- `c` is essentially bounded by `M`. -/
def Bdd (M : ℝ) (c : Lp ℝ 2 μ) : Prop := ∀ᵐ x ∂μ, |(c : E → ℝ) x| ≤ M

/-- the trilinear form `∫ a b c`. -/
noncomputable def tri (a b c : Lp ℝ 2 μ) : ℝ := ∫ x, (a : E → ℝ) x * (b : E → ℝ) x * (c : E → ℝ) x ∂μ

lemma integrable_mul_L2 (a b : Lp ℝ 2 μ) :
    Integrable (fun x => (a : E → ℝ) x * (b : E → ℝ) x) μ := by
  simpa [mul_comm] using L2.integrable_inner (𝕜 := ℝ) b a

lemma tri_integrable {M : ℝ} {c : Lp ℝ 2 μ} (hc : Bdd M c) (a b : Lp ℝ 2 μ) :
    Integrable (fun x => (a : E → ℝ) x * (b : E → ℝ) x * (c : E → ℝ) x) μ :=
  (integrable_mul_L2 a b).mul_bdd (c := M) (Lp.aestronglyMeasurable c)
    (hc.mono fun x hx => by simpa using hx)

lemma tri_abs_le {M : ℝ} (_hM : 0 ≤ M) {c : Lp ℝ 2 μ} (hc : Bdd M c) (a b : Lp ℝ 2 μ) :
    |tri a b c| ≤ M * ‖a‖ * ‖b‖ := by
  have hbc : MemLp (fun x => (b : E → ℝ) x * (c : E → ℝ) x) 2 μ := by
    refine MemLp.of_le_mul (c := M) (Lp.memLp b) ((Lp.aestronglyMeasurable b).mul
      (Lp.aestronglyMeasurable c)) ?_
    filter_upwards [hc] with x hx
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _) |>.trans_eq (by simp [Real.norm_eq_abs])
  set bc : Lp ℝ 2 μ := hbc.toLp _ with hbcdef
  have h1 : tri a b c = inner ℝ a bc := by
    rw [L2.inner_def]
    simp only [tri]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp hbc] with x hx
    rw [hx]; simp; ring
  have h2 : ‖bc‖ ≤ M * ‖b‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [MemLp.coeFn_toLp hbc, hc] with x hx hx2
    rw [hx, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hx2 (abs_nonneg _)
  rw [h1]
  calc |inner ℝ a bc| ≤ ‖a‖ * ‖bc‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖a‖ * (M * ‖b‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = M * ‖a‖ * ‖b‖ := by ring

lemma tri_comm12 (a b c : Lp ℝ 2 μ) : tri a b c = tri b a c := by
  unfold tri; refine integral_congr_ae (Eventually.of_forall fun x => by ring)

lemma tri_rot (a b c : Lp ℝ 2 μ) : tri a b c = tri c a b := by
  unfold tri; refine integral_congr_ae (Eventually.of_forall fun x => by ring)

lemma tri_comm23 (a b c : Lp ℝ 2 μ) : tri a b c = tri a c b := by
  unfold tri; refine integral_congr_ae (Eventually.of_forall fun x => by ring)

lemma tri_sub_left {M : ℝ} {c : Lp ℝ 2 μ} (hc : Bdd M c) (a a' b : Lp ℝ 2 μ) :
    tri (a - a') b c = tri a b c - tri a' b c := by
  unfold tri
  rw [← integral_sub (tri_integrable hc a b) (tri_integrable hc a' b)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub a a'] with x hx
  rw [hx]; simp only [Pi.sub_apply]; ring

lemma tri_smul_left {M : ℝ} {c : Lp ℝ 2 μ} (_hc : Bdd M c) (r : ℝ) (a b : Lp ℝ 2 μ) :
    tri (r • a) b c = r * tri a b c := by
  unfold tri
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_smul r a] with x hx
  rw [hx]; simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma tri_add_left {M : ℝ} {c : Lp ℝ 2 μ} (hc : Bdd M c) (a a' b : Lp ℝ 2 μ) :
    tri (a + a') b c = tri a b c + tri a' b c := by
  unfold tri
  rw [← integral_add (tri_integrable hc a b) (tri_integrable hc a' b)]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_add a a'] with x hx
  rw [hx]; simp only [Pi.add_apply]; ring

lemma tri_telescope {M : ℝ} {c b0 : Lp ℝ 2 μ} (a b a0 c0 : Lp ℝ 2 μ) (hc : Bdd M c)
    (hb0 : Bdd M b0) :
    tri a b c - tri a0 b0 c0 =
      tri (a - a0) b c + tri (b - b0) a0 c + tri (c - c0) a0 b0 := by
  rw [tri_sub_left hc, tri_sub_left hc, tri_sub_left hb0,
    tri_comm12 b a0 c, tri_comm12 b0 a0 c, ← tri_rot a0 b0 c, ← tri_rot a0 b0 c0]
  ring

/-- joint continuity of `tri` (third slot uniformly bounded along the filter, second limit factor
bounded). -/
lemma tri_tendsto {ι : Type*} {l : Filter ι} {a b c : ι → Lp ℝ 2 μ} {a0 b0 c0 : Lp ℝ 2 μ}
    {M : ℝ} (hM : 0 ≤ M) (ha : Tendsto a l (𝓝 a0)) (hb : Tendsto b l (𝓝 b0))
    (hc : Tendsto c l (𝓝 c0)) (hcb : ∀ᶠ i in l, Bdd M (c i)) (hb0 : Bdd M b0) :
    Tendsto (fun i => tri (a i) (b i) (c i)) l (𝓝 (tri a0 b0 c0)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ᶠ i in l, ‖tri (a i) (b i) (c i) - tri a0 b0 c0‖ ≤
      M * ‖a i - a0‖ * ‖b i‖ + M * ‖b i - b0‖ * ‖a0‖ + M * ‖c i - c0‖ * ‖a0‖ := by
    filter_upwards [hcb] with i hi
    rw [tri_telescope _ _ a0 c0 hi hb0]
    refine (norm_add_le _ _).trans ?_
    refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
    have t1 := tri_abs_le hM hi (a i - a0) (b i)
    have t2 := tri_abs_le hM hi (b i - b0) a0
    have t3 := tri_abs_le hM hb0 (c i - c0) a0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith
  have h1 := tendsto_iff_norm_sub_tendsto_zero.1 ha
  have h2 := tendsto_iff_norm_sub_tendsto_zero.1 hb
  have h3 := tendsto_iff_norm_sub_tendsto_zero.1 hc
  have hlim : Tendsto (fun i => M * ‖a i - a0‖ * ‖b i‖ + M * ‖b i - b0‖ * ‖a0‖ +
      M * ‖c i - c0‖ * ‖a0‖) l (𝓝 (M * 0 * ‖b0‖ + M * 0 * ‖a0‖ + M * 0 * ‖a0‖)) :=
    (((tendsto_const_nhds.mul h1).mul hb.norm).add
      ((tendsto_const_nhds.mul h2).mul tendsto_const_nhds)).add
      ((tendsto_const_nhds.mul h3).mul tendsto_const_nhds)
  simp only [mul_zero, zero_mul, add_zero] at hlim
  exact squeeze_zero' (Eventually.of_forall fun i => norm_nonneg _) hbound hlim


/-- **Leibniz rule** for `r ↦ ∫ A_r B_r C_r` with `L²`-differentiable, uniformly bounded factors. -/
theorem tri_hasDerivAt {A B C : ℝ → Lp ℝ 2 μ} {A' B' C' : Lp ℝ 2 μ} {s M : ℝ} (hM : 0 ≤ M)
    (hA : HasDerivAt A A' s) (hB : HasDerivAt B B' s) (hC : HasDerivAt C C' s)
    (hbA : ∀ r, Bdd M (A r)) (hbB : ∀ r, Bdd M (B r)) (hbC : ∀ r, Bdd M (C r)) :
    HasDerivAt (fun r => tri (A r) (B r) (C r))
      (tri A' (B s) (C s) + tri (A s) B' (C s) + tri (A s) (B s) C') s := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hslope : ∀ r, r ≠ s → slope (fun r => tri (A r) (B r) (C r)) s r =
      tri (slope A s r) (B r) (C r) + tri (slope B s r) (A s) (C r) +
        tri (slope C s r) (A s) (B s) := by
    intro r hr
    simp only [slope_def_module, smul_eq_mul]
    rw [tri_telescope _ _ (A s) (C s) (hbC r) (hbB s), mul_add, mul_add,
      ← tri_smul_left (hbC r), ← tri_smul_left (hbC r), ← tri_smul_left (hbB s)]
  have hAc : Tendsto (slope A s) (𝓝[≠] s) (𝓝 A') := hasDerivAt_iff_tendsto_slope.1 hA
  have hBc : Tendsto (slope B s) (𝓝[≠] s) (𝓝 B') := hasDerivAt_iff_tendsto_slope.1 hB
  have hCc : Tendsto (slope C s) (𝓝[≠] s) (𝓝 C') := hasDerivAt_iff_tendsto_slope.1 hC
  have hBt : Tendsto B (𝓝[≠] s) (𝓝 (B s)) := hB.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hCt : Tendsto C (𝓝[≠] s) (𝓝 (C s)) := hC.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t1 := tri_tendsto hM hAc hBt hCt (Eventually.of_forall hbC) (hbB s)
  have t2 := tri_tendsto hM hBc (tendsto_const_nhds (x := A s)) hCt (Eventually.of_forall hbC) (hbA s)
  have t3 := tri_tendsto hM hCc (tendsto_const_nhds (x := A s)) (tendsto_const_nhds (x := B s))
    (Eventually.of_forall fun _ => hbB s) (hbA s)
  have := (t1.add t2).add t3
  have e : tri B' (A s) (C s) = tri (A s) B' (C s) := tri_comm12 _ _ _
  have e2 : tri C' (A s) (B s) = tri (A s) (B s) C' := (tri_rot _ _ _).symm
  rw [e, e2] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (hslope r hr).symm

/-- continuity of `r ↦ ∫ A_r B_r C_r`. -/
theorem tri_continuousAt {A B C : ℝ → Lp ℝ 2 μ} {s M : ℝ} (hM : 0 ≤ M)
    (hA : ContinuousAt A s) (hB : ContinuousAt B s) (hC : ContinuousAt C s)
    (hbB : ∀ r, Bdd M (B r)) (hbC : ∀ r, Bdd M (C r)) :
    ContinuousAt (fun r => tri (A r) (B r) (C r)) s :=
  tri_tendsto hM hA hB hC (Eventually.of_forall hbC) (hbB s)

end MarkovTriple.BGL.Compact

namespace MarkovTriple.BGL.Compact

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

lemma tri_ae {a b c : Lp ℝ 2 μ} {u v w : E → ℝ} (ha : (a : E → ℝ) =ᵐ[μ] u)
    (hb : (b : E → ℝ) =ᵐ[μ] v) (hc : (c : E → ℝ) =ᵐ[μ] w) :
    tri a b c = ∫ x, u x * v x * w x ∂μ := by
  unfold tri
  refine integral_congr_ae ?_
  filter_upwards [ha, hb, hc] with x h1 h2 h3
  rw [h1, h2, h3]

lemma tri_neg_mid (a b c : Lp ℝ 2 μ) : tri a (-b) c = -tri a b c := by
  unfold tri
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg b] with x hx
  rw [hx]; simp only [Pi.neg_apply]; ring

lemma tri_neg_right (a b c : Lp ℝ 2 μ) : tri a b (-c) = -tri a b c := by
  unfold tri
  rw [← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_neg c] with x hx
  rw [hx]; simp only [Pi.neg_apply]; ring

end MarkovTriple.BGL.Compact
