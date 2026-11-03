import Mathlib
import MarkovTriple.BGL.Theory.Interp.EntropyAnalysis

/-!
# The quotient `r ↦ ∫ u_r / g_r` (de Bruijn: the Fisher information `I(s) = ∫ Γ(g_s)/g_s`)

`u_r ∈ L¹` (here `Γ(P_r φ)`), `g_r ∈ L²` with `g_r ≥ ε > 0` (here `ε + P_r φ`), finite measure.

* `tendsto_inv_diff`: `∫ |w| |1/g_r - 1/g_s| → 0` as `g_r → g_s` in `L²` (`w ∈ L¹`; truncation at level `N` using
  `tendsto_tail_integral` and `L¹ ≤ C L²`);
* `continuous_integral_div`: continuity of `r ↦ ∫ u_r/g_r`;
* `hasDerivAt_integral_div`: derivative `∫ u'/g_s - ∫ u_s g'/g_s²` when `u_s ∈ L^∞`.
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

namespace MarkovTriple.BGL

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]

/-- the constant of `L¹ ≤ C L²`. -/
noncomputable def oneNorm (μ : Measure α) [IsFiniteMeasure μ] : ℝ :=
  ‖(memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ).toLp _‖

lemma oneNorm_nonneg : 0 ≤ oneNorm μ := norm_nonneg _

lemma integral_abs_le' (f : Lp ℝ 2 μ) : ∫ x, |f x| ∂μ ≤ ‖f‖ * oneNorm μ := integral_abs_le f

lemma integrable_Lp2 (f : Lp ℝ 2 μ) : Integrable (fun x => f x) μ :=
  (Lp.memLp f).integrable one_le_two

lemma inv_diff_le {ε a b : ℝ} (hε : 0 < ε) (ha : ε ≤ a) (hb : ε ≤ b) :
    |a⁻¹ - b⁻¹| ≤ |a - b| / ε ^ 2 ∧ |a⁻¹ - b⁻¹| ≤ 1 / ε := by
  have ha0 : 0 < a := lt_of_lt_of_le hε ha
  have hb0 : 0 < b := lt_of_lt_of_le hε hb
  have h1 : a⁻¹ ≤ ε⁻¹ := inv_anti₀ hε ha
  have h2 : b⁻¹ ≤ ε⁻¹ := inv_anti₀ hε hb
  constructor
  · have e : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
    rw [e, abs_div, abs_of_pos (mul_pos ha0 hb0), abs_sub_comm]
    refine div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) ?_
    nlinarith
  · have := inv_pos.2 ha0; have := inv_pos.2 hb0
    rw [one_div, abs_le]; constructor <;> linarith

lemma tendsto_inv_diff {l : Filter ℝ} {g : ℝ → Lp ℝ 2 μ} {s : ℝ} (hg : Tendsto g l (𝓝 (g s)))
    {ε : ℝ} (hε : 0 < ε) (hge : ∀ r, ∀ᵐ x ∂μ, ε ≤ g r x) {w : α → ℝ} (hw : Integrable w μ) :
    Tendsto (fun r => ∫ x, |w x| * |(g r x)⁻¹ - (g s x)⁻¹| ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  have ht := tendsto_tail_integral hw
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨N, hN⟩ := ht (η * ε / 2) (by positivity)
  have hN' := hN N le_rfl
  rw [Real.dist_eq, sub_zero] at hN'
  have htail0 : 0 ≤ ∫ x, max (|w x| - N) 0 ∂μ := integral_nonneg fun x => le_max_right _ _
  rw [abs_of_nonneg htail0] at hN'
  set C0 := oneNorm μ with hC0
  have hC00 : 0 ≤ C0 := oneNorm_nonneg
  have hNn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hθ : 0 < η * ε ^ 2 / (2 * (N * C0 + 1)) := by positivity
  have hnorm : ∀ᶠ r in l, ‖g r - g s‖ < η * ε ^ 2 / (2 * (N * C0 + 1)) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hg)
    exact (this.eventually (gt_mem_nhds hθ))
  filter_upwards [hnorm] with r hr
  rw [Real.dist_eq, sub_zero]
  have hnn : 0 ≤ ∫ x, |w x| * |(g r x)⁻¹ - (g s x)⁻¹| ∂μ :=
    integral_nonneg fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [abs_of_nonneg hnn]
  have hΔi : Integrable (fun x => |g r x - g s x|) μ :=
    ((integrable_Lp2 (g r)).sub (integrable_Lp2 (g s))).abs
  have hti : Integrable (fun x => max (|w x| - N) 0) μ :=
    hw.abs.mono' ((hw.abs.aestronglyMeasurable.sub aestronglyMeasurable_const).sup aestronglyMeasurable_const)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
        exact max_le (by linarith) (abs_nonneg _))
  have hmeas : AEStronglyMeasurable (fun x => |w x| * |(g r x)⁻¹ - (g s x)⁻¹|) μ :=
    ((hw.aemeasurable.abs).mul ((((Lp.aestronglyMeasurable (g r)).aemeasurable.inv).sub
      (Lp.aestronglyMeasurable (g s)).aemeasurable.inv).abs)).aestronglyMeasurable
  have hbound : Integrable (fun x => N / ε ^ 2 * |g r x - g s x| + (1 / ε) * max (|w x| - N) 0) μ :=
    (hΔi.const_mul _).add (hti.const_mul _)
  have hle : ∫ x, |w x| * |(g r x)⁻¹ - (g s x)⁻¹| ∂μ ≤
      ∫ x, (N / ε ^ 2 * |g r x - g s x| + (1 / ε) * max (|w x| - N) 0) ∂μ := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun x => mul_nonneg (abs_nonneg _) (abs_nonneg _))
      hbound ?_
    filter_upwards [hge r, hge s] with x h1 h2
    obtain ⟨d1, d2⟩ := inv_diff_le hε h1 h2
    have hD0 := abs_nonneg ((g r x)⁻¹ - (g s x)⁻¹)
    have hsplit : |w x| ≤ min |w x| N + max (|w x| - N) 0 := by
      rcases le_total |w x| N with h | h
      · rw [min_eq_left h, max_eq_right (by linarith)]; linarith
      · rw [min_eq_right h, max_eq_left (by linarith)]; linarith
    calc |w x| * |(g r x)⁻¹ - (g s x)⁻¹|
        ≤ (min |w x| N + max (|w x| - N) 0) * |(g r x)⁻¹ - (g s x)⁻¹| :=
          mul_le_mul_of_nonneg_right hsplit hD0
      _ = min |w x| N * |(g r x)⁻¹ - (g s x)⁻¹| + max (|w x| - N) 0 * |(g r x)⁻¹ - (g s x)⁻¹| := by ring
      _ ≤ N * (|g r x - g s x| / ε ^ 2) + max (|w x| - N) 0 * (1 / ε) := by
          refine add_le_add (mul_le_mul (min_le_right _ _) d1 hD0 hNn)
            (mul_le_mul_of_nonneg_left d2 (le_max_right _ _))
      _ = N / ε ^ 2 * |g r x - g s x| + (1 / ε) * max (|w x| - N) 0 := by ring
  have hrhs : ∫ x, (N / ε ^ 2 * |g r x - g s x| + (1 / ε) * max (|w x| - N) 0) ∂μ =
      N / ε ^ 2 * ∫ x, |g r x - g s x| ∂μ + (1 / ε) * ∫ x, max (|w x| - N) 0 ∂μ := by
    rw [integral_add (hΔi.const_mul _) (hti.const_mul _), integral_const_mul, integral_const_mul]
  have hL1 : ∫ x, |g r x - g s x| ∂μ ≤ ‖g r - g s‖ * C0 := by
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (integral_abs_le' (g r - g s))
    filter_upwards [Lp.coeFn_sub (g r) (g s)] with x hx
    rw [hx]; rfl
  have e1 : N / ε ^ 2 * ∫ x, |g r x - g s x| ∂μ < η / 2 := by
    have h1 : N / ε ^ 2 * ∫ x, |g r x - g s x| ∂μ ≤ N / ε ^ 2 * (‖g r - g s‖ * C0) :=
      mul_le_mul_of_nonneg_left hL1 (by positivity)
    have h2 : N / ε ^ 2 * (‖g r - g s‖ * C0) ≤ N * C0 / ε ^ 2 * ‖g r - g s‖ := by
      apply le_of_eq; ring
    have h3 : N * C0 / ε ^ 2 * ‖g r - g s‖ ≤ N * C0 / ε ^ 2 * (η * ε ^ 2 / (2 * (N * C0 + 1))) :=
      mul_le_mul_of_nonneg_left hr.le (by positivity)
    have h4 : N * C0 / ε ^ 2 * (η * ε ^ 2 / (2 * (N * C0 + 1))) = η / 2 * (N * C0 / (N * C0 + 1)) := by
      field_simp
    have h5 : N * C0 / (N * C0 + 1) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    have h6 : η / 2 * (N * C0 / (N * C0 + 1)) < η / 2 * 1 :=
      mul_lt_mul_of_pos_left h5 (by positivity)
    linarith
  have e2 : (1 / ε) * ∫ x, max (|w x| - N) 0 ∂μ < η / 2 := by
    have : (1 / ε) * ∫ x, max (|w x| - N) 0 ∂μ < (1 / ε) * (η * ε / 2) :=
      mul_lt_mul_of_pos_left hN' (by positivity)
    have e : (1 / ε) * (η * ε / 2) = η / 2 := by field_simp
    linarith
  calc _ ≤ _ := hle
    _ = _ := hrhs
    _ < η := by linarith


omit [IsFiniteMeasure μ] in
lemma integrable_mul_inv {u : α → ℝ} (hu : Integrable u μ) {g : Lp ℝ 2 μ} {ε : ℝ} (hε : 0 < ε)
    (hge : ∀ᵐ x ∂μ, ε ≤ g x) : Integrable (fun x => u x * (g x)⁻¹) μ := by
  refine (hu.abs.div_const ε).mono' (hu.aestronglyMeasurable.mul
    ((Lp.aestronglyMeasurable g).aemeasurable.inv.aestronglyMeasurable)) ?_
  filter_upwards [hge] with x hx
  have h0 : 0 < g x := lt_of_lt_of_le hε hx
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 h0), div_eq_mul_inv, mul_comm |u x|]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hε hx) (abs_nonneg _) |>.trans_eq (by ring)

omit [IsFiniteMeasure μ] in
/-- the `L¹`-norm of a class is the integral of its absolute value. -/
lemma norm_L1_eq (f : Lp ℝ 1 μ) : ‖f‖ = ∫ x, |f x| ∂μ := by
  rw [L1.norm_eq_integral_norm]; simp [Real.norm_eq_abs]

omit [IsFiniteMeasure μ] in
lemma abs_integral_div_diff_le (v w : Lp ℝ 1 μ) {g : Lp ℝ 2 μ} {ε : ℝ} (hε : 0 < ε)
    (hge : ∀ᵐ x ∂μ, ε ≤ g x) :
    |∫ x, (v x - w x) * (g x)⁻¹ ∂μ| ≤ ‖v - w‖ / ε := by
  have hi : Integrable (fun x => (v x - w x) * (g x)⁻¹) μ :=
    integrable_mul_inv ((L1.integrable_coeFn v).sub (L1.integrable_coeFn w)) hε hge
  refine (abs_integral_le_integral_abs).trans ?_
  rw [norm_L1_eq, div_eq_mul_inv, mul_comm, ← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_
  · exact (((L1.integrable_coeFn (v - w)).abs).const_mul _)
  · filter_upwards [hge, Lp.coeFn_sub v w] with x h1 h2
    rw [abs_mul, h2, Pi.sub_apply, abs_of_pos (inv_pos.2 (lt_of_lt_of_le hε h1))]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hε h1) (abs_nonneg _) |>.trans_eq (mul_comm _ _) |>.trans_eq rfl


omit [IsFiniteMeasure μ] in
/-- difference of two quotients, in the form used for continuity and differentiation. -/
lemma integral_div_sub (v w : Lp ℝ 1 μ) {g h : Lp ℝ 2 μ} {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ᵐ x ∂μ, ε ≤ g x) (hh : ∀ᵐ x ∂μ, ε ≤ h x) :
    (∫ x, v x / g x ∂μ) - ∫ x, w x / h x ∂μ =
      (∫ x, (v x - w x) * (g x)⁻¹ ∂μ) + ∫ x, w x * ((g x)⁻¹ - (h x)⁻¹) ∂μ := by
  have i1 := integrable_mul_inv (L1.integrable_coeFn v) hε hg
  have i2 := integrable_mul_inv (L1.integrable_coeFn w) hε hg
  have i3 := integrable_mul_inv (L1.integrable_coeFn w) hε hh
  have i4 : Integrable (fun x => (v x - w x) * (g x)⁻¹) μ :=
    integrable_mul_inv ((L1.integrable_coeFn v).sub (L1.integrable_coeFn w)) hε hg
  have e1 : (∫ x, v x / g x ∂μ) = ∫ x, v x * (g x)⁻¹ ∂μ := by simp only [div_eq_mul_inv]
  have e2 : (∫ x, w x / h x ∂μ) = ∫ x, w x * (h x)⁻¹ ∂μ := by simp only [div_eq_mul_inv]
  have e3 : (∫ x, (v x - w x) * (g x)⁻¹ ∂μ) = (∫ x, v x * (g x)⁻¹ ∂μ) - ∫ x, w x * (g x)⁻¹ ∂μ := by
    rw [← integral_sub i1 i2]; exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  have e4 : (∫ x, w x * ((g x)⁻¹ - (h x)⁻¹) ∂μ) = (∫ x, w x * (g x)⁻¹ ∂μ) - ∫ x, w x * (h x)⁻¹ ∂μ := by
    rw [← integral_sub i2 i3]; exact integral_congr_ae (Eventually.of_forall fun x => by simp only; ring)
  rw [e1, e2, e3, e4]; ring


/-- the key estimate of the differentiation of `r ↦ ∫ u_r/g_r` (difference quotient). -/
lemma slope_bound (v w v' : Lp ℝ 1 μ) (g h g' : Lp ℝ 2 μ) {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ᵐ x ∂μ, ε ≤ g x) (hh : ∀ᵐ x ∂μ, ε ≤ h x) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ᵐ x ∂μ, |w x| ≤ B) {δ : ℝ} (hδ : δ ≠ 0) :
    |δ⁻¹ * ((∫ x, v x / g x ∂μ) - ∫ x, w x / h x ∂μ) -
        ((∫ x, v' x / h x ∂μ) - ∫ x, w x * g' x / (h x) ^ 2 ∂μ)| ≤
      ‖δ⁻¹ • (v - w) - v'‖ / ε + ∫ x, |v' x| * |(g x)⁻¹ - (h x)⁻¹| ∂μ +
      B / ε ^ 2 * (‖δ⁻¹ • (g - h) - g'‖ * oneNorm μ) +
      ε⁻¹ * ∫ x, |w x * g' x| * |(g x)⁻¹ - (h x)⁻¹| ∂μ := by
  set Fp : Lp ℝ 1 μ := δ⁻¹ • (v - w) - v' with hFp
  set Fq : Lp ℝ 2 μ := δ⁻¹ • (g - h) - g' with hFq
  have hv := L1.integrable_coeFn v
  have hw := L1.integrable_coeFn w
  have hv' := L1.integrable_coeFn v'
  have iA : Integrable (fun x => v x / g x) μ := by
    simpa [div_eq_mul_inv] using integrable_mul_inv hv hε hg
  have iB : Integrable (fun x => w x / h x) μ := by
    simpa [div_eq_mul_inv] using integrable_mul_inv hw hε hh
  have iC : Integrable (fun x => v' x / h x) μ := by
    simpa [div_eq_mul_inv] using integrable_mul_inv hv' hε hh
  have hwg : Integrable (fun x => w x * g' x) μ := by
    refine ((integrable_Lp2 g').abs.const_mul B).mono'
      (hw.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g')) ?_
    filter_upwards [hB] with x hx
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have iD : Integrable (fun x => w x * g' x / (h x) ^ 2) μ := by
    refine (hwg.abs.div_const (ε ^ 2)).mono' (hwg.aemeasurable.div
      ((Lp.aestronglyMeasurable h).aemeasurable.pow_const 2)).aestronglyMeasurable ?_
    filter_upwards [hh] with x hx
    have h0 : 0 < h x := lt_of_lt_of_le hε hx
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (pow_pos h0 2)]
    exact div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) (pow_le_pow_left₀ hε.le hx 2)
  set K : α → ℝ := fun x => δ⁻¹ * (v x / g x - w x / h x) - (v' x / h x - w x * g' x / (h x) ^ 2)
    with hK
  have hKint : δ⁻¹ * ((∫ x, v x / g x ∂μ) - ∫ x, w x / h x ∂μ) -
      ((∫ x, v' x / h x ∂μ) - ∫ x, w x * g' x / (h x) ^ 2 ∂μ) = ∫ x, K x ∂μ := by
    have f1 : Integrable (fun x => δ⁻¹ * (v x / g x - w x / h x)) μ := (iA.sub iB).const_mul δ⁻¹
    have f2 : Integrable (fun x => v' x / h x - w x * g' x / (h x) ^ 2) μ := iC.sub iD
    rw [hK, integral_sub f1 f2, integral_const_mul, integral_sub iA iB, integral_sub iC iD]
  -- the dominating function
  set Bd : α → ℝ := fun x => ε⁻¹ * |Fp x| + |v' x| * |(g x)⁻¹ - (h x)⁻¹| +
    B / ε ^ 2 * |Fq x| + ε⁻¹ * (|w x * g' x| * |(g x)⁻¹ - (h x)⁻¹|) with hBd
  have hdiff : Integrable (fun x => |(g x)⁻¹ - (h x)⁻¹|) μ := by
    refine (integrable_const (1 / ε)).mono' ?_ ?_
    · exact (((Lp.aestronglyMeasurable g).aemeasurable.inv).sub
        (Lp.aestronglyMeasurable h).aemeasurable.inv).abs.aestronglyMeasurable
    · filter_upwards [hg, hh] with x h1 h2
      rw [Real.norm_eq_abs, abs_abs]; exact (inv_diff_le hε h1 h2).2
  have bdd_mul : ∀ {u : α → ℝ}, Integrable u μ → Integrable (fun x => |u x| * |(g x)⁻¹ - (h x)⁻¹|) μ := by
    intro u hu
    refine (hu.abs.div_const ε).mono' ?_ ?_
    · exact (hu.aestronglyMeasurable.norm.mul hdiff.aestronglyMeasurable)
    · filter_upwards [hg, hh] with x h1 h2
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_abs, div_eq_mul_inv]
      have := (inv_diff_le hε h1 h2).2
      rw [one_div] at this
      exact mul_le_mul_of_nonneg_left this (abs_nonneg _)
  have iBd : Integrable Bd μ := by
    have a1 : Integrable (fun x => ε⁻¹ * |Fp x|) μ := ((L1.integrable_coeFn Fp).abs).const_mul _
    have a2 := bdd_mul hv'
    have a3 : Integrable (fun x => B / ε ^ 2 * |Fq x|) μ := ((integrable_Lp2 Fq).abs).const_mul _
    have a4 : Integrable (fun x => ε⁻¹ * (|w x * g' x| * |(g x)⁻¹ - (h x)⁻¹|)) μ :=
      (bdd_mul hwg).const_mul _
    exact ((a1.add a2).add a3).add a4
  have hpt : ∀ᵐ x ∂μ, ‖K x‖ ≤ Bd x := by
    filter_upwards [hg, hh, hB, Lp.coeFn_sub (δ⁻¹ • (v - w)) v',
      Lp.coeFn_smul δ⁻¹ (v - w), Lp.coeFn_sub v w, Lp.coeFn_sub (δ⁻¹ • (g - h)) g',
      Lp.coeFn_smul δ⁻¹ (g - h), Lp.coeFn_sub g h] with x h1 h2 h3 e1 e2 e3 e4 e5 e6
    have hP : Fp x = δ⁻¹ * (v x - w x) - v' x := by
      rw [hFp, e1, Pi.sub_apply, e2, Pi.smul_apply, e3, Pi.sub_apply, smul_eq_mul]
    have hQ : Fq x = δ⁻¹ * (g x - h x) - g' x := by
      rw [hFq, e4, Pi.sub_apply, e5, Pi.smul_apply, e6, Pi.sub_apply, smul_eq_mul]
    have g0 : 0 < g x := lt_of_lt_of_le hε h1
    have h0 : 0 < h x := lt_of_lt_of_le hε h2
    have hid : K x = (δ⁻¹ * (v x - w x) - v' x) * (g x)⁻¹ + v' x * ((g x)⁻¹ - (h x)⁻¹) -
        w x * (δ⁻¹ * (g x - h x) - g' x) * (g x * h x)⁻¹ -
        w x * g' x * ((g x * h x)⁻¹ - ((h x) ^ 2)⁻¹) := by
      simp only [hK]; field_simp; ring
    rw [Real.norm_eq_abs, hid, ← hP, ← hQ]
    have ig : (g x)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε h1
    have igh : (g x * h x)⁻¹ ≤ ε⁻¹ * ε⁻¹ := by
      rw [mul_inv]; exact mul_le_mul ig (inv_anti₀ hε h2) (inv_pos.2 h0).le (inv_pos.2 hε).le
    have key : (g x * h x)⁻¹ - ((h x) ^ 2)⁻¹ = (h x)⁻¹ * ((g x)⁻¹ - (h x)⁻¹) := by
      field_simp
    have ih : (h x)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε h2
    have t1 : |Fp x * (g x)⁻¹| ≤ ε⁻¹ * |Fp x| := by
      rw [abs_mul, abs_of_pos (inv_pos.2 g0), mul_comm]
      exact mul_le_mul_of_nonneg_right ig (abs_nonneg _) |>.trans_eq (mul_comm _ _) |>.trans_eq (mul_comm _ _)
    have t3 : |w x * Fq x * (g x * h x)⁻¹| ≤ B / ε ^ 2 * |Fq x| := by
      rw [abs_mul, abs_mul, abs_of_pos (inv_pos.2 (mul_pos g0 h0))]
      have : |w x| * |Fq x| * (g x * h x)⁻¹ ≤ B * |Fq x| * (ε⁻¹ * ε⁻¹) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right h3 (abs_nonneg _)) igh (inv_pos.2 (mul_pos g0 h0)).le
          (mul_nonneg hB0 (abs_nonneg _))
      calc _ ≤ _ := this
        _ = B / ε ^ 2 * |Fq x| := by field_simp
    have t4 : |w x * g' x * ((g x * h x)⁻¹ - ((h x) ^ 2)⁻¹)| ≤
        ε⁻¹ * (|w x * g' x| * |(g x)⁻¹ - (h x)⁻¹|) := by
      rw [key, ← mul_assoc, abs_mul, abs_mul, abs_of_pos (inv_pos.2 h0)]
      calc |w x * g' x| * (h x)⁻¹ * |(g x)⁻¹ - (h x)⁻¹| ≤ |w x * g' x| * ε⁻¹ * |(g x)⁻¹ - (h x)⁻¹| := by
            gcongr
        _ = _ := by ring
    have t2 : |v' x * ((g x)⁻¹ - (h x)⁻¹)| = |v' x| * |(g x)⁻¹ - (h x)⁻¹| := abs_mul _ _
    calc _ ≤ |Fp x * (g x)⁻¹ + v' x * ((g x)⁻¹ - (h x)⁻¹) - w x * Fq x * (g x * h x)⁻¹| +
          |w x * g' x * ((g x * h x)⁻¹ - ((h x) ^ 2)⁻¹)| := abs_sub _ _
      _ ≤ (|Fp x * (g x)⁻¹| + |v' x * ((g x)⁻¹ - (h x)⁻¹)|) + |w x * Fq x * (g x * h x)⁻¹| +
          |w x * g' x * ((g x * h x)⁻¹ - ((h x) ^ 2)⁻¹)| := by
          gcongr; exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl) |>.trans_eq (by ring)
      _ ≤ Bd x := by simp only [hBd]; linarith
  have hmain : |∫ x, K x ∂μ| ≤ ∫ x, Bd x ∂μ := by
    rw [← Real.norm_eq_abs]; exact norm_integral_le_of_norm_le iBd hpt
  have hsum : ∫ x, Bd x ∂μ = ε⁻¹ * ∫ x, |Fp x| ∂μ + ∫ x, |v' x| * |(g x)⁻¹ - (h x)⁻¹| ∂μ +
      B / ε ^ 2 * ∫ x, |Fq x| ∂μ + ε⁻¹ * ∫ x, |w x * g' x| * |(g x)⁻¹ - (h x)⁻¹| ∂μ := by
    have a1 : Integrable (fun x => ε⁻¹ * |Fp x|) μ := ((L1.integrable_coeFn Fp).abs).const_mul _
    have a2 := bdd_mul hv'
    have a3 : Integrable (fun x => B / ε ^ 2 * |Fq x|) μ := ((integrable_Lp2 Fq).abs).const_mul _
    have a4 : Integrable (fun x => ε⁻¹ * (|w x * g' x| * |(g x)⁻¹ - (h x)⁻¹|)) μ :=
      (bdd_mul hwg).const_mul _
    have b12 : Integrable (fun x => ε⁻¹ * |Fp x| + |v' x| * |(g x)⁻¹ - (h x)⁻¹|) μ := a1.add a2
    have b123 : Integrable (fun x => ε⁻¹ * |Fp x| + |v' x| * |(g x)⁻¹ - (h x)⁻¹| +
        B / ε ^ 2 * |Fq x|) μ := b12.add a3
    simp only [hBd]
    rw [integral_add b123 a4, integral_add b12 a3, integral_add a1 a2,
      integral_const_mul, integral_const_mul, integral_const_mul]
  rw [hKint]
  refine hmain.trans ?_
  rw [hsum, ← norm_L1_eq Fp]
  have := integral_abs_le' Fq
  have h5 : B / ε ^ 2 * ∫ x, |Fq x| ∂μ ≤ B / ε ^ 2 * (‖Fq‖ * oneNorm μ) :=
    mul_le_mul_of_nonneg_left this (by positivity)
  simp only [div_eq_mul_inv] at h5 ⊢
  linarith

theorem tendsto_div_diff {l : Filter ℝ} {v : ℝ → Lp ℝ 1 μ} {g : ℝ → Lp ℝ 2 μ} {s : ℝ}
    (hv : Tendsto v l (𝓝 (v s))) (hg : Tendsto g l (𝓝 (g s))) {ε : ℝ} (hε : 0 < ε)
    (hge : ∀ r, ∀ᵐ x ∂μ, ε ≤ g r x) :
    Tendsto (fun r => (∫ x, v r x / g r x ∂μ) - ∫ x, v s x / g s x ∂μ) l (𝓝 0) := by
  have h1 : Tendsto (fun r => ‖v r - v s‖ / ε) l (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hv).div_const ε
    simpa using this
  have h2 := tendsto_inv_diff hg hε hge (L1.integrable_coeFn (v s))
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero_norm (fun r => ?_) h3
  rw [integral_div_sub (v r) (v s) hε (hge r) (hge s), Real.norm_eq_abs]
  refine (abs_add_le _ _).trans (add_le_add (abs_integral_div_diff_le (v r) (v s) hε (hge r)) ?_)
  refine (abs_integral_le_integral_abs).trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun x => ?_)))
  simp only [abs_mul]

theorem continuous_integral_div {v : ℝ → Lp ℝ 1 μ} {g : ℝ → Lp ℝ 2 μ} (hv : Continuous v)
    (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) (hge : ∀ r, ∀ᵐ x ∂μ, ε ≤ g r x) :
    Continuous fun r => ∫ x, v r x / g r x ∂μ := by
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have := tendsto_div_diff (hv.tendsto s) (hg.tendsto s) hε hge
  simpa [Real.norm_eq_abs] using this.abs

/-- **Differentiation of `r ↦ ∫ u_r/g_r`**: `u` differentiable in `L¹`, `g ≥ ε` differentiable in `L²`,
`u_s ∈ L^∞`; derivative `∫ u'/g_s - ∫ u_s g'/g_s²`. -/
theorem hasDerivAt_integral_div {v : ℝ → Lp ℝ 1 μ} {v' : Lp ℝ 1 μ} {g : ℝ → Lp ℝ 2 μ} {g' : Lp ℝ 2 μ}
    {s : ℝ} (hv : HasDerivAt v v' s) (hg : HasDerivAt g g' s) {ε : ℝ} (hε : 0 < ε)
    (hge : ∀ r, ∀ᵐ x ∂μ, ε ≤ g r x) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ᵐ x ∂μ, |v s x| ≤ B) :
    HasDerivAt (fun r => ∫ x, v r x / g r x ∂μ)
      ((∫ x, v' x / g s x ∂μ) - ∫ x, v s x * g' x / (g s x) ^ 2 ∂μ) s := by
  rw [hasDerivAt_iff_tendsto_slope]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hgc : Tendsto g (𝓝[≠] s) (𝓝 (g s)) := hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hvs := hasDerivAt_iff_tendsto_slope.1 hv
  have hgs := hasDerivAt_iff_tendsto_slope.1 hg
  have c1 : Tendsto (fun r => ‖(r - s)⁻¹ • (v r - v s) - v'‖ / ε) (𝓝[≠] s) (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hvs).div_const ε
    simpa [slope_def_module] using this
  have c3 : Tendsto (fun r => B / ε ^ 2 * (‖(r - s)⁻¹ • (g r - g s) - g'‖ * oneNorm μ))
      (𝓝[≠] s) (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 hgs).mul_const (oneNorm μ)).const_mul (B / ε ^ 2)
    simpa [slope_def_module] using this
  have c2 := tendsto_inv_diff hgc hε hge (L1.integrable_coeFn v')
  have c4 := (tendsto_inv_diff hgc hε hge
    (w := fun x => v s x * g' x) (by
      refine ((integrable_Lp2 g').abs.const_mul B).mono'
        ((L1.integrable_coeFn (v s)).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g')) ?_
      filter_upwards [hB] with x hx
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))).const_mul ε⁻¹
  have hsum := (((c1.add c2).add c3).add c4)
  simp only [add_zero, mul_zero] at hsum
  refine squeeze_zero_norm' ?_ hsum
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hδ : r - s ≠ 0 := sub_ne_zero.2 hr
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  have := slope_bound (v r) (v s) v' (g r) (g s) g' hε (hge r) (hge s) hB0 hB hδ
  simpa [slope_def_module, smul_eq_mul] using this


end MarkovTriple.BGL
