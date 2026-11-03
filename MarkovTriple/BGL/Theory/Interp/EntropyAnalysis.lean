import Mathlib
import MarkovTriple.BGL.Theory.Interp.Pairing

/-!
# Analytic lemmas for the entropy interpolation (BGL Prop. 5.5.3 / 5.7.1; no Markov triple here)

* `cs_facts`: a `C^∞` function with compact support is bounded, Lipschitz, with Lipschitz derivative, and has the quadratic
  Taylor remainder estimate;
* `hasDerivAt_integral_smooth`: on a finite measure space, if `g : ℝ → L²` is differentiable at `s` then
  `r ↦ ∫ Φ(g_r)` is differentiable at `s` with derivative `∫ Φ'(g_s) g'` (`Φ ∈ C_c^∞`);
* `continuous_integral_smooth`: the corresponding continuity statement.
-/

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

namespace MarkovTriple.BGL

section smooth

variable {Φ : ℝ → ℝ}

lemma cs_facts (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ) :
    ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧ (∀ a, |Φ a| ≤ K1) ∧ (∀ a, |deriv Φ a| ≤ K1) ∧
      (∀ a b, |Φ b - Φ a| ≤ K1 * |b - a|) ∧
      (∀ a b, |Φ b - Φ a - deriv Φ a * (b - a)| ≤ K2 * (b - a) ^ 2) := by
  have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv Φ) := (contDiff_infty_iff_deriv.1 h).2
  have hdc : HasCompactSupport (deriv Φ) := hc.deriv
  obtain ⟨C0, hC0⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc h (by simp)
  obtain ⟨C1, hC1⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hdc hd (by simp)
  obtain ⟨B0, hB0⟩ := h.continuous.bounded_above_of_compact_support hc
  obtain ⟨B1, hB1⟩ := hd.continuous.bounded_above_of_compact_support hdc
  refine ⟨max (max B0 B1) C0, C1, le_max_of_le_right C0.2, C1.2, fun a => ?_, fun a => ?_,
    fun a b => ?_, fun a b => ?_⟩
  · have := hB0 a; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have := hB1 a; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_right _ _).trans (le_max_left _ _))
  · have := hC0.dist_le_mul b a
    rw [Real.dist_eq, Real.dist_eq] at this
    exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _))
  · -- mean value theorem for y ↦ Φ y - Φ'(a) y
    have hdiff : ∀ y, DifferentiableAt ℝ (fun y => Φ y - deriv Φ a * y) y := fun y =>
      ((h.differentiable (by simp)) y).sub ((differentiableAt_id).const_mul _)
    have hder : ∀ y, deriv (fun y => Φ y - deriv Φ a * y) y = deriv Φ y - deriv Φ a := by
      intro y
      have : HasDerivAt (fun y => Φ y - deriv Φ a * y) (deriv Φ y - deriv Φ a * 1) y :=
        ((h.differentiable (by simp)) y).hasDerivAt.sub ((hasDerivAt_id y).const_mul (deriv Φ a))
      rw [this.deriv, mul_one]
    have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := fun y => Φ y - deriv Φ a * y)
      (C := C1 * |b - a|) (s := Set.uIcc a b) (x := a) (y := b) (fun y _ => hdiff y)
      (fun y hy => by
        rw [hder, Real.norm_eq_abs]
        have := hC1.dist_le_mul y a
        rw [Real.dist_eq, Real.dist_eq] at this
        refine this.trans (mul_le_mul_of_nonneg_left ?_ C1.2)
        rcases le_total a b with hab | hab
        · rw [Set.uIcc_of_le hab] at hy
          rw [abs_of_nonneg (sub_nonneg.2 hab), abs_of_nonneg (sub_nonneg.2 hy.1)]; linarith [hy.2]
        · rw [Set.uIcc_of_ge hab] at hy
          rw [abs_of_nonpos (sub_nonpos.2 hab), abs_of_nonpos (sub_nonpos.2 hy.2)]
          linarith [hy.1])
      (convex_uIcc a b) Set.left_mem_uIcc Set.right_mem_uIcc
    rw [Real.norm_eq_abs] at key
    have e : Φ b - Φ a - deriv Φ a * (b - a) = (Φ b - deriv Φ a * b) - (Φ a - deriv Φ a * a) := by ring
    rw [e]
    calc _ ≤ (C1 : ℝ) * |b - a| * |b - a| := key
      _ = C1 * (b - a) ^ 2 := by rw [mul_assoc, ← sq_abs (b - a), sq]

end smooth


section finite

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {Φ : ℝ → ℝ}

omit [IsFiniteMeasure μ] in
lemma sq_integral_eq (f : Lp ℝ 2 μ) : ∫ x, (f x) ^ 2 ∂μ = ‖f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun x => by simp [sq])

lemma integrable_comp_Lp (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ) (f : Lp ℝ 2 μ) :
    Integrable (fun x => Φ (f x)) μ := by
  obtain ⟨K1, -, -, -, hΦb, -⟩ := cs_facts h hc
  exact Integrable.of_bound (h.continuous.comp_aestronglyMeasurable
    (Lp.aestronglyMeasurable f)) K1 (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hΦb _)

lemma memLp_deriv_comp (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ) (f : Lp ℝ 2 μ) :
    MemLp (fun x => deriv Φ (f x)) 2 μ := by
  obtain ⟨K1, -, -, -, -, hΦ'b, -⟩ := cs_facts h hc
  have hm' : Continuous (deriv Φ) := (contDiff_infty_iff_deriv.1 h).2.continuous
  exact MemLp.of_bound (hm'.comp_aestronglyMeasurable (Lp.aestronglyMeasurable f)) K1
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hΦ'b _)

/-- the sign function (measurable, `|σ| ≤ 1`, `σ(y) y = |y|`). -/
noncomputable def sgn (y : ℝ) : ℝ := (if 0 < y then 1 else 0) - (if y < 0 then 1 else 0)

lemma measurable_sgn : Measurable sgn := by
  unfold sgn
  exact (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const).sub (Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const measurable_const)

lemma abs_sgn_le (y : ℝ) : |sgn y| ≤ 1 := by
  unfold sgn
  by_cases h1 : 0 < y
  · simp [h1, not_lt.2 h1.le]
  · by_cases h2 : y < 0 <;> simp [h1, h2]

lemma sgn_mul (y : ℝ) : sgn y * y = |y| := by
  unfold sgn
  rcases lt_trichotomy y 0 with h | h | h
  · simp [h, not_lt.2 h.le, abs_of_neg h]
  · simp [h]
  · simp [h, not_lt.2 h.le, abs_of_pos h]

/-- `L¹ ≤ L²` on a finite measure space (constant depends only on `μ`). -/
lemma integral_abs_le (f : Lp ℝ 2 μ) :
    ∫ x, |f x| ∂μ ≤ ‖f‖ * ‖(memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ).toLp _‖ := by
  have hsm : AEStronglyMeasurable (fun x => sgn (f x)) μ :=
    (measurable_sgn.comp_aemeasurable (Lp.aestronglyMeasurable f).aemeasurable).aestronglyMeasurable
  have hsg : MemLp (fun x => sgn (f x)) 2 μ :=
    MemLp.of_bound hsm 1 (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_sgn_le _)
  have e : ∫ x, |f x| ∂μ = ⟪f, hsg.toLp _⟫_ℝ := by
    rw [inner_eq_integral f hsg]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only; rw [mul_comm, sgn_mul])
  rw [e]
  refine (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [hsg.coeFn_toLp, (memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ).coeFn_toLp]
    with x h1 h2
  rw [h1, h2, Real.norm_eq_abs, Real.norm_eq_abs]; simpa using abs_sgn_le _

/-- **Chain rule for `r ↦ ∫ Φ(g_r)`** (finite measure, `Φ ∈ C_c^∞`, `g` differentiable in `L²`). -/
theorem hasDerivAt_integral_smooth (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    {g : ℝ → Lp ℝ 2 μ} {g' : Lp ℝ 2 μ} {s : ℝ} (hg : HasDerivAt g g' s) :
    HasDerivAt (fun r => ∫ x, Φ (g r x) ∂μ) (∫ x, deriv Φ (g s x) * g' x ∂μ) s := by
  obtain ⟨K1, K2, hK1, hK2, hΦb, hΦ'b, hΦL, hrem⟩ := cs_facts h hc
  have hm : Measurable Φ := h.continuous.measurable
  have hΨ := memLp_deriv_comp h hc (g s)
  set Ψc : Lp ℝ 2 μ := hΨ.toLp _ with hΨc
  set N := ‖Ψc‖ with hN
  have hI : Integrable (fun x => deriv Φ (g s x) * g' x) μ :=
    hΨ.integrable_mul (Lp.memLp g')
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc0
  set A := ‖g'‖ + 1 with hA
  have hA0 : 0 < A := by positivity
  have hc' : 0 < c / (2 * (N + 1)) := by positivity
  have hη : 0 < c / (2 * (K2 * A ^ 2 + 1)) := by positivity
  filter_upwards [Asymptotics.isLittleO_iff.1 (hasDerivAt_iff_isLittleO.1 hg) hc',
    Asymptotics.isLittleO_iff.1 (hasDerivAt_iff_isLittleO.1 hg) one_pos,
    Metric.ball_mem_nhds s hη] with r h1 h2 h3
  set δ := r - s with hδ
  set d : Lp ℝ 2 μ := g r - g s - δ • g' with hd
  have hd1 : ‖d‖ ≤ c / (2 * (N + 1)) * |δ| := by
    have : ‖d‖ ≤ c / (2 * (N + 1)) * ‖δ‖ := by simpa [hd, hδ] using h1
    simpa [Real.norm_eq_abs] using this
  have hd2 : ‖g r - g s‖ ≤ A * |δ| := by
    have h2' : ‖d‖ ≤ |δ| := by simpa [hd, hδ, Real.norm_eq_abs] using h2
    have : g r - g s = d + δ • g' := by simp [hd]
    rw [this]
    calc ‖d + δ • g'‖ ≤ ‖d‖ + ‖δ • g'‖ := norm_add_le _ _
      _ ≤ |δ| + |δ| * ‖g'‖ := by rw [norm_smul, Real.norm_eq_abs]; linarith
      _ = A * |δ| := by rw [hA]; ring
  have hδη : |δ| < c / (2 * (K2 * A ^ 2 + 1)) := by
    simpa [Metric.mem_ball, Real.dist_eq, hδ] using h3
  -- the pointwise decomposition
  have hdae : (d : α → ℝ) =ᵐ[μ] fun x => g r x - g s x - δ * g' x := by
    filter_upwards [Lp.coeFn_sub (g r - g s) (δ • g'), Lp.coeFn_sub (g r) (g s),
      Lp.coeFn_smul δ g'] with x e1 e2 e3
    rw [hd, e1, Pi.sub_apply, e2, e3]; simp
  set R : α → ℝ := fun x => Φ (g r x) - Φ (g s x) - deriv Φ (g s x) * (g r x - g s x) with hR
  have hRi : Integrable R μ :=
    ((integrable_comp_Lp h hc (g r)).sub (integrable_comp_Lp h hc (g s))).sub
      (hΨ.integrable_mul ((Lp.memLp (g r)).sub (Lp.memLp (g s))))
  have hmain : (∫ x, Φ (g r x) ∂μ) - (∫ x, Φ (g s x) ∂μ) - δ • ∫ x, deriv Φ (g s x) * g' x ∂μ =
      (∫ x, R x ∂μ) + ∫ x, d x * deriv Φ (g s x) ∂μ := by
    have hdi : Integrable (fun x => d x * deriv Φ (g s x)) μ := (Lp.memLp d).integrable_mul hΨ
    have hf : Integrable (fun x => Φ (g r x) - Φ (g s x)) μ :=
      (integrable_comp_Lp h hc (g r)).sub (integrable_comp_Lp h hc (g s))
    have hg2 : Integrable (fun x => δ • (deriv Φ (g s x) * g' x)) μ := hI.smul δ
    rw [← integral_add hRi hdi, ← integral_sub (integrable_comp_Lp h hc (g r))
      (integrable_comp_Lp h hc (g s)), ← integral_smul, ← integral_sub hf hg2]
    refine integral_congr_ae ?_
    filter_upwards [hdae] with x hx
    simp only [hR, smul_eq_mul]
    rw [hx]; ring
  have hRb : |∫ x, R x ∂μ| ≤ K2 * ‖g r - g s‖ ^ 2 := by
    rw [← sq_integral_eq (g r - g s), ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) ?_ ?_)
    · exact (((Lp.memLp (g r - g s)).integrable_sq).const_mul K2)
    · filter_upwards [Lp.coeFn_sub (g r) (g s)] with x hx
      have := hrem (g s x) (g r x)
      simp only [hR]
      rw [hx]; simpa [Pi.sub_apply] using this
  have hdb : |∫ x, d x * deriv Φ (g s x) ∂μ| ≤ ‖d‖ * N := by
    have : ∫ x, d x * deriv Φ (g s x) ∂μ = ⟪d, Ψc⟫_ℝ := (inner_eq_integral d hΨ).symm
    rw [this]; exact (abs_real_inner_le_norm _ _)
  have hgoal : ‖(∫ x, Φ (g r x) ∂μ) - (∫ x, Φ (g s x) ∂μ) - δ • ∫ x, deriv Φ (g s x) * g' x ∂μ‖
      ≤ c * ‖δ‖ := by
    rw [hmain, Real.norm_eq_abs, Real.norm_eq_abs]
    refine (abs_add_le _ _).trans ?_
    have e1 : K2 * ‖g r - g s‖ ^ 2 ≤ K2 * A ^ 2 * |δ| * |δ| := by
      have : ‖g r - g s‖ ^ 2 ≤ (A * |δ|) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd2 2
      nlinarith [mul_le_mul_of_nonneg_left this hK2]
    have e2 : K2 * A ^ 2 * |δ| ≤ c / 2 := by
      have := mul_le_mul_of_nonneg_left hδη.le (by positivity : 0 ≤ K2 * A ^ 2)
      have e : K2 * A ^ 2 * (c / (2 * (K2 * A ^ 2 + 1))) ≤ c / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [mul_nonneg hK2 (sq_nonneg A), hc0.le]
      linarith
    have e3 : ‖d‖ * N ≤ c / 2 * |δ| := by
      calc ‖d‖ * N ≤ (c / (2 * (N + 1)) * |δ|) * N :=
            mul_le_mul_of_nonneg_right hd1 (norm_nonneg _)
        _ = c / 2 * |δ| * (N / (N + 1)) := by field_simp
        _ ≤ c / 2 * |δ| * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            rw [div_le_one (by positivity)]; linarith
        _ = c / 2 * |δ| := mul_one _
    calc |∫ x, R x ∂μ| + |∫ x, d x * deriv Φ (g s x) ∂μ|
        ≤ K2 * A ^ 2 * |δ| * |δ| + c / 2 * |δ| := add_le_add (hRb.trans e1) (hdb.trans e3)
      _ ≤ c / 2 * |δ| + c / 2 * |δ| := by
          nlinarith [abs_nonneg δ]
      _ = c * ‖δ‖ := by rw [Real.norm_eq_abs]; ring
  exact hgoal

/-- Continuity of `r ↦ ∫ Φ(g_r)` for `g` continuous in `L²`. -/
theorem continuous_integral_smooth (h : ContDiff ℝ (⊤ : ℕ∞) Φ) (hc : HasCompactSupport Φ)
    {g : ℝ → Lp ℝ 2 μ} (hg : Continuous g) : Continuous fun r => ∫ x, Φ (g r x) ∂μ := by
  obtain ⟨K1, K2, hK1, hK2, hΦb, hΦ'b, hΦL, hrem⟩ := cs_facts h hc
  rw [continuous_iff_continuousAt]
  intro s
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h0 : Tendsto (fun r => ‖g r - g s‖) (𝓝 s) (𝓝 0) := by
    simpa using tendsto_iff_norm_sub_tendsto_zero.1 (hg.tendsto s)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun r => ?_)
    (by simpa using (h0.mul_const (K1 * ‖(memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ).toLp _‖)))
  rw [Real.norm_eq_abs, ← integral_sub (integrable_comp_Lp h hc (g r)) (integrable_comp_Lp h hc (g s))]
  have hle : ∫ x, |g r x - g s x| ∂μ ≤ ‖g r - g s‖ *
      ‖(memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ).toLp _‖ := by
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (integral_abs_le (g r - g s))
    filter_upwards [Lp.coeFn_sub (g r) (g s)] with x hx
    rw [hx]; rfl
  calc |∫ x, (Φ (g r x) - Φ (g s x)) ∂μ| ≤ ∫ x, |Φ (g r x) - Φ (g s x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, K1 * |g r x - g s x| ∂μ := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) ?_
          (Eventually.of_forall fun x => hΦL _ _)
        exact (((Lp.memLp (g r)).sub (Lp.memLp (g s))).integrable one_le_two).abs.const_mul K1
    _ = K1 * ∫ x, |g r x - g s x| ∂μ := integral_const_mul _ _
    _ ≤ K1 * (‖g r - g s‖ * ‖(memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ).toLp _‖) :=
        mul_le_mul_of_nonneg_left hle hK1
    _ = ‖g r - g s‖ * (K1 * ‖(memLp_const (1 : ℝ) : MemLp (fun _ : α => (1 : ℝ)) 2 μ).toLp _‖) := by ring

end finite

end MarkovTriple.BGL
