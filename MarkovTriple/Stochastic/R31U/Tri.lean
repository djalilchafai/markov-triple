import Mathlib

/-!
# Round 31 (U), part 1: the trilinear form `∫ a b c` on `L²` with one bounded factor

`Λ(a,b,c) = ∫ a b c dμ` is not a bounded trilinear form on `L²`, but `|Λ(a,b,c)| ≤ M ‖a‖₂ ‖c‖₂` as soon as `|b| ≤ M` a.e.
(Cauchy-Schwarz).  This is exactly what is needed to differentiate `r ↦ ∫ k_r g_r²` (the interpolation of BGL Thm 4.7.2 /
proof of Thm 3.3.18) along `L²`-differentiable curves that are uniformly bounded in `L^∞`.
-/

open MeasureTheory Filter Topology
open scoped InnerProductSpace

namespace MarkovTriple.Stochastic.R31U

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma int3_memLp (a b : Lp ℝ 2 μ) {M : ℝ} (hb : ∀ᵐ x ∂μ, |(b : α → ℝ) x| ≤ M) :
    MemLp (fun x => (a : α → ℝ) x * (b : α → ℝ) x) 2 μ := by
  refine (Lp.memLp a).of_le_mul (c := M) ((Lp.memLp a).aestronglyMeasurable.mul
    (Lp.memLp b).aestronglyMeasurable) ?_
  filter_upwards [hb] with x hx
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

lemma int3_integrable (a b c : Lp ℝ 2 μ) {M : ℝ} (hb : ∀ᵐ x ∂μ, |(b : α → ℝ) x| ≤ M) :
    Integrable (fun x => (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x) μ := by
  have h := (int3_memLp a b hb).integrable_mul (Lp.memLp c)
  exact h

lemma int3_eq_inner (a b c : Lp ℝ 2 μ) {M : ℝ} (hb : ∀ᵐ x ∂μ, |(b : α → ℝ) x| ≤ M) :
    ∫ x, (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x ∂μ =
      ⟪c, (int3_memLp a b hb).toLp _⟫_ℝ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [(int3_memLp a b hb).coeFn_toLp] with x hx
  rw [hx]; simp

/-- `|∫ a b c| ≤ M ‖a‖ ‖c‖` when `|b| ≤ M`. -/
lemma int3_le (a b c : Lp ℝ 2 μ) {M : ℝ} (hb : ∀ᵐ x ∂μ, |(b : α → ℝ) x| ≤ M) :
    |∫ x, (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x ∂μ| ≤ M * ‖a‖ * ‖c‖ := by
  rw [int3_eq_inner a b c hb]
  have h1 := abs_real_inner_le_norm c ((int3_memLp a b hb).toLp _)
  have h2 : ‖(int3_memLp a b hb).toLp (fun x => (a : α → ℝ) x * (b : α → ℝ) x)‖ ≤ M * ‖a‖ := by
    refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
    filter_upwards [(int3_memLp a b hb).coeFn_toLp, hb] with x h1 h2
    rw [h1, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
  calc _ ≤ ‖c‖ * ‖(int3_memLp a b hb).toLp (fun x => (a : α → ℝ) x * (b : α → ℝ) x)‖ := h1
    _ ≤ ‖c‖ * (M * ‖a‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = M * ‖a‖ * ‖c‖ := by ring

lemma int3_integrable_left (a b c : Lp ℝ 2 μ) {M : ℝ} (ha : ∀ᵐ x ∂μ, |(a : α → ℝ) x| ≤ M) :
    Integrable (fun x => (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x) μ :=
  (int3_integrable b a c ha).congr (Eventually.of_forall fun x => by simp only; ring)

lemma int3_integrable_right (a b c : Lp ℝ 2 μ) {M : ℝ} (hc : ∀ᵐ x ∂μ, |(c : α → ℝ) x| ≤ M) :
    Integrable (fun x => (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x) μ :=
  (int3_integrable a c b hc).congr (Eventually.of_forall fun x => by simp only; ring)

lemma int3_le_left (a b c : Lp ℝ 2 μ) {M : ℝ} (ha : ∀ᵐ x ∂μ, |(a : α → ℝ) x| ≤ M) :
    |∫ x, (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x ∂μ| ≤ M * ‖b‖ * ‖c‖ := by
  have := int3_le b a c ha
  have e : ∫ x, (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x ∂μ =
      ∫ x, (b : α → ℝ) x * (a : α → ℝ) x * (c : α → ℝ) x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_); simp only; ring
  rw [e]; exact this

lemma int3_le_right (a b c : Lp ℝ 2 μ) {M : ℝ} (hc : ∀ᵐ x ∂μ, |(c : α → ℝ) x| ≤ M) :
    |∫ x, (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x ∂μ| ≤ M * ‖a‖ * ‖b‖ := by
  have := int3_le a c b hc
  have e : ∫ x, (a : α → ℝ) x * (b : α → ℝ) x * (c : α → ℝ) x ∂μ =
      ∫ x, (a : α → ℝ) x * (c : α → ℝ) x * (b : α → ℝ) x ∂μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_); simp only; ring
  rw [e]; exact this

lemma coe_slope_err (A A0 a' : Lp ℝ 2 μ) (δ : ℝ) :
    ((δ⁻¹ • (A - A0) - a' : Lp ℝ 2 μ) : α → ℝ) =ᵐ[μ]
      fun x => δ⁻¹ * ((A : α → ℝ) x - (A0 : α → ℝ) x) - (a' : α → ℝ) x := by
  filter_upwards [Lp.coeFn_sub (δ⁻¹ • (A - A0)) a', Lp.coeFn_smul δ⁻¹ (A - A0),
    Lp.coeFn_sub A A0] with x h1 h2 h3
  rw [h1]
  simp only [Pi.sub_apply]
  rw [h2]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h3]; simp only [Pi.sub_apply]

/-- the six-term estimate of the slope of `Λ` -/
lemma tri_slope_bound (A B C A0 B0 C0 a' b' c' : Lp ℝ 2 μ) (δ M : ℝ)
    (hB : ∀ᵐ x ∂μ, |(B : α → ℝ) x| ≤ M)
    (hC : ∀ᵐ x ∂μ, |(C : α → ℝ) x| ≤ M) (hA0 : ∀ᵐ x ∂μ, |(A0 : α → ℝ) x| ≤ M)
    (hB0 : ∀ᵐ x ∂μ, |(B0 : α → ℝ) x| ≤ M) :
    |δ⁻¹ * (∫ x, (A : α → ℝ) x * B x * C x ∂μ - ∫ x, (A0 : α → ℝ) x * B0 x * C0 x ∂μ) -
        ((∫ x, (a' : α → ℝ) x * B0 x * C0 x ∂μ) + (∫ x, (A0 : α → ℝ) x * b' x * C0 x ∂μ) +
          ∫ x, (A0 : α → ℝ) x * B0 x * c' x ∂μ)| ≤
      M * (‖δ⁻¹ • (A - A0) - a'‖ * ‖C‖ + ‖a'‖ * ‖B - B0‖ + ‖a'‖ * ‖C - C0‖ +
        ‖δ⁻¹ • (B - B0) - b'‖ * ‖C‖ + ‖b'‖ * ‖C - C0‖ + ‖B0‖ * ‖δ⁻¹ • (C - C0) - c'‖) := by
  set ea : Lp ℝ 2 μ := δ⁻¹ • (A - A0) - a' with hea
  set eb : Lp ℝ 2 μ := δ⁻¹ • (B - B0) - b' with heb
  set ec : Lp ℝ 2 μ := δ⁻¹ • (C - C0) - c' with hec
  set dB : Lp ℝ 2 μ := B - B0 with hdB
  set dC : Lp ℝ 2 μ := C - C0 with hdC
  have cea : (ea : α → ℝ) =ᵐ[μ] _ := coe_slope_err A A0 a' δ
  have ceb : (eb : α → ℝ) =ᵐ[μ] _ := coe_slope_err B B0 b' δ
  have cec : (ec : α → ℝ) =ᵐ[μ] _ := coe_slope_err C C0 c' δ
  have cdB : (dB : α → ℝ) =ᵐ[μ] _ := Lp.coeFn_sub B B0
  have cdC : (dC : α → ℝ) =ᵐ[μ] _ := Lp.coeFn_sub C C0
  -- integrability
  have i1 := int3_integrable ea B C hB
  have i2 := int3_integrable_right a' dB C hC
  have i3 := int3_integrable a' B0 dC hB0
  have i4 := int3_integrable_left A0 eb C hA0
  have i5 := int3_integrable_left A0 b' dC hA0
  have i6 := int3_integrable_left A0 B0 ec hA0
  have iX := int3_integrable A B C hB
  have iY := int3_integrable A0 B0 C0 hB0
  have iP := int3_integrable a' B0 C0 hB0
  have iQ := int3_integrable_left A0 b' C0 hA0
  have iR := int3_integrable_left A0 B0 c' hA0
  have hsum : ∫ x, ((ea : α → ℝ) x * B x * C x + (a' : α → ℝ) x * dB x * C x + a' x * B0 x * dC x +
      A0 x * eb x * C x + A0 x * b' x * dC x + A0 x * B0 x * ec x) ∂μ =
      δ⁻¹ * (∫ x, (A : α → ℝ) x * B x * C x ∂μ - ∫ x, (A0 : α → ℝ) x * B0 x * C0 x ∂μ) -
        ((∫ x, (a' : α → ℝ) x * B0 x * C0 x ∂μ) + (∫ x, (A0 : α → ℝ) x * b' x * C0 x ∂μ) +
          ∫ x, (A0 : α → ℝ) x * B0 x * c' x ∂μ) := by
    have e1 : ∫ x, ((ea : α → ℝ) x * B x * C x + (a' : α → ℝ) x * dB x * C x + a' x * B0 x * dC x +
        A0 x * eb x * C x + A0 x * b' x * dC x + A0 x * B0 x * ec x) ∂μ =
        ∫ x, (δ⁻¹ * ((A : α → ℝ) x * B x * C x - A0 x * B0 x * C0 x) -
          (a' x * B0 x * C0 x + A0 x * b' x * C0 x + A0 x * B0 x * c' x)) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [cea, ceb, cec, cdB, cdC] with x h1 h2 h3 h4 h5
      simp only [h1, h2, h3, h4, h5, Pi.sub_apply]
      ring
    have iL : Integrable (fun x => δ⁻¹ * ((A : α → ℝ) x * B x * C x - A0 x * B0 x * C0 x)) μ :=
      (iX.sub iY).const_mul _
    have iPQ : Integrable (fun x => (a' : α → ℝ) x * B0 x * C0 x + A0 x * b' x * C0 x) μ := iP.add iQ
    have iPQR : Integrable (fun x => (a' : α → ℝ) x * B0 x * C0 x + A0 x * b' x * C0 x +
        A0 x * B0 x * c' x) μ := iPQ.add iR
    rw [e1, integral_sub iL iPQR, integral_const_mul, integral_sub iX iY, integral_add iPQ iR,
      integral_add iP iQ]
  have j2 : Integrable (fun x => (ea : α → ℝ) x * B x * C x + (a' : α → ℝ) x * dB x * C x) μ := i1.add i2
  have j3 : Integrable (fun x => (ea : α → ℝ) x * B x * C x + (a' : α → ℝ) x * dB x * C x +
      a' x * B0 x * dC x) μ := j2.add i3
  have j4 : Integrable (fun x => (ea : α → ℝ) x * B x * C x + (a' : α → ℝ) x * dB x * C x +
      a' x * B0 x * dC x + A0 x * eb x * C x) μ := j3.add i4
  have j5 : Integrable (fun x => (ea : α → ℝ) x * B x * C x + (a' : α → ℝ) x * dB x * C x +
      a' x * B0 x * dC x + A0 x * eb x * C x + A0 x * b' x * dC x) μ := j4.add i5
  rw [← hsum, integral_add j5 i6, integral_add j4 i5, integral_add j3 i4, integral_add j2 i3,
    integral_add i1 i2]
  have b1 := int3_le ea B C hB
  have b2 := int3_le_right a' dB C hC
  have b3 := int3_le a' B0 dC hB0
  have b4 := int3_le_left A0 eb C hA0
  have b5 := int3_le_left A0 b' dC hA0
  have b6 := int3_le_left A0 B0 ec hA0
  have := abs_add_le (∫ x, (ea : α → ℝ) x * B x * C x ∂μ + ∫ x, (a' : α → ℝ) x * dB x * C x ∂μ +
    ∫ x, (a' : α → ℝ) x * B0 x * dC x ∂μ + ∫ x, (A0 : α → ℝ) x * eb x * C x ∂μ +
    ∫ x, (A0 : α → ℝ) x * b' x * dC x ∂μ) (∫ x, (A0 : α → ℝ) x * B0 x * ec x ∂μ)
  have := abs_add_le (∫ x, (ea : α → ℝ) x * B x * C x ∂μ + ∫ x, (a' : α → ℝ) x * dB x * C x ∂μ +
    ∫ x, (a' : α → ℝ) x * B0 x * dC x ∂μ + ∫ x, (A0 : α → ℝ) x * eb x * C x ∂μ)
    (∫ x, (A0 : α → ℝ) x * b' x * dC x ∂μ)
  have := abs_add_le (∫ x, (ea : α → ℝ) x * B x * C x ∂μ + ∫ x, (a' : α → ℝ) x * dB x * C x ∂μ +
    ∫ x, (a' : α → ℝ) x * B0 x * dC x ∂μ) (∫ x, (A0 : α → ℝ) x * eb x * C x ∂μ)
  have := abs_add_le (∫ x, (ea : α → ℝ) x * B x * C x ∂μ + ∫ x, (a' : α → ℝ) x * dB x * C x ∂μ)
    (∫ x, (a' : α → ℝ) x * B0 x * dC x ∂μ)
  have := abs_add_le (∫ x, (ea : α → ℝ) x * B x * C x ∂μ) (∫ x, (a' : α → ℝ) x * dB x * C x ∂μ)
  nlinarith [b1, b2, b3, b4, b5, b6]

/-- the three-term estimate of the increment of `Λ` -/
lemma tri_diff_bound (A B C A0 B0 C0 : Lp ℝ 2 μ) (M : ℝ)
    (hB : ∀ᵐ x ∂μ, |(B : α → ℝ) x| ≤ M)
    (hA0 : ∀ᵐ x ∂μ, |(A0 : α → ℝ) x| ≤ M) (hB0 : ∀ᵐ x ∂μ, |(B0 : α → ℝ) x| ≤ M) :
    |∫ x, (A : α → ℝ) x * B x * C x ∂μ - ∫ x, (A0 : α → ℝ) x * B0 x * C0 x ∂μ| ≤
      M * (‖A - A0‖ * ‖C‖ + ‖B - B0‖ * ‖C‖ + ‖B0‖ * ‖C - C0‖) := by
  set dA : Lp ℝ 2 μ := A - A0 with hdA
  set dB : Lp ℝ 2 μ := B - B0 with hdB
  set dC : Lp ℝ 2 μ := C - C0 with hdC
  have cdA : (dA : α → ℝ) =ᵐ[μ] _ := Lp.coeFn_sub A A0
  have cdB : (dB : α → ℝ) =ᵐ[μ] _ := Lp.coeFn_sub B B0
  have cdC : (dC : α → ℝ) =ᵐ[μ] _ := Lp.coeFn_sub C C0
  have i1 := int3_integrable dA B C hB
  have i2 := int3_integrable_left A0 dB C hA0
  have i3 := int3_integrable_left A0 B0 dC hA0
  have iX := int3_integrable A B C hB
  have iY := int3_integrable A0 B0 C0 hB0
  have j2 : Integrable (fun x => (dA : α → ℝ) x * B x * C x + (A0 : α → ℝ) x * dB x * C x) μ := i1.add i2
  have hsum : ∫ x, ((dA : α → ℝ) x * B x * C x + (A0 : α → ℝ) x * dB x * C x +
      A0 x * B0 x * dC x) ∂μ =
      ∫ x, (A : α → ℝ) x * B x * C x ∂μ - ∫ x, (A0 : α → ℝ) x * B0 x * C0 x ∂μ := by
    have e1 : ∫ x, ((dA : α → ℝ) x * B x * C x + (A0 : α → ℝ) x * dB x * C x +
        A0 x * B0 x * dC x) ∂μ = ∫ x, ((A : α → ℝ) x * B x * C x - A0 x * B0 x * C0 x) ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [cdA, cdB, cdC] with x h1 h2 h3
      simp only [h1, h2, h3, Pi.sub_apply]
      ring
    have iXY : Integrable (fun x => (A : α → ℝ) x * B x * C x - A0 x * B0 x * C0 x) μ := iX.sub iY
    rw [e1]
    exact integral_sub iX iY
  rw [← hsum, integral_add j2 i3, integral_add i1 i2]
  have b1 := int3_le dA B C hB
  have b2 := int3_le_left A0 dB C hA0
  have b3 := int3_le_left A0 B0 dC hA0
  have := abs_add_le (∫ x, (dA : α → ℝ) x * B x * C x ∂μ + ∫ x, (A0 : α → ℝ) x * dB x * C x ∂μ)
    (∫ x, (A0 : α → ℝ) x * B0 x * dC x ∂μ)
  have := abs_add_le (∫ x, (dA : α → ℝ) x * B x * C x ∂μ) (∫ x, (A0 : α → ℝ) x * dB x * C x ∂μ)
  nlinarith [b1, b2, b3]

/-- continuity of `r ↦ ∫ a_r b_r c_r` along continuous `L²`-curves bounded in `L^∞` -/
theorem tri_continuous {a b c : ℝ → Lp ℝ 2 μ} (ha : Continuous a) (hb : Continuous b)
    (hc : Continuous c) {M : ℝ} (hMa : ∀ r, ∀ᵐ x ∂μ, |(a r : α → ℝ) x| ≤ M)
    (hMb : ∀ r, ∀ᵐ x ∂μ, |(b r : α → ℝ) x| ≤ M) :
    Continuous (fun r => ∫ x, (a r : α → ℝ) x * (b r : α → ℝ) x * (c r : α → ℝ) x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro s
  have h1 : Tendsto (fun r => ‖a r - a s‖) (𝓝 s) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (ha.continuousAt (x := s))
  have h2 : Tendsto (fun r => ‖b r - b s‖) (𝓝 s) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hb.continuousAt (x := s))
  have h3 : Tendsto (fun r => ‖c r - c s‖) (𝓝 s) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 (hc.continuousAt (x := s))
  have h4 : Tendsto (fun r => ‖c r‖) (𝓝 s) (𝓝 ‖c s‖) := (hc.continuousAt (x := s)).norm
  have hlim : Tendsto (fun r => M * (‖a r - a s‖ * ‖c r‖ + ‖b r - b s‖ * ‖c r‖ +
      ‖b s‖ * ‖c r - c s‖)) (𝓝 s) (𝓝 0) := by
    have := ((h1.mul h4).add (h2.mul h4)).add (tendsto_const_nhds (x := ‖b s‖) |>.mul h3)
    simpa using this.const_mul M
  have := squeeze_zero_norm (fun r => by
    rw [Real.norm_eq_abs]
    exact tri_diff_bound (a r) (b r) (c r) (a s) (b s) (c s) M (hMb r) (hMa s) (hMb s)) hlim
  rw [ContinuousAt, tendsto_sub_nhds_zero_iff.symm]
  exact this

/-- **Product rule** for `r ↦ ∫ a_r b_r c_r` along `L²`-differentiable curves bounded in `L^∞`. -/
theorem hasDerivAt_int3 {a b c : ℝ → Lp ℝ 2 μ} {a' b' c' : Lp ℝ 2 μ} {s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) (hc : HasDerivAt c c' s) {M : ℝ}
    (hMa : ∀ r, ∀ᵐ x ∂μ, |(a r : α → ℝ) x| ≤ M) (hMb : ∀ r, ∀ᵐ x ∂μ, |(b r : α → ℝ) x| ≤ M)
    (hMc : ∀ r, ∀ᵐ x ∂μ, |(c r : α → ℝ) x| ≤ M) :
    HasDerivAt (fun r => ∫ x, (a r : α → ℝ) x * (b r : α → ℝ) x * (c r : α → ℝ) x ∂μ)
      ((∫ x, (a' : α → ℝ) x * (b s : α → ℝ) x * (c s : α → ℝ) x ∂μ) +
        (∫ x, (a s : α → ℝ) x * (b' : α → ℝ) x * (c s : α → ℝ) x ∂μ) +
        ∫ x, (a s : α → ℝ) x * (b s : α → ℝ) x * (c' : α → ℝ) x ∂μ) s := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hs : Tendsto (fun t : ℝ => s + t) (𝓝[≠] 0) (𝓝 s) := by
    have : Tendsto (fun t : ℝ => s + t) (𝓝 0) (𝓝 (s + 0)) :=
      (continuous_const.add continuous_id).tendsto 0
    rw [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have sa := hasDerivAt_iff_tendsto_slope_zero.1 ha
  have sb := hasDerivAt_iff_tendsto_slope_zero.1 hb
  have sc := hasDerivAt_iff_tendsto_slope_zero.1 hc
  have ea : Tendsto (fun t : ℝ => ‖t⁻¹ • (a (s + t) - a s) - a'‖) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 sa
  have eb : Tendsto (fun t : ℝ => ‖t⁻¹ • (b (s + t) - b s) - b'‖) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 sb
  have ec : Tendsto (fun t : ℝ => ‖t⁻¹ • (c (s + t) - c s) - c'‖) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 sc
  have db : Tendsto (fun t : ℝ => ‖b (s + t) - b s‖) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((hb.continuousAt).tendsto.comp hs)
  have dc : Tendsto (fun t : ℝ => ‖c (s + t) - c s‖) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ((hc.continuousAt).tendsto.comp hs)
  have nc : Tendsto (fun t : ℝ => ‖c (s + t)‖) (𝓝[≠] 0) (𝓝 ‖c s‖) :=
    (((hc.continuousAt).tendsto.comp hs).norm)
  have hlim : Tendsto (fun t : ℝ => M * (‖t⁻¹ • (a (s + t) - a s) - a'‖ * ‖c (s + t)‖ +
      ‖a'‖ * ‖b (s + t) - b s‖ + ‖a'‖ * ‖c (s + t) - c s‖ +
      ‖t⁻¹ • (b (s + t) - b s) - b'‖ * ‖c (s + t)‖ + ‖b'‖ * ‖c (s + t) - c s‖ +
      ‖b s‖ * ‖t⁻¹ • (c (s + t) - c s) - c'‖)) (𝓝[≠] 0) (𝓝 0) := by
    have := ((((((ea.mul nc).add (tendsto_const_nhds (x := ‖a'‖) |>.mul db)).add
      (tendsto_const_nhds (x := ‖a'‖) |>.mul dc)).add (eb.mul nc)).add
      (tendsto_const_nhds (x := ‖b'‖) |>.mul dc)).add (tendsto_const_nhds (x := ‖b s‖) |>.mul ec))
    simpa using this.const_mul M
  have := squeeze_zero_norm (fun t => by
    rw [Real.norm_eq_abs]
    have := tri_slope_bound (a (s + t)) (b (s + t)) (c (s + t)) (a s) (b s) (c s) a' b' c' t M
      (hMb _) (hMc _) (hMa s) (hMb s)
    simpa [smul_eq_mul] using this) hlim
  exact tendsto_sub_nhds_zero_iff.1 (by simpa [smul_eq_mul] using this)

end MarkovTriple.Stochastic.R31U
