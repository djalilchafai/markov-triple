import Mathlib

/-!
# Jensen / Cauchy-Schwarz inequality for positive sub-Markov operators on `L²(μ)`

Generic (no triple, no kernel).  `P : L²(μ) →L[ℝ] L²(μ)` is *positive* (`u ≥ 0 ⇒ P u ≥ 0` a.e.) and
*sub-Markov* (`u ≤ 1 ⇒ P u ≤ 1` a.e., for `u ∈ L²`).  Then for `0 ≤ w ∈ L²(μ)` with `w² ∈ L²(μ)` (class `W`):
`(P w)² ≤ P(W)` a.e.  This is the "Jensen's inequality for the sub-Markov `P_t`" invoked by the book
(BGL p. 163, deduction of Cor. 3.3.19 from Thm 3.3.18).  Proof: for `u_n = min(1, n w) ∈ L²`,
`0 ≤ P((w - q u_n)²) = P(w²) - 2q P(w u_n) + q² P(u_n²) ≤ P(w²) - 2 q P(w u_n) + q²` for every rational `q`,
whence `(P(w u_n))² ≤ P(w²)`; then `w u_n → w` in `L²` and a subsequence converges a.e.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- real-variable step: `2 q a - q² ≤ b` for all rational `q` forces `a² ≤ b`. -/
lemma sq_le_of_forall_rat {a b : ℝ} (h : ∀ q : ℚ, 2 * q * a - q ^ 2 ≤ b) : a ^ 2 ≤ b := by
  by_contra hlt0
  have hlt := not_le.mp hlt0
  set δ := min 1 (a ^ 2 - b) with hδ
  have hδpos : 0 < δ := lt_min one_pos (by linarith)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδ2 : δ ≤ a ^ 2 - b := min_le_right _ _
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show a < a + δ by linarith)
  have h0 := h q
  have h1 : (q - a) ^ 2 < δ := by nlinarith
  nlinarith

/-- the truncation `min 1 (n w)`. -/
noncomputable def jTrunc (w : E → ℝ) (n : ℕ) : E → ℝ := fun x => min 1 ((n : ℝ) * w x)

lemma jTrunc_aesm {w : E → ℝ} (hw : AEStronglyMeasurable w μ) (n : ℕ) :
    AEStronglyMeasurable (jTrunc w n) μ :=
  (continuous_const.min continuous_id).comp_aestronglyMeasurable (hw.const_mul (n : ℝ))

lemma jTrunc_nonneg {w : E → ℝ} (hw : 0 ≤ᵐ[μ] w) (n : ℕ) : 0 ≤ᵐ[μ] jTrunc w n := by
  filter_upwards [hw] with x hx
  exact le_min zero_le_one (mul_nonneg (Nat.cast_nonneg n) hx)

omit [MeasurableSpace E] in
lemma jTrunc_le_one (w : E → ℝ) (n : ℕ) (x : E) : jTrunc w n x ≤ 1 := min_le_left _ _

lemma jTrunc_memLp {w : E → ℝ} (hw : MemLp w 2 μ) (hw0 : 0 ≤ᵐ[μ] w) (n : ℕ) :
    MemLp (jTrunc w n) 2 μ := by
  refine (hw.const_mul (n : ℝ)).mono (jTrunc_aesm hw.aestronglyMeasurable n) ?_
  filter_upwards [hw0] with x hx
  have h0 : 0 ≤ (n : ℝ) * w x := mul_nonneg (Nat.cast_nonneg n) hx
  have := min_le_right 1 ((n : ℝ) * w x)
  simp only [jTrunc, Real.norm_eq_abs]
  rw [abs_of_nonneg (le_min zero_le_one h0), abs_of_nonneg h0]
  exact this

/-- **Jensen for positive sub-Markov operators** (generic `L²` statement). -/
theorem jensen_sq (P : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (hpos : ∀ u : Lp ℝ 2 μ, 0 ≤ᵐ[μ] (u : E → ℝ) → 0 ≤ᵐ[μ] (P u : E → ℝ))
    (hle : ∀ u : Lp ℝ 2 μ, (u : E → ℝ) ≤ᵐ[μ] (1 : E → ℝ) → (P u : E → ℝ) ≤ᵐ[μ] (1 : E → ℝ))
    (w W : Lp ℝ 2 μ) (hw : 0 ≤ᵐ[μ] (w : E → ℝ)) (hW : (W : E → ℝ) =ᵐ[μ] fun x => (w x) ^ 2) :
    ∀ᵐ x ∂μ, (P w x) ^ 2 ≤ P W x := by
  have hwm : MemLp (w : E → ℝ) 2 μ := Lp.memLp w
  set u : ℕ → E → ℝ := fun n => jTrunc (w : E → ℝ) n with hu
  have hu0 : ∀ n, 0 ≤ᵐ[μ] u n := fun n => jTrunc_nonneg hw n
  have hum : ∀ n, MemLp (u n) 2 μ := fun n => jTrunc_memLp hwm hw n
  -- products and squares
  have hv : ∀ n, MemLp (fun x => (w : E → ℝ) x * u n x) 2 μ := by
    intro n
    refine hwm.mono (hwm.aestronglyMeasurable.mul (hum n).aestronglyMeasurable) ?_
    filter_upwards [hw, hu0 n] with x h1 h2
    have h3 : u n x ≤ 1 := jTrunc_le_one _ n x
    simp only [Pi.zero_apply] at h1 h2
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg h1 h2), abs_of_nonneg h1]
    nlinarith
  have hs : ∀ n, MemLp (fun x => u n x * u n x) 2 μ := by
    intro n
    refine (hum n).mono ((hum n).aestronglyMeasurable.mul (hum n).aestronglyMeasurable) ?_
    filter_upwards [hu0 n] with x h2
    have h3 : u n x ≤ 1 := jTrunc_le_one _ n x
    simp only [Pi.zero_apply] at h2
    simp only [Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg h2 h2), abs_of_nonneg h2]
    nlinarith
  set B : ℕ → Lp ℝ 2 μ := fun n => (hv n).toLp _ with hB
  set S : ℕ → Lp ℝ 2 μ := fun n => (hs n).toLp _ with hS
  have hBc : ∀ n, (B n : E → ℝ) =ᵐ[μ] fun x => (w : E → ℝ) x * u n x := fun n => MemLp.coeFn_toLp _
  have hSc : ∀ n, (S n : E → ℝ) =ᵐ[μ] fun x => u n x * u n x := fun n => MemLp.coeFn_toLp _
  -- Cauchy-Schwarz step
  have key : ∀ n, ∀ᵐ x ∂μ, (P (B n) x) ^ 2 ≤ P W x := by
    intro n
    have hq : ∀ q : ℚ, ∀ᵐ x ∂μ, 2 * (q : ℝ) * P (B n) x - (q : ℝ) ^ 2 ≤ P W x := by
      intro q
      set Z : Lp ℝ 2 μ := W - ((2 * (q : ℝ)) • B n) + ((q : ℝ) ^ 2) • S n with hZ
      have hZ0 : 0 ≤ᵐ[μ] (Z : E → ℝ) := by
        filter_upwards [Lp.coeFn_add (W - ((2 * (q : ℝ)) • B n)) (((q : ℝ) ^ 2) • S n),
          Lp.coeFn_sub W ((2 * (q : ℝ)) • B n), Lp.coeFn_smul (2 * (q : ℝ)) (B n),
          Lp.coeFn_smul ((q : ℝ) ^ 2) (S n), hW, hBc n, hSc n] with x a1 a2 a3 a4 a5 a6 a7
        rw [hZ, a1, Pi.add_apply, a2, Pi.sub_apply, a3, a4, Pi.smul_apply, Pi.smul_apply, a5, a6, a7]
        simp only [smul_eq_mul, Pi.zero_apply]
        nlinarith [sq_nonneg ((w : E → ℝ) x - q * u n x)]
      have hPZ := hpos Z hZ0
      have hPZe : P Z = P W - (2 * (q : ℝ)) • P (B n) + ((q : ℝ) ^ 2) • P (S n) := by
        rw [hZ, map_add, map_sub, map_smul, map_smul]
      have hS1 : (S n : E → ℝ) ≤ᵐ[μ] (1 : E → ℝ) := by
        filter_upwards [hSc n, hu0 n] with x a b
        have h3 : u n x ≤ 1 := jTrunc_le_one _ n x
        simp only [Pi.zero_apply] at b
        rw [a]; simp only [Pi.one_apply]; nlinarith
      have hPS := hle (S n) hS1
      filter_upwards [hPZ, hPS, Lp.coeFn_add (P W - (2 * (q : ℝ)) • P (B n)) (((q : ℝ) ^ 2) • P (S n)),
          Lp.coeFn_sub (P W) ((2 * (q : ℝ)) • P (B n)), Lp.coeFn_smul (2 * (q : ℝ)) (P (B n)),
          Lp.coeFn_smul ((q : ℝ) ^ 2) (P (S n))] with x a1 a2 a3 a4 a5 a6
      rw [hPZe, a3, Pi.add_apply, a4, Pi.sub_apply, a5, a6, Pi.smul_apply, Pi.smul_apply] at a1
      simp only [smul_eq_mul, Pi.zero_apply] at a1
      simp only [Pi.one_apply] at a2
      nlinarith [sq_nonneg (q : ℝ)]
    have := ae_all_iff.2 hq
    filter_upwards [this] with x hx
    exact sq_le_of_forall_rat hx
  -- convergence `B n → w` in `L²`
  have hconv : Tendsto B atTop (𝓝 w) := by
    have hnorm : ∀ n, ‖B n - w‖ ^ 2 = ∫ x, ((w : E → ℝ) x * (u n x - 1)) ^ 2 ∂μ := by
      intro n
      rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (B n) w, hBc n] with x a b
      rw [a, Pi.sub_apply, b]
      simp only [RCLike.inner_apply, conj_trivial]
      ring
    have hlim : Tendsto (fun n => ∫ x, ((w : E → ℝ) x * (u n x - 1)) ^ 2 ∂μ) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => ((w : E → ℝ) x) ^ 2)
        (F := fun n x => ((w : E → ℝ) x * (u n x - 1)) ^ 2) (f := fun _ => (0 : ℝ))
        (fun n => (hwm.aestronglyMeasurable.mul
          ((hum n).aestronglyMeasurable.sub aestronglyMeasurable_const)).pow 2)
        hwm.integrable_sq
        (fun n => by
          filter_upwards [hw, hu0 n] with x h1 h2
          simp only [Pi.zero_apply] at h1 h2
          have h3 : u n x ≤ 1 := jTrunc_le_one _ n x
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
          have : (u n x - 1) ^ 2 ≤ 1 := by nlinarith
          nlinarith [sq_nonneg ((w : E → ℝ) x)])
        (by
          filter_upwards [hw] with x h1
          simp only [Pi.zero_apply] at h1
          rcases h1.eq_or_lt with h0 | hpos'
          · simp [← h0]
          · obtain ⟨N, hN⟩ := exists_nat_ge (1 / (w : E → ℝ) x)
            refine tendsto_const_nhds.congr' ?_
            filter_upwards [eventually_ge_atTop N] with n hn
            have h4 : 1 ≤ (n : ℝ) * (w : E → ℝ) x := by
              have : 1 / (w : E → ℝ) x ≤ n := hN.trans (Nat.cast_le.2 hn)
              rw [div_le_iff₀ hpos'] at this
              linarith
            have : u n x = 1 := min_eq_left h4
            simp [this])
      simpa using this
    have h2 : Tendsto (fun n => ‖B n - w‖ ^ 2) atTop (𝓝 0) := by simpa [hnorm] using hlim
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    simp only [Function.comp_def, Real.sqrt_zero] at h3
    have h4 : Tendsto (fun n => ‖B n - w‖) atTop (𝓝 0) := by
      refine h3.congr (fun n => ?_)
      exact Real.sqrt_sq (norm_nonneg _)
    exact tendsto_iff_norm_sub_tendsto_zero.2 h4
  have hPconv : Tendsto (fun n => P (B n)) atTop (𝓝 (P w)) := (P.continuous.tendsto w).comp hconv
  obtain ⟨φ, hφ, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hPconv).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, (P (B n) x) ^ 2 ≤ P W x := ae_all_iff.2 key
  filter_upwards [hall, hae] with x h1 h2
  have h3 : Tendsto (fun k => (P (B (φ k)) x) ^ 2) atTop (𝓝 ((P w x) ^ 2)) := h2.pow 2
  exact le_of_tendsto' h3 (fun k => h1 (φ k))

end MarkovTriple.BGL
