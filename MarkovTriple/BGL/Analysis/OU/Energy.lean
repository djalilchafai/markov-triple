import MarkovTriple.BGL.Analysis.OU.Ergodic

/-! # OU (Part 10): energy estimate, `f, Lf ∈ L² ⇒ f' ∈ L²`, and `ibp_AA` -/

open MeasureTheory Filter Topology ProbabilityTheory Polynomial
open scoped ENNReal NNReal Real InnerProductSpace

namespace MarkovTriple.Sanity.OU

/-- the cutoff radii `c_k = 1/(k+1)` -/
noncomputable def cc (k : ℕ) : ℝ := 1 / ((k : ℝ) + 1)

lemma cc_pos (k : ℕ) : 0 < cc k := by unfold cc; positivity
lemma cc_le_one (k : ℕ) : cc k ≤ 1 := by
  unfold cc; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
lemma one_div_cc (k : ℕ) : 1 / cc k = (k : ℝ) + 1 := by simp [cc]

lemma cut_tendsto (x : ℝ) : Tendsto (fun k => cut (cc k) x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  symm
  refine cut_one (cc_pos k) ?_
  rw [one_div_cc]
  have : (N : ℝ) ≤ k := by exact_mod_cast hk
  linarith

lemma dcut_tendsto (x : ℝ) : Tendsto (fun k => deriv (cut (cc k)) x) atTop (𝓝 0) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop N] with k hk
  symm
  refine dcut_zero (cc_pos k) ?_
  rw [one_div_cc]
  have : (N : ℝ) ≤ k := by exact_mod_cast hk
  linarith

lemma cc_tendsto : Tendsto cc atTop (𝓝 0) := by
  have : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact this

lemma cut_sq_mem (k : ℕ) {h : ℝ → ℝ} (hh : Sm h) : (fun x => cut (cc k) x ^ 2 * h x) ∈ A₀ :=
  ⟨((cut_sm _).pow 2).mul hh, by
    have h1 : HasCompactSupport (fun x => cut (cc k) x * (cut (cc k) x * h x)) :=
      (cut_cs (cc_pos k)).mul_right (f' := fun x => cut (cc k) x * h x)
    have e : (fun x => cut (cc k) x ^ 2 * h x) = fun x => cut (cc k) x * (cut (cc k) x * h x) := by
      funext x; ring
    rw [e]; exact h1⟩

lemma cut_mem (k : ℕ) {h : ℝ → ℝ} (hh : Sm h) : (fun x => cut (cc k) x * h x) ∈ A₀ :=
  ⟨(cut_sm _).mul hh, (cut_cs (cc_pos k)).mul_right⟩

lemma integrable_cut_mul {F : ℝ → ℝ} (hF : Continuous F) (k : ℕ) :
    Integrable (fun x => cut (cc k) x * F x) γ :=
  ((cut_sm _).continuous.mul hF).integrable_of_hasCompactSupport ((cut_cs (cc_pos k)).mul_right)

lemma hasDerivAt_cut_sq_mul {h : ℝ → ℝ} (hh : Sm h) (k : ℕ) (x : ℝ) :
    HasDerivAt (fun x => cut (cc k) x ^ 2 * h x)
      (2 * cut (cc k) x * deriv (cut (cc k)) x * h x + cut (cc k) x ^ 2 * deriv h x) x := by
  have := ((hasDerivAt_cut (cc k) x).pow 2).mul (hh.hasDerivAt x)
  rw [deriv_cut]
  convert this using 1
  simp

/-- the energy identity with cutoff (valid for every smooth `h`) -/
lemma energy_identity {h : ℝ → ℝ} (hh : Sm h) (k : ℕ) :
    ∫ x, cut (cc k) x ^ 2 * deriv h x ^ 2 ∂γ =
      ∫ x, (-(cut (cc k) x ^ 2 * h x * Lo h x) -
        2 * (cut (cc k) x * deriv (cut (cc k)) x * h x * deriv h x)) ∂γ := by
  have hib := ibp_cs_left hh (cut_sq_mem k hh)
  have hg : ∀ x, deriv (fun x => cut (cc k) x ^ 2 * h x) x =
      2 * cut (cc k) x * deriv (cut (cc k)) x * h x + cut (cc k) x ^ 2 * deriv h x :=
    fun x => (hasDerivAt_cut_sq_mul hh k x).deriv
  simp_rw [hg] at hib
  have i1 : Integrable (fun x => cut (cc k) x ^ 2 * deriv h x ^ 2) γ := by
    have := integrable_cut_mul (F := fun x => cut (cc k) x * deriv h x ^ 2)
      ((cut_sm _).continuous.mul (hh.deriv'.continuous.pow 2)) k
    refine this.congr (ae_of_all _ fun x => ?_); simp only; ring
  have i2 : Integrable (fun x => 2 * (cut (cc k) x * deriv (cut (cc k)) x * h x * deriv h x)) γ := by
    have := (integrable_cut_mul (F := fun x => deriv (cut (cc k)) x * h x * deriv h x)
      (((cut_sm _).deriv'.continuous.mul hh.continuous).mul hh.deriv'.continuous) k).const_mul 2
    refine this.congr (ae_of_all _ fun x => ?_); simp only; ring
  have i3 : Integrable (fun x => cut (cc k) x ^ 2 * h x * Lo h x) γ := by
    have := integrable_cut_mul (F := fun x => cut (cc k) x * h x * Lo h x)
      (((cut_sm _).continuous.mul hh.continuous).mul (sm_Lo hh).continuous) k
    refine this.congr (ae_of_all _ fun x => ?_); simp only; ring
  have e1 : (fun x => (2 * cut (cc k) x * deriv (cut (cc k)) x * h x + cut (cc k) x ^ 2 * deriv h x)
      * deriv h x) = fun x => 2 * (cut (cc k) x * deriv (cut (cc k)) x * h x * deriv h x)
        + cut (cc k) x ^ 2 * deriv h x ^ 2 := by funext x; ring
  rw [e1, integral_add i2 i1] at hib
  have e2 : (fun x => cut (cc k) x ^ 2 * h x * Lo h x) = fun x => cut (cc k) x ^ 2 * h x * Lo h x := rfl
  rw [integral_sub (by simpa using i3.neg) i2, integral_neg]
  have e3 : ∫ x, (cut (cc k) x ^ 2 * h x) * Lo h x ∂γ = ∫ x, cut (cc k) x ^ 2 * h x * Lo h x ∂γ := rfl
  rw [e3] at hib
  linarith

lemma energy_le {h : ℝ → ℝ} (hh : Sm h) (h0 : MemLp h 2 γ) (h2 : MemLp (Lo h) 2 γ) {K : ℝ}
    (_hK0 : 0 ≤ K) (hK : ∀ x, |deriv ψ0 x| ≤ K ∧ |deriv (deriv ψ0) x| ≤ K) (k : ℕ) :
    ∫ x, cut (cc k) x ^ 2 * deriv h x ^ 2 ∂γ ≤
      (1 + 4 * K ^ 2) * ∫ x, h x ^ 2 ∂γ + ∫ x, Lo h x ^ 2 ∂γ := by
  have i1 : Integrable (fun x => cut (cc k) x ^ 2 * deriv h x ^ 2) γ := by
    have := integrable_cut_mul (F := fun x => cut (cc k) x * deriv h x ^ 2)
      ((cut_sm _).continuous.mul (hh.deriv'.continuous.pow 2)) k
    refine this.congr (ae_of_all _ fun x => ?_); simp only; ring
  have i2 : Integrable (fun x => 2 * (cut (cc k) x * deriv (cut (cc k)) x * h x * deriv h x)) γ := by
    have := (integrable_cut_mul (F := fun x => deriv (cut (cc k)) x * h x * deriv h x)
      (((cut_sm _).deriv'.continuous.mul hh.continuous).mul hh.deriv'.continuous) k).const_mul 2
    refine this.congr (ae_of_all _ fun x => ?_); simp only; ring
  have i3 : Integrable (fun x => cut (cc k) x ^ 2 * h x * Lo h x) γ := by
    have := integrable_cut_mul (F := fun x => cut (cc k) x * h x * Lo h x)
      (((cut_sm _).continuous.mul hh.continuous).mul (sm_Lo hh).continuous) k
    refine this.congr (ae_of_all _ fun x => ?_); simp only; ring
  have j0 : Integrable (fun x => h x ^ 2) γ := h0.integrable_sq
  have j2 : Integrable (fun x => Lo h x ^ 2) γ := h2.integrable_sq
  have hid := energy_identity hh k
  have hF : Integrable (fun x => -(cut (cc k) x ^ 2 * h x * Lo h x) -
      2 * (cut (cc k) x * deriv (cut (cc k)) x * h x * deriv h x)) γ := i3.neg.sub i2
  have hG : Integrable (fun x => (h x ^ 2 + Lo h x ^ 2) / 2 +
      (1 / 2 * (cut (cc k) x ^ 2 * deriv h x ^ 2) + 2 * K ^ 2 * h x ^ 2)) γ :=
    (j0.add j2).div_const 2 |>.add ((i1.const_mul (1 / 2)).add (j0.const_mul (2 * K ^ 2)))
  have hle := integral_mono hF hG (fun x => by
    simp only
    have hc : |deriv (cut (cc k)) x| ≤ K := dcut_bound hK (cc_pos k) (cc_le_one k) x
    have hs0 : 0 ≤ cut (cc k) x ^ 2 := sq_nonneg _
    have hs1 : cut (cc k) x ^ 2 ≤ 1 := by
      have := cut_nonneg (cc k) x; have := cut_le_one (cc k) x; nlinarith
    -- bound 1
    have b1 : -(cut (cc k) x ^ 2 * h x * Lo h x) ≤ (h x ^ 2 + Lo h x ^ 2) / 2 := by
      nlinarith [sq_nonneg (h x + Lo h x), sq_nonneg (h x - Lo h x), mul_nonneg hs0 (sq_nonneg (h x + Lo h x)),
        mul_nonneg (sub_nonneg.2 hs1) (sq_nonneg (h x - Lo h x)),
        mul_nonneg hs0 (sq_nonneg (h x - Lo h x)), mul_nonneg (sub_nonneg.2 hs1) (sq_nonneg (h x + Lo h x))]
    -- bound 2
    have b2 : -(2 * (cut (cc k) x * deriv (cut (cc k)) x * h x * deriv h x)) ≤
        1 / 2 * (cut (cc k) x ^ 2 * deriv h x ^ 2) + 2 * K ^ 2 * h x ^ 2 := by
      have hv : (deriv (cut (cc k)) x * h x) ^ 2 ≤ K ^ 2 * h x ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (by
          have := sq_le_sq' (abs_le.1 hc).1 (abs_le.1 hc).2; exact this) (sq_nonneg _)
      nlinarith [sq_nonneg (cut (cc k) x * deriv h x + 2 * (deriv (cut (cc k)) x * h x))]
    linarith)
  have hA : Integrable (fun x => (h x ^ 2 + Lo h x ^ 2) / 2) γ := (j0.add j2).div_const 2
  have hBC : Integrable (fun x => 1 / 2 * (cut (cc k) x ^ 2 * deriv h x ^ 2) + 2 * K ^ 2 * h x ^ 2) γ :=
    (i1.const_mul (1 / 2)).add (j0.const_mul (2 * K ^ 2))
  rw [integral_add hA hBC, integral_add (i1.const_mul (1 / 2)) (j0.const_mul (2 * K ^ 2)),
    integral_const_mul, integral_const_mul, integral_div, integral_add j0 j2] at hle
  linarith

lemma enorm_rpow_two (a : ℝ) : ‖a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (a ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg a) (by norm_num)]
  congr 1
  rw [Real.rpow_two, sq_abs]

lemma enorm_sq' (a : ℝ) : ‖a ^ 2‖ₑ = ENNReal.ofReal (a ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg a)]

/-- **`f, Lf ∈ L² ⇒ f' ∈ L²`** (for smooth `f`). -/
theorem deriv_memLp {h : ℝ → ℝ} (hh : Sm h) (h0 : MemLp h 2 γ) (h2 : MemLp (Lo h) 2 γ) :
    MemLp (deriv h) 2 γ := by
  obtain ⟨K, hK0, hK⟩ := exists_K
  set M : ℝ := (1 + 4 * K ^ 2) * ∫ x, h x ^ 2 ∂γ + ∫ x, Lo h x ^ 2 ∂γ with hM
  have hF : ∀ k, ∫⁻ x, ‖cut (cc k) x * deriv h x‖ₑ ^ (2 : ℝ) ∂γ ≤ ENNReal.ofReal M := by
    intro k
    have hi : Integrable (fun x => cut (cc k) x ^ 2 * deriv h x ^ 2) γ := by
      have := integrable_cut_mul (F := fun x => cut (cc k) x * deriv h x ^ 2)
        ((cut_sm _).continuous.mul (hh.deriv'.continuous.pow 2)) k
      refine this.congr (ae_of_all _ fun x => ?_); simp only; ring
    have e : ∀ x, ‖cut (cc k) x * deriv h x‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (cut (cc k) x ^ 2 * deriv h x ^ 2) := by
      intro x; rw [enorm_rpow_two]; congr 1; ring
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
    exact ENNReal.ofReal_le_ofReal (energy_le hh h0 h2 hK0 hK k)
  have hmeas : ∀ k, Measurable (fun x => ‖cut (cc k) x * deriv h x‖ₑ ^ (2 : ℝ)) := fun k =>
    (((cut_sm _).continuous.mul hh.deriv'.continuous).measurable.enorm).pow_const _
  have hfat : ∫⁻ x, Filter.liminf (fun k => ‖cut (cc k) x * deriv h x‖ₑ ^ (2 : ℝ)) atTop ∂γ ≤
      Filter.liminf (fun k => ∫⁻ x, ‖cut (cc k) x * deriv h x‖ₑ ^ (2 : ℝ) ∂γ) atTop :=
    lintegral_liminf_le hmeas
  have hlim : ∀ x, Filter.liminf (fun k => ‖cut (cc k) x * deriv h x‖ₑ ^ (2 : ℝ)) atTop =
      ‖deriv h x‖ₑ ^ (2 : ℝ) := by
    intro x
    have : Tendsto (fun k => ‖cut (cc k) x * deriv h x‖ₑ ^ (2 : ℝ)) atTop (𝓝 (‖deriv h x‖ₑ ^ (2 : ℝ))) := by
      have h1 : Tendsto (fun k => cut (cc k) x * deriv h x) atTop (𝓝 (1 * deriv h x)) :=
        (cut_tendsto x).mul_const _
      simp only [one_mul] at h1
      exact ((ENNReal.continuous_rpow_const (y := 2)).tendsto _).comp
        ((continuous_enorm.tendsto _).comp h1)
    exact this.liminf_eq
  simp_rw [hlim] at hfat
  have hfin : ∫⁻ x, ‖deriv h x‖ₑ ^ (2 : ℝ) ∂γ ≤ ENNReal.ofReal M := by
    refine hfat.trans ?_
    exact Filter.liminf_le_of_frequently_le' (f := (atTop : Filter ℕ)) (Frequently.of_forall hF)
  rw [memLp_two_iff_integrable_sq hh.deriv'.continuous.aestronglyMeasurable]
  refine ⟨(hh.deriv'.continuous.pow 2).aestronglyMeasurable, ?_⟩
  simp only [HasFiniteIntegral, enorm_sq']
  have : ∀ x, ENNReal.ofReal (deriv h x ^ 2) = ‖deriv h x‖ₑ ^ (2 : ℝ) := fun x => (enorm_rpow_two _).symm
  simp_rw [this]
  exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top

lemma ae_bound_of_memLp_top {k : ℝ → ℝ} (hk : MemLp k ∞ γ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ᵐ x ∂γ, |k x| ≤ B := by
  have h : eLpNormEssSup k γ < ⊤ := by
    have := hk.eLpNorm_lt_top
    rwa [eLpNorm_exponent_top hk.aestronglyMeasurable] at this
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.1 h
  refine ⟨C, C.2, ?_⟩
  filter_upwards [Filter.eventually_map.1 hC] with x hx
  have := NNReal.coe_le_coe.2 hx
  simpa using this

/-- **`ibp_AA` for OU**. -/
theorem ou_ibp_AA {f k : ℝ → ℝ} (hf : Sm f) (hk : Sm k) (hf0 : MemLp f 2 γ)
    (hf2 : MemLp (Lo f) 2 γ) (hk0 : MemLp k 2 γ) (hk2 : MemLp (Lo k) 2 γ) (hkb : MemLp k ∞ γ) :
    Integrable (Go f k) γ ∧ ∫ x, k x * Lo f x ∂γ = -∫ x, Go f k x ∂γ := by
  have hf1 := deriv_memLp hf hf0 hf2
  have hk1 := deriv_memLp hk hk0 hk2
  have hΓ : Integrable (fun x => deriv f x * deriv k x) γ := hf1.integrable_mul hk1
  refine ⟨hΓ, ?_⟩
  obtain ⟨K, hK0, hK⟩ := exists_K
  obtain ⟨B, hB0, hB⟩ := ae_bound_of_memLp_top hkb
  have hkLf : Integrable (fun x => k x * Lo f x) γ := hk0.integrable_mul hf2
  have hk'f' : Integrable (fun x => deriv k x * deriv f x) γ := hk1.integrable_mul hf1
  have hf'i : Integrable (fun x => deriv f x) γ := hf1.integrable one_le_two
  -- identity for each cutoff
  have hid : ∀ j, ∫ x, cut (cc j) x * k x * Lo f x ∂γ =
      -(∫ x, deriv (cut (cc j)) x * k x * deriv f x ∂γ) -
        ∫ x, cut (cc j) x * (deriv k x * deriv f x) ∂γ := by
    intro j
    have h := ibp_cs_left hf (cut_mem j hk)
    have hd : ∀ x, deriv (fun x => cut (cc j) x * k x) x =
        deriv (cut (cc j)) x * k x + cut (cc j) x * deriv k x := fun x =>
      ((hasDerivAt_cut (cc j) x).mul (hk.hasDerivAt x)).deriv.trans (by rw [deriv_cut])
    simp_rw [hd] at h
    have i1 : Integrable (fun x => deriv (cut (cc j)) x * k x * deriv f x) γ :=
      ((((cut_sm _).deriv'.continuous.mul hk.continuous).mul hf.deriv'.continuous).integrable_of_hasCompactSupport
        (((cut_cs (cc_pos j)).deriv).mul_right.mul_right))
    have i2 : Integrable (fun x => cut (cc j) x * (deriv k x * deriv f x)) γ :=
      integrable_cut_mul (F := fun x => deriv k x * deriv f x)
        (hk.deriv'.continuous.mul hf.deriv'.continuous) j
    have e : (fun x => (deriv (cut (cc j)) x * k x + cut (cc j) x * deriv k x) * deriv f x) =
        fun x => deriv (cut (cc j)) x * k x * deriv f x + cut (cc j) x * (deriv k x * deriv f x) := by
      funext x; ring
    rw [e, integral_add i1 i2] at h
    rw [h]; ring
  -- limits
  have tA : Tendsto (fun j => ∫ x, cut (cc j) x * k x * Lo f x ∂γ) atTop (𝓝 (∫ x, k x * Lo f x ∂γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |k x * Lo f x|)
      (fun j => ?_) hkLf.abs (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · exact (((cut_sm _).continuous.mul hk.continuous).mul (sm_Lo hf).continuous).aestronglyMeasurable
    · rw [Real.norm_eq_abs, mul_assoc, abs_mul, abs_of_nonneg (cut_nonneg _ x)]
      calc cut (cc j) x * |k x * Lo f x| ≤ 1 * |k x * Lo f x| :=
            mul_le_mul_of_nonneg_right (cut_le_one _ x) (abs_nonneg _)
        _ = _ := one_mul _
    · have := ((cut_tendsto x).mul_const (k x)).mul_const (Lo f x)
      simpa [mul_assoc] using this
  have tC : Tendsto (fun j => ∫ x, cut (cc j) x * (deriv k x * deriv f x) ∂γ) atTop
      (𝓝 (∫ x, deriv k x * deriv f x ∂γ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |deriv k x * deriv f x|)
      (fun j => ?_) hk'f'.abs (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · exact ((cut_sm _).continuous.mul (hk.deriv'.continuous.mul hf.deriv'.continuous)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (cut_nonneg _ x)]
      calc cut (cc j) x * |deriv k x * deriv f x| ≤ 1 * |deriv k x * deriv f x| :=
            mul_le_mul_of_nonneg_right (cut_le_one _ x) (abs_nonneg _)
        _ = _ := one_mul _
    · have := (cut_tendsto x).mul_const (deriv k x * deriv f x)
      simpa using this
  have tB : Tendsto (fun j => ∫ x, deriv (cut (cc j)) x * k x * deriv f x ∂γ) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence (μ := γ)
      (F := fun j x => deriv (cut (cc j)) x * k x * deriv f x) (f := fun _ => 0)
      (fun x => K * B * |deriv f x|)
      (fun j => (((cut_sm _).deriv'.continuous.mul hk.continuous).mul hf.deriv'.continuous).aestronglyMeasurable)
      (hf'i.abs.const_mul (K * B))
      (fun j => by
        filter_upwards [hB] with x hx
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 := dcut_bound hK (cc_pos j) (cc_le_one j) x
        calc |deriv (cut (cc j)) x| * |k x| * |deriv f x| ≤ K * B * |deriv f x| :=
              mul_le_mul_of_nonneg_right (mul_le_mul h1 hx (abs_nonneg _) hK0) (abs_nonneg _))
      (ae_of_all _ fun x => by
        have := ((dcut_tendsto x).mul_const (k x)).mul_const (deriv f x)
        simpa using this)
    simpa using this
  have hlim : Tendsto (fun j => ∫ x, cut (cc j) x * k x * Lo f x ∂γ) atTop
      (𝓝 (-(0 : ℝ) - ∫ x, deriv k x * deriv f x ∂γ)) := by
    refine (tB.neg.sub tC).congr fun j => ?_
    rw [hid j]
  have := tendsto_nhds_unique tA hlim
  rw [this]
  simp only [Go]
  have e : ∫ x, deriv k x * deriv f x ∂γ = ∫ x, deriv f x * deriv k x ∂γ :=
    integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
  rw [e]; ring

end MarkovTriple.Sanity.OU
