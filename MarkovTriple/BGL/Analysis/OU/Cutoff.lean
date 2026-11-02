import MarkovTriple.BGL.Analysis.OU.Basis

/-! # OU (Part 7): cutoffs and approximation in the graph norm -/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

/-! ### The basic bump -/

/-- a fixed smooth bump: `=1` on `[-1,1]`, supported in `[-2,2]`, values in `[0,1]` -/
noncomputable def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩

noncomputable def ψ0 : ℝ → ℝ := bump

lemma ψ0_sm : Sm ψ0 := bump.contDiff
lemma ψ0_cs : HasCompactSupport ψ0 := bump.hasCompactSupport
lemma ψ0_nonneg (x : ℝ) : 0 ≤ ψ0 x := bump.nonneg
lemma ψ0_le_one (x : ℝ) : ψ0 x ≤ 1 := bump.le_one
lemma ψ0_one {x : ℝ} (h : |x| ≤ 1) : ψ0 x = 1 :=
  bump.one_of_mem_closedBall (by simpa [bump] using h)
lemma ψ0_zero {x : ℝ} (h : 2 ≤ |x|) : ψ0 x = 0 :=
  bump.zero_of_le_dist (by simpa [bump] using h)

lemma ψ0_eventually_one {x : ℝ} (h : |x| < 1) : ψ0 =ᶠ[𝓝 x] fun _ => 1 := by
  have : Set.Ioo (-1 : ℝ) 1 ∈ 𝓝 x := Ioo_mem_nhds (by linarith [abs_lt.1 h]) (by linarith [abs_lt.1 h])
  filter_upwards [this] with y hy
  exact ψ0_one (abs_le.2 ⟨hy.1.le, hy.2.le⟩)

lemma ψ0_eventually_zero {x : ℝ} (h : 2 < |x|) : ψ0 =ᶠ[𝓝 x] fun _ => 0 := by
  have : {y : ℝ | 2 < |y|} ∈ 𝓝 x := (isOpen_lt continuous_const continuous_abs).mem_nhds h
  filter_upwards [this] with y hy
  exact ψ0_zero hy.le

lemma dψ0_zero_of_lt {x : ℝ} (h : |x| < 1) : deriv ψ0 x = 0 := by
  rw [(ψ0_eventually_one h).deriv_eq]; simp
lemma dψ0_zero_of_gt {x : ℝ} (h : 2 < |x|) : deriv ψ0 x = 0 := by
  rw [(ψ0_eventually_zero h).deriv_eq]; simp

lemma ddψ0_zero_of_lt {x : ℝ} (h : |x| < 1) : deriv (deriv ψ0) x = 0 := by
  have : {y : ℝ | |y| < 1} ∈ 𝓝 x := (isOpen_lt continuous_abs continuous_const).mem_nhds h
  have e : deriv ψ0 =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [this] with y hy using dψ0_zero_of_lt hy
  rw [e.deriv_eq]; simp
lemma ddψ0_zero_of_gt {x : ℝ} (h : 2 < |x|) : deriv (deriv ψ0) x = 0 := by
  have : {y : ℝ | 2 < |y|} ∈ 𝓝 x := (isOpen_lt continuous_const continuous_abs).mem_nhds h
  have e : deriv ψ0 =ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [this] with y hy using dψ0_zero_of_gt hy
  rw [e.deriv_eq]; simp

lemma exists_K : ∃ K : ℝ, 0 ≤ K ∧ ∀ x, |deriv ψ0 x| ≤ K ∧ |deriv (deriv ψ0) x| ≤ K := by
  obtain ⟨C1, h1⟩ := ψ0_sm.deriv'.continuous.bounded_above_of_compact_support ψ0_cs.deriv
  obtain ⟨C2, h2⟩ := ψ0_sm.deriv'.deriv'.continuous.bounded_above_of_compact_support ψ0_cs.deriv.deriv
  refine ⟨max |C1| |C2|, by positivity, fun x => ⟨?_, ?_⟩⟩
  · have := h1 x; simp only [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans (le_max_left _ _))
  · have := h2 x; simp only [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans (le_max_right _ _))

/-- the dilated cutoff -/
noncomputable def cut (c : ℝ) : ℝ → ℝ := fun x => ψ0 (c * x)

lemma cut_sm (c : ℝ) : Sm (cut c) := ψ0_sm.comp (contDiff_const.mul contDiff_id)

lemma hasDerivAt_cut (c x : ℝ) : HasDerivAt (cut c) (c * deriv ψ0 (c * x)) x := by
  have h := (ψ0_sm.hasDerivAt (c * x)).comp x ((hasDerivAt_id' x).const_mul c)
  exact h.congr_deriv (by ring)

lemma deriv_cut (c : ℝ) : deriv (cut c) = fun x => c * deriv ψ0 (c * x) :=
  funext fun x => (hasDerivAt_cut c x).deriv

lemma deriv_deriv_cut (c : ℝ) : deriv (deriv (cut c)) = fun x => c * (c * deriv (deriv ψ0) (c * x)) := by
  rw [deriv_cut]
  funext x
  have h := ((ψ0_sm.deriv'.hasDerivAt (c * x)).comp x ((hasDerivAt_id' x).const_mul c)).const_mul c
  exact (h.congr_deriv (by ring)).deriv

lemma cut_cs {c : ℝ} (hc : 0 < c) : HasCompactSupport (cut c) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 / c)) fun x hx => ?_
  have h1 : 2 / c < |x| := by simpa using hx
  have h3 := (div_lt_iff₀ hc).1 h1
  have h2 : 2 ≤ |c * x| := by
    rw [abs_mul, abs_of_pos hc]; linarith [mul_comm c |x|]
  exact ψ0_zero h2

lemma cut_nonneg (c x : ℝ) : 0 ≤ cut c x := ψ0_nonneg _
lemma cut_le_one (c x : ℝ) : cut c x ≤ 1 := ψ0_le_one _

/-- on `|x| ≤ 1/c` the cutoff is `1`, and all its derivatives vanish on `|x| < 1/c` -/
lemma cut_one {c x : ℝ} (hc : 0 < c) (h : |x| ≤ 1 / c) : cut c x = 1 := by
  apply ψ0_one
  rw [abs_mul, abs_of_pos hc]
  calc c * |x| ≤ c * (1 / c) := mul_le_mul_of_nonneg_left h hc.le
    _ = 1 := by field_simp

lemma dcut_zero {c x : ℝ} (hc : 0 < c) (h : |x| < 1 / c) : deriv (cut c) x = 0 := by
  rw [deriv_cut]
  have : |c * x| < 1 := by
    rw [abs_mul, abs_of_pos hc]
    calc c * |x| < c * (1 / c) := mul_lt_mul_of_pos_left h hc
      _ = 1 := by field_simp
  simp [dψ0_zero_of_lt this]

lemma ddcut_zero {c x : ℝ} (hc : 0 < c) (h : |x| < 1 / c) : deriv (deriv (cut c)) x = 0 := by
  rw [deriv_deriv_cut]
  have : |c * x| < 1 := by
    rw [abs_mul, abs_of_pos hc]
    calc c * |x| < c * (1 / c) := mul_lt_mul_of_pos_left h hc
      _ = 1 := by field_simp
  simp [ddψ0_zero_of_lt this]

lemma abs_x_dcut_le {K c : ℝ} (hK : ∀ x, |deriv ψ0 x| ≤ K) (x : ℝ) :
    |x * deriv (cut c) x| ≤ 2 * K := by
  rw [deriv_cut]
  by_cases h : 2 < |c * x|
  · simp [dψ0_zero_of_gt h]
    have := hK 0; have := abs_nonneg (deriv ψ0 0); linarith
  · push Not at h
    have e : x * (c * deriv ψ0 (c * x)) = (c * x) * deriv ψ0 (c * x) := by ring
    rw [e, abs_mul]
    exact mul_le_mul h (hK _) (abs_nonneg _) (by norm_num)

lemma eLpNorm_two_form {f : ℝ → ℝ} (hf : AEStronglyMeasurable f γ) :
    eLpNorm f 2 γ = (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂γ) ^ (1 / 2 : ℝ) := by
  have := eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (μ := γ) (by norm_num) (by simp) hf
  simpa using this

lemma tendsto_L2_dom {F : ℕ → ℝ → ℝ} {G : ℝ → ℝ} (hG : MemLp G 2 γ)
    (hFm : ∀ k, AEStronglyMeasurable (F k) γ) (hF : ∀ k x, |F k x| ≤ |G x|)
    (hz : ∀ (k : ℕ) (x : ℝ), |x| < (k : ℝ) + 1 → F k x = 0) :
    Tendsto (fun k => eLpNorm (F k) 2 γ) atTop (𝓝 0) := by
  have hfin : ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂γ ≠ ∞ := by
    have h := hG.eLpNorm_lt_top
    rw [eLpNorm_two_form hG.aestronglyMeasurable] at h
    intro h2
    rw [h2] at h
    simp at h
  have hlim : Tendsto (fun k => ∫⁻ x, ‖F k x‖ₑ ^ (2 : ℝ) ∂γ) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence' (μ := γ)
      (F := fun k x => ‖F k x‖ₑ ^ (2 : ℝ)) (f := fun _ => 0) (fun x => ‖G x‖ₑ ^ (2 : ℝ))
      (fun k => (hFm k).enorm.pow_const _) (fun k => ae_of_all _ fun x => by
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
        exact ENNReal.ofReal_le_ofReal (hF k x))
      hfin (ae_of_all _ fun x => by
        obtain ⟨N, hN⟩ := exists_nat_gt |x|
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with k hk
        have : |x| < k + 1 := by
          have : (N : ℝ) ≤ k := by exact_mod_cast hk
          linarith
        rw [hz k x this]; simp)
    simpa using this
  have h2 : Tendsto (fun k => (∫⁻ x, ‖F k x‖ₑ ^ (2 : ℝ) ∂γ) ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp hlim
    simpa [Function.comp_def] using this
  refine h2.congr fun k => ?_
  rw [eLpNorm_two_form (hFm k)]

lemma dcut_bound {K c : ℝ} (hK : ∀ x, |deriv ψ0 x| ≤ K ∧ |deriv (deriv ψ0) x| ≤ K)
    (hc : 0 < c) (hc1 : c ≤ 1) (x : ℝ) : |deriv (cut c) x| ≤ K := by
  rw [deriv_cut]
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0).1
  rw [abs_mul, abs_of_pos hc]
  calc c * |deriv ψ0 (c * x)| ≤ 1 * K := mul_le_mul hc1 (hK _).1 (abs_nonneg _) (by norm_num)
    _ = K := one_mul K

lemma Lo_cut_bound {K c : ℝ} (hK : ∀ x, |deriv ψ0 x| ≤ K ∧ |deriv (deriv ψ0) x| ≤ K)
    (hc : 0 < c) (hc1 : c ≤ 1) (x : ℝ) : |Lo (cut c) x| ≤ 3 * K := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0).1
  have h1 : |deriv (deriv (cut c)) x| ≤ K := by
    rw [deriv_deriv_cut, abs_mul, abs_mul, abs_of_pos hc]
    calc c * (c * |deriv (deriv ψ0) (c * x)|) ≤ 1 * (1 * K) :=
          mul_le_mul hc1 (mul_le_mul hc1 (hK _).2 (abs_nonneg _) (by norm_num)) (by positivity)
            (by norm_num)
      _ = K := by ring
  have h2 := abs_x_dcut_le (c := c) (fun x => (hK x).1) x
  unfold Lo
  calc |deriv (deriv (cut c)) x - x * deriv (cut c) x|
      ≤ |deriv (deriv (cut c)) x| + |x * deriv (cut c) x| := abs_sub _ _
    _ ≤ 3 * K := by linarith

/-- **Cutoff approximation in the graph norm.** -/
theorem cutoff_approx {f : ℝ → ℝ} (hf : Sm f) (h0 : MemLp f 2 γ) (h1 : MemLp (deriv f) 2 γ)
    (h2 : MemLp (Lo f) 2 γ) :
    ∃ g : ℕ → ℝ → ℝ, (∀ k, g k ∈ A₀) ∧
      Tendsto (fun k => eLpNorm (g k - f) 2 γ) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (Lo (g k) - Lo f) 2 γ) atTop (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_K
  set c : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hc
  have hcpos : ∀ k, 0 < c k := fun k => by simp only [hc]; positivity
  have hcle : ∀ k, c k ≤ 1 := fun k => by
    simp only [hc]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hinv : ∀ k, 1 / c k = (k : ℝ) + 1 := fun k => by simp [hc]
  refine ⟨fun k x => cut (c k) x * f x, fun k => ?_, ?_, ?_⟩
  · exact ⟨(cut_sm _).mul hf, (cut_cs (hcpos k)).mul_right⟩
  · have hG : MemLp (fun x => ‖f x‖) 2 γ := h0.norm
    refine tendsto_L2_dom hG (fun k => ?_) (fun k x => ?_) (fun k x hx => ?_)
    · have hcont : Continuous (fun x => cut (c k) x * f x - f x) :=
        ((cut_sm _).mul hf).continuous.sub hf.continuous
      exact hcont.aestronglyMeasurable
    · simp only [Pi.sub_apply, abs_norm]
      have : cut (c k) x * f x - f x = (cut (c k) x - 1) * f x := by ring
      rw [this, abs_mul]
      have h3 : |cut (c k) x - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [cut_nonneg (c k) x, cut_le_one (c k) x]
      calc |cut (c k) x - 1| * |f x| ≤ 1 * |f x| := mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
        _ = |f x| := one_mul _
    · simp only [Pi.sub_apply]
      rw [cut_one (hcpos k) (by rw [hinv]; exact hx.le)]; ring
  · have hG : MemLp (fun x => 3 * K * ‖f x‖ + 2 * K * ‖deriv f x‖ + ‖Lo f x‖) 2 γ :=
      ((h0.norm.const_mul (3 * K)).add (h1.norm.const_mul (2 * K))).add h2.norm
    refine tendsto_L2_dom hG (fun k => ?_) (fun k x => ?_) (fun k x hx => ?_)
    · have hcont : Continuous (Lo (fun x => cut (c k) x * f x) - Lo f) :=
        (sm_Lo ((cut_sm _).mul hf)).continuous.sub (sm_Lo hf).continuous
      exact hcont.aestronglyMeasurable
    · have hm := Lo_mul (cut_sm (c k)) hf x
      have e : (Lo (fun x => cut (c k) x * f x) - Lo f) x =
          Lo (cut (c k)) x * f x + 2 * (deriv (cut (c k)) x * deriv f x)
            - (1 - cut (c k) x) * Lo f x := by
        simp only [Pi.sub_apply]
        rw [show (fun x => cut (c k) x * f x) = cut (c k) * f from rfl, hm]; ring
      rw [e]
      have b1 := Lo_cut_bound hK (hcpos k) (hcle k) x
      have b2 := dcut_bound hK (hcpos k) (hcle k) x
      have b3 : |1 - cut (c k) x| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [cut_nonneg (c k) x, cut_le_one (c k) x]
      have t1 : |Lo (cut (c k)) x * f x| ≤ 3 * K * ‖f x‖ := by
        rw [abs_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right b1 (abs_nonneg _)
      have t2 : |2 * (deriv (cut (c k)) x * deriv f x)| ≤ 2 * K * ‖deriv f x‖ := by
        rw [abs_mul, abs_mul, Real.norm_eq_abs]
        have : |(2 : ℝ)| = 2 := by norm_num
        rw [this]
        have := mul_le_mul_of_nonneg_right b2 (abs_nonneg (deriv f x))
        nlinarith
      have t3 : |(1 - cut (c k) x) * Lo f x| ≤ ‖Lo f x‖ := by
        rw [abs_mul, Real.norm_eq_abs]
        calc |1 - cut (c k) x| * |Lo f x| ≤ 1 * |Lo f x| :=
              mul_le_mul_of_nonneg_right b3 (abs_nonneg _)
          _ = |Lo f x| := one_mul _
      have hnn : 0 ≤ 3 * K * ‖f x‖ + 2 * K * ‖deriv f x‖ + ‖Lo f x‖ := by positivity
      rw [abs_of_nonneg hnn]
      calc |Lo (cut (c k)) x * f x + 2 * (deriv (cut (c k)) x * deriv f x)
              - (1 - cut (c k) x) * Lo f x|
          ≤ |Lo (cut (c k)) x * f x| + |2 * (deriv (cut (c k)) x * deriv f x)|
              + |(1 - cut (c k) x) * Lo f x| := by
            refine (abs_sub _ _).trans ?_
            gcongr
            exact abs_add_le _ _
        _ ≤ _ := by linarith
    · have hx' : |x| < 1 / c k := by rw [hinv]; exact hx
      have e : (Lo (fun x => cut (c k) x * f x) - Lo f) x = 0 := by
        have hm := Lo_mul (cut_sm (c k)) hf x
        simp only [Pi.sub_apply]
        rw [show (fun x => cut (c k) x * f x) = cut (c k) * f from rfl, hm]
        have h1 := dcut_zero (hcpos k) hx'
        have h2 := ddcut_zero (hcpos k) hx'
        have h3 := cut_one (hcpos k) hx'.le
        unfold Lo at *
        rw [h1, h2, h3]; ring
      exact e

end MarkovTriple.Sanity.OU
