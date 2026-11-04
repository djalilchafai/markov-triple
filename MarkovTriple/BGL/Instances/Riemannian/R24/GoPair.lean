import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R24.GoSeries
import MarkovTriple.BGL.Instances.Riemannian.R24.GoCore2

/-!
# Round 24 (stream D), part B2: the deficiency pair for `goFullTriple`

Power-series solution `w = Σ aa_n xⁿ` of `L w = w` (`aa_{n+2} = aa_n (1 - 1/((n+1)(n+2)))`, `aa_0 = 1`, `aa_1 = 0`),
`(1-x²) w = A(x) := Σ dd_n xⁿ` with `Λ = A(±1) = Σ dd_n`, `|A(x) - Λ| ≤ C √(1-x²)`; `h = (Λ/4) log(1-x²)`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.R24

/-- coefficients of `(1-x²) w`. -/
noncomputable def dd : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | (n + 2) => aa (n + 2) - aa n

lemma dd_add_two (n : ℕ) : dd (n + 2) = aa (n + 2) - aa n := rfl

lemma aa_odd : ∀ k : ℕ, aa (2 * k + 1) = 0 := by
  intro k
  induction k with
  | zero => simp [aa_one]
  | succ k ih =>
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [this, aa_add_two, ih, zero_mul]

lemma dd_odd (k : ℕ) : dd (2 * k + 1) = 0 := by
  rcases k with _ | k
  · rfl
  · have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    have h1 := aa_odd (k + 1)
    have h2 := aa_odd k
    rw [this] at h1
    rw [this, dd_add_two, h1, h2, sub_zero]

lemma abs_dd_le (n : ℕ) : |dd (n + 2)| ≤ 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)) := by
  rw [dd_add_two, aa_add_two]
  have hp : (0 : ℝ) < ((n : ℝ) + 1) * ((n : ℝ) + 2) := by positivity
  have e : aa n * (1 - 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) - aa n =
      -(aa n * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))) := by ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg (aa_bounds n).1 (by positivity))]
  calc aa n * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) ≤ 1 * (1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_right (aa_bounds n).2 (by positivity)
    _ = _ := one_mul _

/-- `|dd n| √n ≤ 2 n^{-3/2}` (for all `n`). -/
lemma ee_le (n : ℕ) : |dd n| * Real.sqrt n ≤ 2 * (((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := by
  rcases n with _ | _ | m
  · simp [dd]
  · simp [dd]
  · have h1 := abs_dd_le m
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hn2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have h2 : ((m + 2 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    rw [h2]
    have h3 : ((m : ℝ) + 2) ^ ((3 : ℝ) / 2) = ((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn2.le (by norm_num)]
      norm_num
    rw [h3]
    have hs : 0 < Real.sqrt ((m : ℝ) + 2) := Real.sqrt_pos.2 hn2
    have h4 : 1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤ 2 / (((m : ℝ) + 2) * ((m : ℝ) + 2)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc |dd (m + 2)| * Real.sqrt ((m : ℝ) + 2)
        ≤ (2 / (((m : ℝ) + 2) * ((m : ℝ) + 2))) * Real.sqrt ((m : ℝ) + 2) := by
          apply mul_le_mul_of_nonneg_right (h1.trans h4) hs.le
      _ = 2 * ((((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2))⁻¹) := by
          have : Real.sqrt ((m : ℝ) + 2) * Real.sqrt ((m : ℝ) + 2) = (m : ℝ) + 2 :=
            Real.mul_self_sqrt hn2.le
          field_simp
          nlinarith [this]


lemma summable_ee : Summable (fun n : ℕ => |dd n| * Real.sqrt n) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) ee_le
    ((Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2)

lemma summable_abs_dd : Summable (fun n : ℕ => |dd n|) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    ((summable_nat_add_iff 1).2 summable_ee)
  have h1 : (1 : ℝ) ≤ Real.sqrt ((n + 1 : ℕ) : ℝ) := by
    rw [Real.one_le_sqrt]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact le_mul_of_one_le_right (abs_nonneg _) h1

lemma summable_dd_mul {x : ℝ} (hx : |x| ≤ 1) : Summable (fun n : ℕ => dd n * x ^ n) := by
  refine Summable.of_norm_bounded summable_abs_dd fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hx)

/-- `A(x) = Σ dd_n xⁿ`. -/
noncomputable def A (x : ℝ) : ℝ := ∑' n, dd n * x ^ n

/-- `Λ = A(1)`. -/
noncomputable def Lam : ℝ := ∑' n, dd n

lemma A_eq {x : ℝ} (hx : |x| < 1) : A x = (1 - x ^ 2) * P aa x := by
  have hA : Summable (fun n : ℕ => aa n * x ^ n) := summable_P (B := 1) (m := 0) zero_le_one abs_aa_le hx
  have hA2 : Summable (fun n : ℕ => aa (n + 2) * x ^ (n + 2)) :=
    (summable_nat_add_iff 2 (f := fun n : ℕ => aa n * x ^ n)).2 hA
  have hAs : Summable (fun n : ℕ => aa n * x ^ (n + 2)) := by
    refine (hA.mul_left (x ^ 2)).congr fun n => ?_
    ring
  have hD : Summable (fun n : ℕ => dd n * x ^ n) := summable_dd_mul hx.le
  have e1 : A x = dd 0 + dd 1 * x + ∑' n, dd (n + 2) * x ^ (n + 2) := by
    have := tsum_two hD
    simpa [A] using this
  have e2 : P aa x = aa 0 + aa 1 * x + ∑' n, aa (n + 2) * x ^ (n + 2) := by
    have := tsum_two hA
    simpa [P] using this
  have e4 : x ^ 2 * P aa x = ∑' n, aa n * x ^ (n + 2) := by
    rw [P, ← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have hsub : ∑' n, dd (n + 2) * x ^ (n + 2) = ∑' n, aa (n + 2) * x ^ (n + 2) - ∑' n, aa n * x ^ (n + 2) := by
    rw [← hA2.tsum_sub hAs]
    exact tsum_congr fun n => by rw [dd_add_two]; ring
  rw [e1, hsub]
  have e3 : (1 - x ^ 2) * P aa x = P aa x - x ^ 2 * P aa x := by ring
  rw [e3, e4, e2]
  simp [dd, aa_zero, aa_one]
  ring

lemma abs_sub_le_sqrt {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    |dd n| * |x ^ n - 1| ≤ |dd n| * Real.sqrt n * Real.sqrt (1 - x ^ 2) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst hk
    set s : ℝ := 1 - x ^ 2 with hs
    have hs0 : 0 < s := by
      have : x ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg x]
      linarith
    have hs1 : s ≤ 1 := by nlinarith [sq_nonneg x]
    have ht : x ^ (2 * k) = (1 - s) ^ k := by rw [pow_mul, hs]; ring_nf
    have hb := one_add_mul_le_pow (a := -s) (by linarith) k
    have hb2 : 0 ≤ (1 - s) ^ k := pow_nonneg (by nlinarith [sq_nonneg x]) k
    have hb3 : (1 - s) ^ k ≤ 1 := pow_le_one₀ (by nlinarith [sq_nonneg x]) (by linarith)
    have hy : |x ^ (2 * k) - 1| ≤ Real.sqrt ((2 * k : ℕ) * s) := by
      rw [ht, abs_of_nonpos (by linarith)]
      apply Real.le_sqrt_of_sq_le
      push_cast
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have hb' : 1 - (k : ℝ) * s ≤ (1 - s) ^ k := by
        have := hb; rw [← sub_eq_add_neg] at this; linarith
      set y : ℝ := 1 - (1 - s) ^ k with hy
      have hy0 : 0 ≤ y := by rw [hy]; linarith
      have hy1 : y ≤ 1 := by rw [hy]; linarith
      have hy2 : y ≤ k * s := by rw [hy]; linarith
      have : (-((1 - s) ^ k - 1)) = y := by rw [hy]; ring
      rw [this]
      nlinarith [mul_nonneg hk0 hs0.le, mul_nonneg hy0 (sub_nonneg.2 hy1)]
    calc |dd (2 * k)| * |x ^ (2 * k) - 1| ≤ |dd (2 * k)| * Real.sqrt ((2 * k : ℕ) * s) :=
          mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg _)]; ring
  · subst hk
    rw [dd_odd]
    simp


/-- `C₀ = Σ |dd_n| √n`. -/
noncomputable def C0 : ℝ := ∑' n : ℕ, |dd n| * Real.sqrt n

lemma C0_nonneg : 0 ≤ C0 := tsum_nonneg fun _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)

/-- the Hölder-`1/2` estimate `|A(x) - Λ| ≤ C₀ √(1-x²)`. -/
theorem holder {x : ℝ} (hx : |x| < 1) : |A x - Lam| ≤ C0 * Real.sqrt (1 - x ^ 2) := by
  have h1 := summable_dd_mul hx.le
  have h2 : Summable dd := summable_abs_dd.of_abs
  have e : A x - Lam = ∑' n, (dd n * x ^ n - dd n) := by
    rw [A, Lam, ← h1.tsum_sub h2]
  rw [e]
  have hg : HasSum (fun n : ℕ => |dd n| * Real.sqrt n * Real.sqrt (1 - x ^ 2))
      (C0 * Real.sqrt (1 - x ^ 2)) := summable_ee.hasSum.mul_right _
  have := tsum_of_norm_bounded hg (f := fun n : ℕ => dd n * x ^ n - dd n) (fun n => by
    rw [Real.norm_eq_abs]
    calc |dd n * x ^ n - dd n| = |dd n * (x ^ n - 1)| := by ring_nf
      _ ≤ _ := by rw [abs_mul]; exact abs_sub_le_sqrt hx n)
  simpa [Real.norm_eq_abs] using this


/-! ### the solution `w`, the function `h`, and their generators -/

/-- the solution `w = Σ aa_n xⁿ` of `L w = w`. -/
noncomputable abbrev wf : ℝ → ℝ := P aa

lemma wf_smooth : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) wf (Ioo (-1 : ℝ) 1) :=
  contDiffOn_infty.2 fun n => contDiffOn_P n aa 1 0 zero_le_one abs_aa_le

lemma wf_L {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : goL wf x = wf x := by
  have h1 : deriv wf x = P (D aa) x := deriv_P (B := 1) (m := 0) zero_le_one abs_aa_le hx
  have h2 : deriv wf =ᶠ[𝓝 x] P (D aa) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact deriv_P (B := 1) (m := 0) zero_le_one abs_aa_le hy
  have h3 : deriv (deriv wf) x = P (D (D aa)) x := by
    rw [h2.deriv_eq]
    exact deriv_P (B := 1) (m := 1) zero_le_one abs_Daa_le hx
  have := ode_series (abs_lt_one_of_mem hx)
  simp only [goL, h1, h3]
  linarith

lemma wf_zero : wf 0 = 1 := by
  simp only [P]
  rw [tsum_eq_single 0]
  · simp [aa_zero]
  · intro n hn; simp [hn]

/-- `h = α log(1-x²)`. -/
noncomputable def hf (α : ℝ) (x : ℝ) : ℝ := α * Real.log (1 - x ^ 2)

lemma one_sub_sq_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

lemma hasDerivAt_hf (α : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (hf α) (α * (-2 * x) / (1 - x ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have h2 := (h1.log (one_sub_sq_pos hx).ne').const_mul α
  have e : α * (-2 * x) / (1 - x ^ 2) = α * (-(2 * x) / (1 - x ^ 2)) := by ring
  rw [e]
  exact h2

lemma hf_L (α : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    goL (hf α) x = α * (6 * x ^ 2 - 2) / (1 - x ^ 2) := by
  have hpos := one_sub_sq_pos hx
  have h1 : deriv (hf α) x = α * (-2 * x) / (1 - x ^ 2) := (hasDerivAt_hf α hx).deriv
  have h2 : deriv (hf α) =ᶠ[𝓝 x] fun y => α * (-2 * y) / (1 - y ^ 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact (hasDerivAt_hf α hy).deriv
  have h3 : HasDerivAt (fun y : ℝ => α * (-2 * y) / (1 - y ^ 2))
      ((α * (-2) * (1 - x ^ 2) - α * (-2 * x) * (-(2 * x))) / (1 - x ^ 2) ^ 2) x := by
    have hn : HasDerivAt (fun y : ℝ => α * (-2 * y)) (α * (-2)) x := by
      simpa using ((hasDerivAt_id x).const_mul (-2 : ℝ)).const_mul α
    have hd : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
      simpa using ((hasDerivAt_pow 2 x).const_sub 1)
    exact hn.div hd hpos.ne'
  have h4 : deriv (deriv (hf α)) x = (α * (-2) * (1 - x ^ 2) - α * (-2 * x) * (-(2 * x))) / (1 - x ^ 2) ^ 2 := by
    rw [h2.deriv_eq]; exact h3.deriv
  simp only [goL, h1, h4]
  field_simp
  ring

lemma hf_smooth (α : ℝ) : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hf α) (Ioo (-1 : ℝ) 1) := by
  refine contDiffOn_const.mul (ContDiffOn.log ?_ fun x hx => (one_sub_sq_pos hx).ne')
  exact (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn


/-- `L²(goμ)` membership from a weighted bound. -/
lemma memLp_go {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo (-1 : ℝ) 1)) (C : ℝ)
    (hb : ∀ x ∈ Ioo (-1 : ℝ) 1, (1 - x ^ 2) * f x ^ 2 ≤ C) : MemLp f 2 goμ := by
  have hm : AEStronglyMeasurable f goμ :=
    (hf.aestronglyMeasurable measurableSet_Ioo).mono_measure goμ_le
  rw [memLp_two_iff_integrable_sq hm]
  rw [integrable_withDensity_iff_integrable_smul' measurable_goρ
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have : IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 1)) := ⟨by simp⟩
  have hm2 : AEStronglyMeasurable (fun x : ℝ => (ENNReal.ofReal (3 / 4 * (1 - x ^ 2))).toReal • f x ^ 2)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    have hd : Measurable (fun x : ℝ => (ENNReal.ofReal (3 / 4 * (1 - x ^ 2))).toReal) :=
      measurable_goρ.ennreal_toReal
    have := hd.aestronglyMeasurable.mul ((hf.aestronglyMeasurable (μ := volume) measurableSet_Ioo).pow 2)
    exact this.congr (Filter.Eventually.of_forall fun x => rfl)
  refine (integrable_const (3 / 4 * C)).mono' hm2 ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hd : 0 ≤ 3 / 4 * (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
  rw [Real.norm_eq_abs, smul_eq_mul, ENNReal.toReal_ofReal hd,
    abs_of_nonneg (mul_nonneg hd (sq_nonneg _))]
  have := hb x hx
  nlinarith

/-- the weighted bound for `g = w - L h`. -/
theorem g_bound {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    (1 - x ^ 2) * (wf x - goL (hf (Lam / 4)) x) ^ 2 ≤ (C0 + 6 * |Lam / 4|) ^ 2 := by
  set α : ℝ := Lam / 4 with hα
  set s : ℝ := 1 - x ^ 2 with hs
  have hs0 : 0 < s := one_sub_sq_pos hx
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg x]
  have hAx : A x = s * wf x := A_eq (abs_lt_one_of_mem hx)
  have hL := hf_L α hx
  have hsg : s * (wf x - goL (hf α) x) = (A x - Lam) + 6 * α * s := by
    rw [hL, mul_sub, ← hAx]
    have : s * (α * (6 * x ^ 2 - 2) / (1 - x ^ 2)) = α * (6 * x ^ 2 - 2) := by
      rw [← hs]; field_simp
    rw [this, hα]
    have : x ^ 2 = 1 - s := by rw [hs]; ring
    rw [this]; ring
  have hh := holder (abs_lt_one_of_mem hx)
  have hsq : s ≤ Real.sqrt s := by
    have h1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.2 hs1
    have h2 : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs0.le
    nlinarith [Real.sqrt_nonneg s]
  have hsg2 : |s * (wf x - goL (hf α) x)| ≤ (C0 + 6 * |α|) * Real.sqrt s := by
    rw [hsg]
    calc |(A x - Lam) + 6 * α * s| ≤ |A x - Lam| + |6 * α * s| := abs_add_le _ _
      _ ≤ C0 * Real.sqrt s + 6 * |α| * s := by
          rw [abs_mul, abs_mul, abs_of_nonneg hs0.le]
          have : |(6 : ℝ)| = 6 := abs_of_pos (by norm_num)
          rw [this]
          linarith [hh]
      _ ≤ _ := by nlinarith [abs_nonneg α, Real.sqrt_nonneg s]
  set y : ℝ := s * (wf x - goL (hf α) x) with hy
  set K : ℝ := C0 + 6 * |α| with hK
  have hK0 : 0 ≤ K := by positivity [C0_nonneg]
  have hy2 : y ^ 2 ≤ K ^ 2 * s := by
    have h1 : y ^ 2 ≤ (K * Real.sqrt s) ^ 2 := by
      rw [← sq_abs y]
      exact pow_le_pow_left₀ (abs_nonneg _) hsg2 2
    rw [mul_pow K (Real.sqrt s) 2, Real.sq_sqrt hs0.le] at h1
    exact h1
  have h3 : s * (s * (wf x - goL (hf α) x) ^ 2) ≤ s * K ^ 2 := by
    calc s * (s * (wf x - goL (hf α) x) ^ 2) = y ^ 2 := by rw [hy]; ring
      _ ≤ K ^ 2 * s := hy2
      _ = s * K ^ 2 := by ring
  exact le_of_mul_le_mul_left h3 hs0


lemma s_log_sq_le {s : ℝ} (h0 : 0 < s) (h1 : s ≤ 1) : s * Real.log s ^ 2 ≤ 4 := by
  set r : ℝ := Real.sqrt s with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 h0
  have hr1 : r ≤ 1 := Real.sqrt_le_one.2 h1
  have hrr : r * r = s := Real.mul_self_sqrt h0.le
  have hl : Real.log s = 2 * Real.log r := by
    have := Real.log_sqrt h0.le
    rw [← hr] at this
    linarith
  have h2 : 1 - r⁻¹ ≤ Real.log r := Real.one_sub_inv_le_log_of_pos hr0
  have h3 : Real.log r ≤ 0 := Real.log_nonpos hr0.le hr1
  have h4 : r - 1 ≤ r * Real.log r := by
    have := mul_le_mul_of_nonneg_left h2 hr0.le
    rw [mul_sub, mul_one, mul_inv_cancel₀ hr0.ne'] at this
    linarith
  have h5 : r * Real.log r ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr0.le h3
  have h6 : (r * Real.log r) ^ 2 ≤ 1 := by nlinarith
  rw [hl, ← hrr]
  nlinarith [h6]

end MarkovTriple.BGL.Instances.GegenbauerOpen.R24

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open MarkovTriple.BGL.Instances.GegenbauerOpen.R24

/-- **B2**: the deficiency pair exists. -/
theorem go_deficiency_pair : ∃ w h : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1) ∧ (∀ x ∈ Ioo (-1 : ℝ) 1, goL w x = w x) ∧
    MemLp h 2 goμ ∧ MemLp (fun x => w x - goL h x) 2 goμ ∧ ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0 := by
  set α : ℝ := Lam / 4 with hα
  refine ⟨wf, hf α, wf_smooth, hf_smooth α, fun x hx => wf_L hx, ?_, ?_, ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩⟩
  · refine memLp_go (hf_smooth α).continuousOn (4 * α ^ 2) fun x hx => ?_
    have hs0 := one_sub_sq_pos hx
    have hs1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
    have := s_log_sq_le hs0 hs1
    have e : (1 - x ^ 2) * hf α x ^ 2 = α ^ 2 * ((1 - x ^ 2) * Real.log (1 - x ^ 2) ^ 2) := by
      simp only [hf]; ring
    rw [e]
    nlinarith [sq_nonneg α]
  · refine memLp_go ?_ ((C0 + 6 * |α|) ^ 2) fun x hx => g_bound hx
    have h1 : ContinuousOn wf (Ioo (-1 : ℝ) 1) := wf_smooth.continuousOn
    have h2 : ContinuousOn (fun x : ℝ => α * (6 * x ^ 2 - 2) / (1 - x ^ 2)) (Ioo (-1 : ℝ) 1) :=
      ContinuousOn.div (by fun_prop) (by fun_prop) fun x hx => (one_sub_sq_pos hx).ne'
    exact h1.sub (h2.congr fun x hx => hf_L α hx)
  · rw [wf_zero]; norm_num

/-- **B3 (new): `Core2` FAILS for the non-complete triple `goFullTriple`** (F1–F10 and `CD(3,4)` hold). -/
theorem goFullTriple_not_core2 : ¬ goFullTriple.Core2 := by
  obtain ⟨w, h, hw, hh, hwL, hh2, hg2, hne⟩ := go_deficiency_pair
  exact go_not_core2_of_pair w h hw hh hwL hh2 hg2 hne

/-- **B4**: F1–F10 + `CD` do not imply `Core2`. -/
theorem exists_fullTriple_cd_not_core2 : ∃ T : FullTriple ℝ, T.CD 3 4 ∧ ¬ T.Core2 :=
  ⟨goFullTriple, goFullTriple_CD, goFullTriple_not_core2⟩

end MarkovTriple.BGL.Instances.GegenbauerOpen
