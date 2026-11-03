import Mathlib
import MarkovTriple.BGL.Instances.Lebesgue.Core

/-!
# Brownian triple on `(ℝ, Lebesgue)`: cut-off approximation in the graph norm of `L²` (fourth derivatives)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Lebesgue

lemma iter_sm (j : ℕ) : Sm (deriv^[j] chi) := by
  induction j with
  | zero => exact chi_smooth
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.deriv'

lemma iter_cs (j : ℕ) : HasCompactSupport (deriv^[j] chi) := by
  induction j with
  | zero => exact chi_cs
  | succ j ih => rw [Function.iterate_succ_apply']; exact ih.deriv

lemma iter_bound (j : ℕ) : ∃ C, 0 ≤ C ∧ ∀ x, |deriv^[j] chi x| ≤ C := by
  obtain ⟨C, hC⟩ := (iter_sm j).continuous.bounded_above_of_compact_support (iter_cs j)
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    simp only [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

lemma iter_zero (j : ℕ) {y : ℝ} (hy : |y| < 1) : deriv^[j + 1] chi y = 0 := by
  induction j generalizing y with
  | zero =>
    have : {z : ℝ | |z| < 1} ∈ 𝓝 y := (isOpen_lt continuous_abs continuous_const).mem_nhds hy
    have e : chi =ᶠ[𝓝 y] fun _ => 1 := by
      filter_upwards [this] with z hz using chi_eq_one hz.le
    show deriv chi y = 0
    rw [e.deriv_eq]; simp
  | succ j ih =>
    have : {z : ℝ | |z| < 1} ∈ 𝓝 y := (isOpen_lt continuous_abs continuous_const).mem_nhds hy
    have e : deriv^[j + 1] chi =ᶠ[𝓝 y] fun _ => 0 := by
      filter_upwards [this] with z hz using ih hz
    rw [Function.iterate_succ_apply']
    rw [e.deriv_eq]; simp

lemma iter_chiR (j : ℕ) (R : ℝ) : deriv^[j] (chiR R) = fun x => deriv^[j] chi (x / R) / R ^ j := by
  induction j with
  | zero => funext x; simp [chiR]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    funext x
    have h1 : HasDerivAt (fun x : ℝ => x / R) (1 / R) x := (hasDerivAt_id x).div_const R
    have := ((iter_sm j).hasDerivAt (x / R)).comp x h1
    have h2 := this.div_const (R ^ j)
    refine h2.deriv.trans ?_
    rw [Function.iterate_succ_apply']
    by_cases hR : R = 0
    · simp [hR]
    · field_simp
      ring

/-- pointwise expansion of `(u f)'''' − f''''`. -/
lemma LL_mul {u f : ℝ → ℝ} (hu : Sm u) (hf : Sm f) (x : ℝ) :
    Lf (Lf (u * f)) x - Lf (Lf f) x =
      (u x - 1) * Lf (Lf f) x + 4 * (deriv u x * deriv (Lf f) x) + 6 * (Lf u x * Lf f x)
      + 4 * (deriv (Lf u) x * deriv f x) + Lf (Lf u) x * f x := by
  have hLu : Sm (Lf u) := hu.deriv'.deriv'
  have hLf : Sm (Lf f) := hf.deriv'.deriv'
  have hdu := hu.deriv'
  have hdf := hf.deriv'
  have e1 : Lf (u * f) = Lf u * f + (2 : ℝ) • (deriv u * deriv f) + u * Lf f := by
    funext y
    rw [Lf_mul hu hf y]
    simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  have hA : Sm (Lf u * f) := hLu.mul hf
  have hB : Sm (deriv u * deriv f) := hdu.mul hdf
  have hC : Sm (u * Lf f) := hu.mul hLf
  have hB2 : Sm ((2 : ℝ) • (deriv u * deriv f)) := hB.const_smul (2 : ℝ)
  have hAB : Sm (Lf u * f + (2 : ℝ) • (deriv u * deriv f)) := hA.add hB2
  have lin : ∀ {a b : ℝ → ℝ}, Sm a → Sm b → Lf (a + b) = Lf a + Lf b := by
    intro a b ha hb
    funext y
    unfold Lf
    rw [deriv_add_sm ha hb, deriv_add_sm ha.deriv' hb.deriv']
  have lins : ∀ (c : ℝ) {a : ℝ → ℝ}, Sm a → Lf (c • a) = c • Lf a := by
    intro c a ha
    funext y
    unfold Lf
    rw [deriv_smul_sm c ha, deriv_smul_sm c ha.deriv']
  rw [e1, lin hAB hC, lin hA hB2, lins 2 hB]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [Lf_mul hLu hf x, Lf_mul hdu hdf x, Lf_mul hu hLf x]
  have d1 : deriv (Lf u) = fun y => deriv (deriv (deriv u)) y := rfl
  simp only [Lf]
  ring

/-- `∫ ((χ_n v)⁗ − v⁗)² → 0` for `v` smooth with `v, …, v⁗ ∈ L²` (⁗ = fourth derivative). -/
theorem cutoff4_tendsto {v : ℝ → ℝ} (hv : Sm v) (h0 : MemLp v 2 volume) (h1 : MemLp (deriv v) 2 volume)
    (h2 : MemLp (deriv (deriv v)) 2 volume) (h3 : MemLp (deriv (deriv (deriv v))) 2 volume)
    (h4 : MemLp (deriv (deriv (deriv (deriv v)))) 2 volume) :
    Tendsto (fun n : ℕ => ∫ x, (Lf (Lf (chiR (Rn n) * v)) x - Lf (Lf v) x) ^ 2) atTop (𝓝 0) := by
  obtain ⟨C1, hC1, hb1⟩ := iter_bound 1
  obtain ⟨C2, hC2, hb2⟩ := iter_bound 2
  obtain ⟨C3, hC3, hb3⟩ := iter_bound 3
  obtain ⟨C4, hC4, hb4⟩ := iter_bound 4
  set K : ℝ := C1 + C2 + C3 + C4 + 1 with hK
  have hK1 : 1 ≤ K := by linarith
  have hRn : ∀ n, 1 ≤ Rn n := fun n => by unfold Rn; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have bound : ∀ (j : ℕ) (C : ℝ), (∀ y, |deriv^[j] chi y| ≤ C) → C ≤ K → ∀ n x,
      |deriv^[j] (chiR (Rn n)) x| ≤ K := by
    intro j C hC hCK n x
    rw [iter_chiR, abs_div, abs_of_pos (pow_pos (Rn_pos n) j)]
    have : 1 ≤ Rn n ^ j := one_le_pow₀ (hRn n)
    calc |deriv^[j] chi (x / Rn n)| / Rn n ^ j ≤ |deriv^[j] chi (x / Rn n)| :=
          div_le_self (abs_nonneg _) this
      _ ≤ C := hC _
      _ ≤ K := hCK
  have B1 := bound 1 C1 hb1 (by linarith)
  have B2 := bound 2 C2 hb2 (by linarith)
  have B3 := bound 3 C3 hb3 (by linarith)
  have B4 := bound 4 C4 hb4 (by linarith)
  have Z : ∀ (j : ℕ) (n : ℕ) (x : ℝ), |x| < Rn n → deriv^[j + 1] (chiR (Rn n)) x = 0 := by
    intro j n x hx
    rw [iter_chiR]
    have : |x / Rn n| < 1 := by
      rw [abs_div, abs_of_pos (Rn_pos n), div_lt_one (Rn_pos n)]; exact hx
    simp [iter_zero j this]
  set G : ℝ → ℝ := fun x => 6 * K * (|deriv (deriv (deriv (deriv v))) x| + |deriv (deriv (deriv v)) x| +
    |deriv (deriv v) x| + |deriv v x| + |v x|) with hG
  have hGL : MemLp G 2 volume :=
    (((((h4.norm.add h3.norm).add h2.norm).add h1.norm).add h0.norm).const_mul (6 * K))
  have hid := fun n x => LL_mul (chiR_smooth (Rn n)) hv x
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun x => (Lf (Lf (chiR (Rn n) * v)) x - Lf (Lf v) x) ^ 2) volume := by
    intro n
    have hs : Sm (Lf (Lf (chiR (Rn n) * v))) := ((chiR_smooth _).mul hv).deriv'.deriv'.deriv'.deriv'
    have hs' : Sm (Lf (Lf v)) := hv.deriv'.deriv'.deriv'.deriv'
    exact ((hs.continuous.sub hs'.continuous).pow 2).aestronglyMeasurable
  have hdom : ∀ n, ∀ᵐ x ∂(volume : Measure ℝ),
      ‖(Lf (Lf (chiR (Rn n) * v)) x - Lf (Lf v) x) ^ 2‖ ≤ (fun x => (G x) ^ 2) x := by
    intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hid]
    have b1 : |deriv (chiR (Rn n)) x| ≤ K := B1 n x
    have b2 : |Lf (chiR (Rn n)) x| ≤ K := B2 n x
    have b3 : |deriv (Lf (chiR (Rn n))) x| ≤ K := B3 n x
    have b4 : |Lf (Lf (chiR (Rn n))) x| ≤ K := B4 n x
    have mk : ∀ (a q m : ℝ), |a| ≤ K → 0 ≤ m → m ≤ 6 → |m * (a * q)| ≤ 6 * K * |q| := by
      intro a q m ha hm hm'
      rw [abs_mul, abs_mul, abs_of_nonneg hm]
      have : |a| * |q| ≤ K * |q| := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
      have h4' : m * (|a| * |q|) ≤ 6 * (K * |q|) := mul_le_mul hm' this (by positivity) (by norm_num)
      nlinarith [abs_nonneg q]
    have t0 : |(chiR (Rn n) x - 1) * Lf (Lf v) x| ≤ 6 * K * |Lf (Lf v) x| := by
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_right (abs_chiR_sub_one_le (Rn n) x) (abs_nonneg (Lf (Lf v) x))
      nlinarith [abs_nonneg (Lf (Lf v) x)]
    have t1 := mk _ (deriv (Lf v) x) 4 b1 (by norm_num) (by norm_num)
    have t2 := mk _ (Lf v x) 6 b2 (by norm_num) (by norm_num)
    have t3 := mk _ (deriv v x) 4 b3 (by norm_num) (by norm_num)
    have t4 := mk _ (v x) 1 b4 (by norm_num) (by norm_num)
    rw [one_mul] at t4
    have s1 := abs_add_le ((chiR (Rn n) x - 1) * Lf (Lf v) x + 4 * (deriv (chiR (Rn n)) x * deriv (Lf v) x)
      + 6 * (Lf (chiR (Rn n)) x * Lf v x) + 4 * (deriv (Lf (chiR (Rn n))) x * deriv v x))
      (Lf (Lf (chiR (Rn n))) x * v x)
    have s2 := abs_add_le ((chiR (Rn n) x - 1) * Lf (Lf v) x + 4 * (deriv (chiR (Rn n)) x * deriv (Lf v) x)
      + 6 * (Lf (chiR (Rn n)) x * Lf v x)) (4 * (deriv (Lf (chiR (Rn n))) x * deriv v x))
    have s3 := abs_add_le ((chiR (Rn n) x - 1) * Lf (Lf v) x + 4 * (deriv (chiR (Rn n)) x * deriv (Lf v) x))
      (6 * (Lf (chiR (Rn n)) x * Lf v x))
    have s4 := abs_add_le ((chiR (Rn n) x - 1) * Lf (Lf v) x) (4 * (deriv (chiR (Rn n)) x * deriv (Lf v) x))
    have hle : |(chiR (Rn n) x - 1) * Lf (Lf v) x + 4 * (deriv (chiR (Rn n)) x * deriv (Lf v) x)
      + 6 * (Lf (chiR (Rn n)) x * Lf v x) + 4 * (deriv (Lf (chiR (Rn n))) x * deriv v x)
      + Lf (Lf (chiR (Rn n))) x * v x| ≤ G x := by
      simp only [hG, Lf] at *
      linarith
    calc _ = |_| ^ 2 := (sq_abs _).symm
      _ ≤ (G x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hle 2
  have hlim : ∀ᵐ x ∂(volume : Measure ℝ), Tendsto
      (fun n : ℕ => (Lf (Lf (chiR (Rn n) * v)) x - Lf (Lf v) x) ^ 2) atTop (𝓝 0) := by
    refine Filter.Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with n hn
    have h1' : |x| < Rn n := by
      unfold Rn
      have := (Nat.le_ceil |x|).trans (by exact_mod_cast hn : (⌈|x|⌉₊ : ℝ) ≤ n)
      linarith
    rw [hid]
    have z1 := Z 0 n x h1'
    have z2 := Z 1 n x h1'
    have z3 := Z 2 n x h1'
    have z4 := Z 3 n x h1'
    have o : chiR (Rn n) x - 1 = 0 := by rw [chiR_eq_one_of (Rn_pos n) h1'.le]; ring
    have z1' : deriv (chiR (Rn n)) x = 0 := z1
    have z2' : Lf (chiR (Rn n)) x = 0 := z2
    have z3' : deriv (Lf (chiR (Rn n))) x = 0 := z3
    have z4' : Lf (Lf (chiR (Rn n))) x = 0 := z4
    rw [o, z1', z2', z3', z4']; ring
  have key := tendsto_integral_of_dominated_convergence (μ := (volume : Measure ℝ))
    (F := fun (n : ℕ) x => (Lf (Lf (chiR (Rn n) * v)) x - Lf (Lf v) x) ^ 2) (f := fun _ => (0 : ℝ))
    (fun x => (G x) ^ 2) hmeas hGL.integrable_sq hdom hlim
  simpa using key

end MarkovTriple.BGL.Lebesgue
