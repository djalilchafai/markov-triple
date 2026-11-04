import Mathlib

/-!
# Round 24 (stream D), part B2a: power-series calculus on `(-1,1)` (helper for `GoPair.lean`)

`P b y = Σ b_n yⁿ`; for polynomially bounded coefficients `P b` is differentiable on `(-1,1)` with derivative
`P (D b)`, `D b n = (n+1) b_{n+1}`, and hence smooth.  See `STATEMENTS_R24_D.md`.
-/

open Filter Topology Set

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.R24

/-- the power series `Σ b_n yⁿ`. -/
noncomputable def P (b : ℕ → ℝ) (y : ℝ) : ℝ := ∑' n, b n * y ^ n

/-- derivative coefficients. -/
def D (b : ℕ → ℝ) : ℕ → ℝ := fun n => ((n : ℝ) + 1) * b (n + 1)

lemma summable_pow_mul_geom (k : ℕ) {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) :
    Summable (fun n : ℕ => (n : ℝ) ^ k * r ^ n) :=
  summable_pow_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)

theorem hasDerivAt_P (b : ℕ → ℝ) (B : ℝ) (hB : 0 ≤ B) (m : ℕ)
    (hb : ∀ n, |b n| ≤ B * ((n : ℝ) + 1) ^ m) {x : ℝ}
    (hx : |x| < 1) : HasDerivAt (P b) (P (D b) x) x := by
  set r : ℝ := (|x| + 1) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hxr : |x| < r := by rw [hr]; linarith
  set K : ℝ := B * 2 ^ m with hK
  have hK0 : 0 ≤ K := by positivity
  set u : ℕ → ℝ := fun n => (K / r) * ((n : ℝ) ^ (m + 1) * r ^ n) with hu
  have hus : Summable u := (summable_pow_mul_geom (m + 1) hr0.le hr1).mul_left _
  have hxs : x ∈ Ioo (-r) r := ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩
  have hy₀ : (0 : ℝ) ∈ Ioo (-r) r := ⟨by linarith, hr0⟩
  have hbound : ∀ (n : ℕ) (y : ℝ), y ∈ Ioo (-r) r → ‖b n * ((n : ℝ) * y ^ (n - 1))‖ ≤ u n := by
    intro n y hy
    have hya : |y| ≤ r := abs_le.2 ⟨hy.1.le, hy.2.le⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hu]
    · have h1 : |y ^ (n - 1)| ≤ r ^ (n - 1) := by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hya _
      have h2 : |b n| ≤ K * (n : ℝ) ^ m := by
        refine (hb n).trans ?_
        rw [hK, mul_assoc, ← mul_pow]
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ m) hB
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      have hrn : r ^ n = r ^ (n - 1) * r := by
        rw [← pow_succ]; congr 1; omega
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ n)]
      have h3 : K / r * ((n : ℝ) ^ (m + 1) * r ^ n) = K * (n : ℝ) ^ m * (n * r ^ (n - 1)) := by
        rw [hrn, pow_succ]; field_simp
      show _ ≤ K / r * ((n : ℝ) ^ (m + 1) * r ^ n)
      rw [h3]
      calc |b n| * ((n : ℝ) * |y ^ (n - 1)|) ≤ (K * (n : ℝ) ^ m) * ((n : ℝ) * r ^ (n - 1)) := by
            apply mul_le_mul h2 (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity)
              (by positivity)
        _ = _ := by ring
  have hg0 : Summable (fun n : ℕ => b n * (0 : ℝ) ^ n) := by
    refine summable_of_ne_finset_zero (s := {0}) fun n hn => ?_
    have : n ≠ 0 := by simpa using hn
    simp [this]
  have key := hasDerivAt_tsum_of_isPreconnected (g := fun n y => b n * y ^ n)
    (g' := fun n y => b n * ((n : ℝ) * y ^ (n - 1))) hus isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => (hasDerivAt_pow n y).const_mul (b n)) hbound hy₀ hg0 hxs
  have hsum : Summable (fun n : ℕ => b n * ((n : ℝ) * x ^ (n - 1))) :=
    Summable.of_norm_bounded hus (fun n => hbound n x hxs)
  have e : ∑' n : ℕ, b n * ((n : ℝ) * x ^ (n - 1)) = P (D b) x := by
    rw [hsum.tsum_eq_zero_add]
    simp only [P, D, Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel]
    refine tsum_congr fun n => ?_
    push_cast; ring
  rw [e] at key
  exact key

lemma D_bound {b : ℕ → ℝ} {B : ℝ} {m : ℕ} (hb : ∀ n, |b n| ≤ B * ((n : ℝ) + 1) ^ m) (hB : 0 ≤ B) :
    ∀ n, |D b n| ≤ (B * 2 ^ m) * ((n : ℝ) + 1) ^ (m + 1) := by
  intro n
  have h1 := hb (n + 1)
  have h2 : ((n + 1 : ℕ) : ℝ) + 1 ≤ 2 * ((n : ℝ) + 1) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h3 : ((n + 1 : ℕ) : ℝ) + 1 ≥ 0 := by positivity
  have h4 : (((n + 1 : ℕ) : ℝ) + 1) ^ m ≤ (2 * ((n : ℝ) + 1)) ^ m := pow_le_pow_left₀ h3 h2 m
  have h5 : |b (n + 1)| ≤ B * (2 ^ m * ((n : ℝ) + 1) ^ m) := by
    refine h1.trans ?_
    rw [← mul_pow]
    exact mul_le_mul_of_nonneg_left h4 hB
  calc |D b n| = ((n : ℝ) + 1) * |b (n + 1)| := by
        simp only [D, abs_mul]; rw [abs_of_nonneg (by positivity)]
    _ ≤ ((n : ℝ) + 1) * (B * (2 ^ m * ((n : ℝ) + 1) ^ m)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = _ := by ring

lemma abs_lt_one_of_mem {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : |x| < 1 := abs_lt.2 ⟨hx.1, hx.2⟩

lemma deriv_P {b : ℕ → ℝ} {B : ℝ} {m : ℕ} (hB : 0 ≤ B) (hb : ∀ n, |b n| ≤ B * ((n : ℝ) + 1) ^ m)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : deriv (P b) x = P (D b) x :=
  (hasDerivAt_P b B hB m hb (abs_lt_one_of_mem hx)).deriv

/-- smoothness of polynomially bounded power series on `(-1,1)`. -/
theorem contDiffOn_P : ∀ (N : ℕ) (b : ℕ → ℝ) (B : ℝ) (m : ℕ), 0 ≤ B →
    (∀ n, |b n| ≤ B * ((n : ℝ) + 1) ^ m) → ContDiffOn ℝ (N : WithTop ℕ∞) (P b) (Ioo (-1 : ℝ) 1) := by
  intro N
  induction N with
  | zero =>
    intro b B m hB hb
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hasDerivAt_P b B hB m hb (abs_lt_one_of_mem hx)).continuousAt.continuousWithinAt
  | succ N ih =>
    intro b B m hB hb
    rw [Nat.cast_succ, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun x hx => (hasDerivAt_P b B hB m hb (abs_lt_one_of_mem hx)).differentiableAt.differentiableWithinAt,
      fun h => absurd h (by simp), ?_⟩
    have := ih (D b) (B * 2 ^ m) (m + 1) (by positivity) (D_bound hb hB)
    exact this.congr fun x hx => deriv_P hB hb hx


theorem summable_P {b : ℕ → ℝ} {B : ℝ} {m : ℕ} (hB : 0 ≤ B) (hb : ∀ n, |b n| ≤ B * ((n : ℝ) + 1) ^ m)
    {x : ℝ} (hx : |x| < 1) : Summable (fun n : ℕ => b n * x ^ n) := by
  set r : ℝ := (|x| + 1) / 2 with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr]; linarith
  have hxr : |x| ≤ r := by rw [hr]; linarith
  have h1 : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * r ^ n) := by
    have := (summable_nat_add_iff 1).2 (summable_pow_mul_geom m hr0.le hr1)
    have h2 := this.div_const r
    refine h2.congr fun n => ?_
    push_cast
    field_simp
    ring
  refine Summable.of_norm_bounded (h1.mul_left B) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  calc |b n| * |x| ^ n ≤ (B * ((n : ℝ) + 1) ^ m) * r ^ n :=
        mul_le_mul (hb n) (pow_le_pow_left₀ (abs_nonneg _) hxr n) (by positivity) (by positivity)
    _ = _ := by ring

/-- the coefficients of the solution of `(1-x²) w'' - 4 x w' = w`, `w(0) = 1`, `w'(0) = 0`. -/
noncomputable def aa : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | (n + 2) => aa n * (1 - 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2)))

lemma aa_zero : aa 0 = 1 := rfl
lemma aa_one : aa 1 = 0 := rfl
lemma aa_add_two (n : ℕ) : aa (n + 2) = aa n * (1 - 1 / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := rfl

lemma aa_rec (n : ℕ) : ((n : ℝ) + 1) * ((n : ℝ) + 2) * aa (n + 2) = ((n : ℝ) ^ 2 + 3 * n + 1) * aa n := by
  rw [aa_add_two]
  have : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

lemma aa_bounds : ∀ n, 0 ≤ aa n ∧ aa n ≤ 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [aa_zero]
    | 1, _ => simp [aa_one]
    | (k + 2), ih =>
      obtain ⟨h0, h1⟩ := ih k (by omega)
      rw [aa_add_two]
      have hp : (0 : ℝ) < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
      have hq : 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) ≤ 1 := by
        rw [div_le_one hp]; nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have hq0 : 0 ≤ 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2)) := by positivity
      constructor
      · exact mul_nonneg h0 (by linarith)
      · calc aa k * (1 - 1 / (((k : ℝ) + 1) * ((k : ℝ) + 2))) ≤ 1 * 1 :=
              mul_le_mul h1 (by linarith) (by linarith) zero_le_one
          _ = 1 := one_mul 1

lemma abs_aa_le (n : ℕ) : |aa n| ≤ 1 * ((n : ℝ) + 1) ^ 0 := by
  rw [pow_zero, mul_one, abs_of_nonneg (aa_bounds n).1]; exact (aa_bounds n).2

lemma abs_Daa_le (n : ℕ) : |D aa n| ≤ 1 * ((n : ℝ) + 1) ^ 1 := by
  have := D_bound (B := 1) (m := 0) abs_aa_le zero_le_one n
  simpa using this

lemma abs_DDaa_le (n : ℕ) : |D (D aa) n| ≤ 2 * ((n : ℝ) + 1) ^ 2 := by
  have := D_bound (B := 1) (m := 1) abs_Daa_le zero_le_one n
  simpa using this

lemma tsum_two {f : ℕ → ℝ} (hf : Summable f) : ∑' n, f n = f 0 + f 1 + ∑' n, f (n + 2) := by
  rw [hf.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hf).tsum_eq_zero_add]
  ring


/-- the ODE for the series: `(1-x²) w'' - 4 x w' - w = 0` with `w = P aa`, `w' = P (D aa)`, `w'' = P (D (D aa))`. -/
theorem ode_series {x : ℝ} (hx : |x| < 1) :
    (1 - x ^ 2) * P (D (D aa)) x - 4 * x * P (D aa) x - P aa x = 0 := by
  have hA : Summable (fun n : ℕ => aa n * x ^ n) := summable_P (B := 1) (m := 0) zero_le_one abs_aa_le hx
  have hF : Summable (fun n : ℕ => D aa n * x ^ n) := summable_P (B := 1) (m := 1) zero_le_one abs_Daa_le hx
  have hE : Summable (fun n : ℕ => D (D aa) n * x ^ n) := summable_P (B := 2) (m := 2) (by norm_num) abs_DDaa_le hx
  have hA2 : Summable (fun n : ℕ => aa (n + 2) * x ^ (n + 2)) := (summable_nat_add_iff 2 (f := fun n : ℕ => aa n * x ^ n)).2 hA
  have hE2 : Summable (fun n : ℕ => D (D aa) (n + 2) * x ^ (n + 2)) := (summable_nat_add_iff 2 (f := fun n : ℕ => D (D aa) n * x ^ n)).2 hE
  have hF1 : Summable (fun n : ℕ => D aa (n + 1) * x ^ (n + 1)) := (summable_nat_add_iff 1 (f := fun n : ℕ => D aa n * x ^ n)).2 hF
  have hEs : Summable (fun n : ℕ => D (D aa) n * x ^ (n + 2)) := by
    refine (hE.mul_left (x ^ 2)).congr fun n => ?_
    ring
  have hFs : Summable (fun n : ℕ => D aa (n + 1) * x ^ (n + 2)) := by
    refine (hF1.mul_left x).congr fun n => ?_
    ring
  have e1 : P (D (D aa)) x = D (D aa) 0 + D (D aa) 1 * x + ∑' n, D (D aa) (n + 2) * x ^ (n + 2) := by
    have := tsum_two hE
    simpa [P] using this
  have e2 : P aa x = aa 0 + aa 1 * x + ∑' n, aa (n + 2) * x ^ (n + 2) := by
    have := tsum_two hA
    simpa [P] using this
  have e3 : x * P (D aa) x = D aa 0 * x + ∑' n, D aa (n + 1) * x ^ (n + 2) := by
    have hg : Summable (fun n : ℕ => D aa n * x ^ (n + 1)) := by
      refine (hF.mul_left x).congr fun n => ?_
      ring
    have := hg.tsum_eq_zero_add
    have h1 : ∑' n, D aa n * x ^ (n + 1) = x * P (D aa) x := by
      rw [P, ← tsum_mul_left]
      exact tsum_congr fun n => by ring
    rw [← h1, this]
    simp
  have e4 : x ^ 2 * P (D (D aa)) x = ∑' n, D (D aa) n * x ^ (n + 2) := by
    rw [P, ← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have hz : ∀ n : ℕ, D (D aa) (n + 2) - D (D aa) n - 4 * D aa (n + 1) - aa (n + 2) = 0 := by
    intro n
    have h1 := aa_rec n
    have h2 := aa_rec (n + 2)
    simp only [D]
    push_cast at h2 ⊢
    nlinarith [h1, h2]
  have hsum : ∑' n, D (D aa) (n + 2) * x ^ (n + 2) - ∑' n, D (D aa) n * x ^ (n + 2) -
      4 * ∑' n, D aa (n + 1) * x ^ (n + 2) - ∑' n, aa (n + 2) * x ^ (n + 2) = 0 := by
    have hFs4 : Summable (fun n : ℕ => 4 * (D aa (n + 1) * x ^ (n + 2))) := hFs.mul_left 4
    have t1 := hE2.tsum_sub hEs
    have t2 := (hE2.sub hEs).tsum_sub hFs4
    have t3 := ((hE2.sub hEs).sub hFs4).tsum_sub hA2
    have t4 : ∑' n : ℕ, 4 * (D aa (n + 1) * x ^ (n + 2)) = 4 * ∑' n, D aa (n + 1) * x ^ (n + 2) :=
      tsum_mul_left
    have hz0 : ∀ n : ℕ, D (D aa) (n + 2) * x ^ (n + 2) - D (D aa) n * x ^ (n + 2) -
        4 * (D aa (n + 1) * x ^ (n + 2)) - aa (n + 2) * x ^ (n + 2) = 0 := fun n => by
      have := hz n
      linear_combination x ^ (n + 2) * this
    have t5 : ∑' n : ℕ, (D (D aa) (n + 2) * x ^ (n + 2) - D (D aa) n * x ^ (n + 2) -
        4 * (D aa (n + 1) * x ^ (n + 2)) - aa (n + 2) * x ^ (n + 2)) = 0 := by
      simp [hz0]
    linarith [t1, t2, t3, t4, t5]
  have c0 : D (D aa) 0 - aa 0 = 0 := by
    simp only [D, aa_zero]
    have := aa_rec 0
    rw [aa_zero] at this
    push_cast at this ⊢
    nlinarith [this]
  have c1 : D (D aa) 1 - 4 * D aa 0 - aa 1 = 0 := by
    simp only [D, aa_one]
    have h3 : aa 3 = 0 := by
      have := aa_add_two 1
      simpa [aa_one] using this
    norm_num [h3, aa_one]
  linear_combination e1 - e4 - 4 * e3 - e2 + c0 + x * c1 + hsum

end MarkovTriple.BGL.Instances.GegenbauerOpen.R24
