import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R24.GoSeries

/-!
# R32-Z: the power series `A = Σ cc_n xⁿ` solving `(1-x²)A'' + 2xA' + 3A = 0` (helper for `lam = 5/2`)

`cc_0 = 1, cc_1 = 0, cc_{n+2} = cc_n (n²-3n-3)/((n+1)(n+2))`.  `|cc_n| ≲ n^{-5/2}` (via squares),
hence the Lipschitz estimate `|A(x) - A(1)| ≤ C (1-x²)`.  See `STATEMENTS_R32_Z.md`.
-/

open Filter Topology Set
open MarkovTriple.BGL.Instances.GegenbauerOpen.R24

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Z

/-- coefficients of `A`. -/
noncomputable def cc : ℕ → ℝ
  | 0 => 1
  | 1 => 0
  | (n + 2) => cc n * (((n : ℝ) ^ 2 - 3 * n - 3) / (((n : ℝ) + 1) * ((n : ℝ) + 2)))

lemma cc_zero : cc 0 = 1 := rfl
lemma cc_one : cc 1 = 0 := rfl
lemma cc_add_two (n : ℕ) :
    cc (n + 2) = cc n * (((n : ℝ) ^ 2 - 3 * n - 3) / (((n : ℝ) + 1) * ((n : ℝ) + 2))) := rfl

lemma cc_rec (n : ℕ) :
    ((n : ℝ) + 1) * ((n : ℝ) + 2) * cc (n + 2) = ((n : ℝ) ^ 2 - 3 * n - 3) * cc n := by
  rw [cc_add_two]
  have : ((n : ℝ) + 1) * ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp

lemma cc_two : cc 2 = -(3 / 2) := by
  rw [cc_add_two]; simp [cc_zero]; norm_num

lemma cc_three : cc 3 = 0 := by
  have := cc_add_two 1
  simpa [cc_one] using this

lemma abs_cc_le : ∀ n, |cc n| ≤ 3 / 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => simp [cc_zero]; norm_num
    | 1, _ => simp [cc_one]; norm_num
    | (k + 2), ih =>
      by_cases hk0 : k = 0
      · subst hk0
        simp [cc_two]; norm_num [abs_of_pos]
      · have h := ih k (by omega)
        rw [cc_add_two, abs_mul]
        have hp : (0 : ℝ) < ((k : ℝ) + 1) * ((k : ℝ) + 2) := by positivity
        have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hk0
        have hq : |((k : ℝ) ^ 2 - 3 * k - 3) / (((k : ℝ) + 1) * ((k : ℝ) + 2))| ≤ 1 := by
          rw [abs_div, abs_of_pos hp, div_le_one hp, abs_le]
          constructor <;> nlinarith
        calc |cc k| * _ ≤ (3 / 2) * 1 := mul_le_mul h hq (abs_nonneg _) (by norm_num)
          _ = 3 / 2 := mul_one _

lemma abs_cc_le' (n : ℕ) : |cc n| ≤ 2 * ((n : ℝ) + 1) ^ 0 := by
  have := abs_cc_le n
  simp only [pow_zero, mul_one]; linarith

lemma abs_Dcc_le (n : ℕ) : |D cc n| ≤ 2 * ((n : ℝ) + 1) ^ 1 := by
  have := D_bound (B := 2) (m := 0) abs_cc_le' (by norm_num) n
  simpa using this

lemma abs_DDcc_le (n : ℕ) : |D (D cc) n| ≤ 4 * ((n : ℝ) + 1) ^ 2 := by
  have := D_bound (B := 2) (m := 1) abs_Dcc_le (by norm_num) n
  norm_num at this
  linarith

lemma cc_odd : ∀ k : ℕ, cc (2 * k + 1) = 0 := by
  intro k
  induction k with
  | zero => simp [cc_one]
  | succ k ih =>
    have : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by ring
    rw [this, cc_add_two, ih, zero_mul]

/-- one step of the decay: `cc_{n+2}² (n+3)⁵ ≤ cc_n² (n+1)⁵` for `n ≥ 3`. -/
lemma cc_decay {n : ℕ} (hn : 3 ≤ n) :
    cc (n + 2) ^ 2 * ((n : ℝ) + 3) ^ 5 ≤ cc n ^ 2 * ((n : ℝ) + 1) ^ 5 := by
  rw [cc_add_two]
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  generalize (n : ℝ) = y at hn' ⊢
  obtain ⟨m, rfl⟩ : ∃ m : ℝ, y = m + 3 := ⟨y - 3, by ring⟩
  have hm : 0 ≤ m := by linarith
  have hp : (0 : ℝ) < ((m + 3 + 1) * (m + 3 + 2)) ^ 2 := by positivity
  have key : ((m + 3) ^ 2 - 3 * (m + 3) - 3) ^ 2 * (m + 3 + 3) ^ 5 ≤
      ((m + 3 + 1) * (m + 3 + 2)) ^ 2 * (m + 3 + 1) ^ 5 := by
    nlinarith [pow_nonneg hm 2, pow_nonneg hm 3, pow_nonneg hm 4, pow_nonneg hm 5, pow_nonneg hm 6,
      pow_nonneg hm 7, pow_nonneg hm 8]
  have e : (cc n * (((m + 3) ^ 2 - 3 * (m + 3) - 3) / ((m + 3 + 1) * (m + 3 + 2)))) ^ 2 * (m + 3 + 3) ^ 5
      = cc n ^ 2 * ((((m + 3) ^ 2 - 3 * (m + 3) - 3) ^ 2 * (m + 3 + 3) ^ 5) /
        ((m + 3 + 1) * (m + 3 + 2)) ^ 2) := by
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  rw [div_le_iff₀ hp]
  linarith

lemma cc_four : cc 4 = 5 / 8 := by
  have := cc_add_two 2
  rw [cc_two] at this
  norm_num at this
  linarith

lemma cc_sq_bound : ∀ n : ℕ, cc n ^ 2 * ((n : ℝ) + 1) ^ 5 ≤ 1300 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases h4 : n < 5
    · interval_cases n
      · norm_num [cc_zero]
      · norm_num [cc_one]
      · norm_num [cc_two]
      · norm_num [cc_three]
      · norm_num [cc_four]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
      have h1 := cc_decay (n := m) (by omega)
      have h2 := ih m (by omega)
      push_cast
      have : ((m : ℝ) + 2 + 1) = (m : ℝ) + 3 := by ring
      rw [this]
      linarith

lemma abs_cc_le_inv (n : ℕ) :
    |cc n| ≤ 37 / (((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1)) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 hn
  have hss : Real.sqrt ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) = (n : ℝ) + 1 := Real.mul_self_sqrt hn.le
  rw [le_div_iff₀ (by positivity)]
  have h := cc_sq_bound n
  set X : ℝ := |cc n| * (((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1)) with hX
  have hX2 : X ^ 2 = cc n ^ 2 * ((n : ℝ) + 1) ^ 5 := by
    rw [hX, mul_pow, mul_pow, sq_abs, ← pow_mul, Real.sq_sqrt hn.le]
    ring
  have hX0 : 0 ≤ X := by positivity
  by_contra hc
  have hc := not_le.1 hc
  nlinarith

lemma n_abs_cc_le (n : ℕ) :
    (n : ℝ) * |cc n| ≤ 37 * ((((n + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2))⁻¹) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 hn
  have h3 : ((n : ℝ) + 1) ^ ((3 : ℝ) / 2) = ((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hn.le (by norm_num)]
    norm_num
  have h2 : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [h2, h3]
  have h := abs_cc_le_inv n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc (n : ℝ) * |cc n| ≤ (n : ℝ) * (37 / (((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left h hn0
    _ ≤ ((n : ℝ) + 1) * (37 / (((n : ℝ) + 1) ^ 2 * Real.sqrt ((n : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 37 * ((((n : ℝ) + 1) * Real.sqrt ((n : ℝ) + 1))⁻¹) := by
        field_simp

lemma summable_n_cc : Summable (fun n : ℕ => (n : ℝ) * |cc n|) := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _))
    n_abs_cc_le ?_
  have := (summable_nat_add_iff 1 (f := fun n : ℕ => ((n : ℝ) ^ ((3 : ℝ) / 2))⁻¹)).2
    (Real.summable_nat_rpow_inv.2 (by norm_num : (1 : ℝ) < 3 / 2))
  exact this.mul_left 37

lemma summable_abs_cc : Summable (fun n : ℕ => |cc n|) := by
  rw [← summable_nat_add_iff 1]
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_)
    ((summable_nat_add_iff 1).2 summable_n_cc)
  have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  exact le_mul_of_one_le_left (abs_nonneg _) h1

lemma summable_cc_mul {x : ℝ} (hx : |x| ≤ 1) : Summable (fun n : ℕ => cc n * x ^ n) := by
  refine Summable.of_norm_bounded summable_abs_cc fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact mul_le_of_le_one_right (abs_nonneg _) (pow_le_one₀ (abs_nonneg _) hx)

/-- `A(x) = Σ cc_n xⁿ`. -/
noncomputable def AA (x : ℝ) : ℝ := ∑' n, cc n * x ^ n

/-- `Λ = A(1) = Σ cc_n`. -/
noncomputable def Lam : ℝ := ∑' n, cc n

lemma AA_eq_P (x : ℝ) : AA x = P cc x := rfl

lemma abs_pow_sub_one_le {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    |cc n| * |x ^ n - 1| ≤ |cc n| * n * (1 - x ^ 2) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' n
  · subst hk
    set s : ℝ := 1 - x ^ 2 with hs
    have hs0 : 0 < s := by
      have : x ^ 2 < 1 := by rw [← sq_abs]; nlinarith [abs_nonneg x]
      linarith
    have hs1 : s ≤ 1 := by nlinarith [sq_nonneg x]
    have ht : x ^ (2 * k) = (1 - s) ^ k := by rw [pow_mul, hs]; ring_nf
    have hb := one_add_mul_le_pow (a := -s) (by linarith) k
    have hb3 : (1 - s) ^ k ≤ 1 := pow_le_one₀ (by nlinarith [sq_nonneg x]) (by linarith)
    have hy : |x ^ (2 * k) - 1| ≤ (2 * k : ℕ) * s := by
      rw [ht, abs_of_nonpos (by linarith)]
      push_cast
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have : 1 + (k : ℝ) * -s ≤ (1 - s) ^ k := hb
      nlinarith [mul_nonneg hk0 hs0.le]
    calc |cc (2 * k)| * |x ^ (2 * k) - 1| ≤ |cc (2 * k)| * ((2 * k : ℕ) * s) :=
          mul_le_mul_of_nonneg_left hy (abs_nonneg _)
      _ = _ := by ring
  · subst hk
    rw [cc_odd]
    simp

/-- `C₁ = Σ n |cc_n|`. -/
noncomputable def C1 : ℝ := ∑' n : ℕ, (n : ℝ) * |cc n|

lemma C1_nonneg : 0 ≤ C1 := tsum_nonneg fun n => mul_nonneg (Nat.cast_nonneg n) (abs_nonneg _)

/-- Lipschitz estimate `|A(x) - Λ| ≤ C₁ (1-x²)`. -/
theorem lipschitz {x : ℝ} (hx : |x| < 1) : |AA x - Lam| ≤ C1 * (1 - x ^ 2) := by
  have h1 := summable_cc_mul hx.le
  have h2 : Summable cc := summable_abs_cc.of_abs
  have e : AA x - Lam = ∑' n, (cc n * x ^ n - cc n) := by
    rw [AA, Lam, ← h1.tsum_sub h2]
  rw [e]
  have hg : HasSum (fun n : ℕ => (n : ℝ) * |cc n| * (1 - x ^ 2)) (C1 * (1 - x ^ 2)) :=
    summable_n_cc.hasSum.mul_right _
  have := tsum_of_norm_bounded hg (f := fun n : ℕ => cc n * x ^ n - cc n) (fun n => by
    rw [Real.norm_eq_abs]
    calc |cc n * x ^ n - cc n| = |cc n * (x ^ n - 1)| := by ring_nf
      _ ≤ _ := by
        rw [abs_mul]
        calc _ ≤ |cc n| * n * (1 - x ^ 2) := abs_pow_sub_one_le hx n
          _ = _ := by ring)
  simpa [Real.norm_eq_abs] using this

/-! ### the ODE for the series -/

lemma tsum_two' {f : ℕ → ℝ} (hf : Summable f) : ∑' n, f n = f 0 + f 1 + ∑' n, f (n + 2) := by
  rw [hf.tsum_eq_zero_add, ((summable_nat_add_iff 1).2 hf).tsum_eq_zero_add]
  ring

/-- `(1-x²) A'' + 2x A' + 3 A = 0` for the series (`A = P cc`, `A' = P (D cc)`, `A'' = P (D (D cc))`). -/
theorem ode_series_cc {x : ℝ} (hx : |x| < 1) :
    (1 - x ^ 2) * P (D (D cc)) x + 2 * (x * P (D cc) x) + 3 * P cc x = 0 := by
  have hA : Summable (fun n : ℕ => cc n * x ^ n) := summable_P (B := 2) (m := 0) (by norm_num) abs_cc_le' hx
  have hF : Summable (fun n : ℕ => D cc n * x ^ n) := summable_P (B := 2) (m := 1) (by norm_num) abs_Dcc_le hx
  have hE : Summable (fun n : ℕ => D (D cc) n * x ^ n) :=
    summable_P (B := 4) (m := 2) (by norm_num) abs_DDcc_le hx
  have hA2 : Summable (fun n : ℕ => cc (n + 2) * x ^ (n + 2)) :=
    (summable_nat_add_iff 2 (f := fun n : ℕ => cc n * x ^ n)).2 hA
  have hE2 : Summable (fun n : ℕ => D (D cc) (n + 2) * x ^ (n + 2)) :=
    (summable_nat_add_iff 2 (f := fun n : ℕ => D (D cc) n * x ^ n)).2 hE
  have hF1 : Summable (fun n : ℕ => D cc (n + 1) * x ^ (n + 1)) :=
    (summable_nat_add_iff 1 (f := fun n : ℕ => D cc n * x ^ n)).2 hF
  have hEs : Summable (fun n : ℕ => D (D cc) n * x ^ (n + 2)) := by
    refine (hE.mul_left (x ^ 2)).congr fun n => ?_
    ring
  have hFs : Summable (fun n : ℕ => D cc (n + 1) * x ^ (n + 2)) := by
    refine (hF1.mul_left x).congr fun n => ?_
    ring
  have e1 : P (D (D cc)) x = D (D cc) 0 + D (D cc) 1 * x + ∑' n, D (D cc) (n + 2) * x ^ (n + 2) := by
    have := tsum_two' hE
    simpa [P] using this
  have e2 : P cc x = cc 0 + cc 1 * x + ∑' n, cc (n + 2) * x ^ (n + 2) := by
    have := tsum_two' hA
    simpa [P] using this
  have e3 : x * P (D cc) x = D cc 0 * x + ∑' n, D cc (n + 1) * x ^ (n + 2) := by
    have hg : Summable (fun n : ℕ => D cc n * x ^ (n + 1)) := by
      refine (hF.mul_left x).congr fun n => ?_
      ring
    have := hg.tsum_eq_zero_add
    have h1 : ∑' n, D cc n * x ^ (n + 1) = x * P (D cc) x := by
      rw [P, ← tsum_mul_left]
      exact tsum_congr fun n => by ring
    rw [← h1, this]
    simp
  have e4 : x ^ 2 * P (D (D cc)) x = ∑' n, D (D cc) n * x ^ (n + 2) := by
    rw [P, ← tsum_mul_left]
    exact tsum_congr fun n => by ring
  have hz : ∀ n : ℕ, D (D cc) (n + 2) - D (D cc) n + 2 * D cc (n + 1) + 3 * cc (n + 2) = 0 := by
    intro n
    have h1 := cc_rec (n + 2)
    simp only [D]
    push_cast at h1 ⊢
    nlinarith [h1]
  have hsum : ∑' n, D (D cc) (n + 2) * x ^ (n + 2) - ∑' n, D (D cc) n * x ^ (n + 2) +
      2 * ∑' n, D cc (n + 1) * x ^ (n + 2) + 3 * ∑' n, cc (n + 2) * x ^ (n + 2) = 0 := by
    have hA2' : Summable (fun n : ℕ => 3 * (cc (n + 2) * x ^ (n + 2))) := hA2.mul_left 3
    have hFs' : Summable (fun n : ℕ => 2 * (D cc (n + 1) * x ^ (n + 2))) := hFs.mul_left 2
    have t1 := hE2.tsum_sub hEs
    have t2 := (hE2.sub hEs).tsum_add hFs'
    have t3 := ((hE2.sub hEs).add hFs').tsum_add hA2'
    have t4 : ∑' n : ℕ, 3 * (cc (n + 2) * x ^ (n + 2)) = 3 * ∑' n, cc (n + 2) * x ^ (n + 2) :=
      tsum_mul_left
    have t4' : ∑' n : ℕ, 2 * (D cc (n + 1) * x ^ (n + 2)) = 2 * ∑' n, D cc (n + 1) * x ^ (n + 2) :=
      tsum_mul_left
    have hz0 : ∀ n : ℕ, D (D cc) (n + 2) * x ^ (n + 2) - D (D cc) n * x ^ (n + 2) +
        2 * (D cc (n + 1) * x ^ (n + 2)) + 3 * (cc (n + 2) * x ^ (n + 2)) = 0 := fun n => by
      have := hz n
      linear_combination x ^ (n + 2) * this
    have t5 : ∑' n : ℕ, (D (D cc) (n + 2) * x ^ (n + 2) - D (D cc) n * x ^ (n + 2) +
        2 * (D cc (n + 1) * x ^ (n + 2)) + 3 * (cc (n + 2) * x ^ (n + 2))) = 0 := by
      simp [hz0]
    linarith [t1, t2, t3, t4, t4', t5]
  have c0 : D (D cc) 0 + 3 * cc 0 = 0 := by
    simp only [D, cc_zero]
    have := cc_rec 0
    rw [cc_zero] at this
    push_cast at this ⊢
    nlinarith [this]
  have c1 : D (D cc) 1 + 2 * D cc 0 + 3 * cc 1 = 0 := by
    simp only [D, cc_one]
    have h3 : cc 3 = 0 := cc_three
    norm_num [h3, cc_one]
  linear_combination e1 - e4 + 2 * e3 + 3 * e2 + c0 + x * c1 + hsum

end MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Z
