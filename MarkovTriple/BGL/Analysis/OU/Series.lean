import MarkovTriple.BGL.Analysis.OU.Bound

/-! # OU (Part 13): Hermite series, smoothness and termwise differentiation -/

open MeasureTheory Filter Topology Polynomial Set
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

/-- derivatives of the normalised Hermite function (through the polynomial) -/
noncomputable def dh (n k : ℕ) : ℝ → ℝ :=
  fun x => (√(n.factorial : ℝ))⁻¹ * (derivative^[k] (He n)).eval x

lemma dh_zero (n : ℕ) : dh n 0 = hh n := by funext x; simp [dh, hh]

lemma hasDerivAt_dh (n k : ℕ) (x : ℝ) : HasDerivAt (dh n k) (dh n (k + 1) x) x := by
  have := ((derivative^[k] (He n)).hasDerivAt x).const_mul ((√(n.factorial : ℝ))⁻¹)
  simp only [dh, Function.iterate_succ_apply']
  exact this

lemma dh_succ_succ (m k : ℕ) (x : ℝ) : dh (m + 1) (k + 1) x = √((m : ℝ) + 1) * dh m k x := by
  simp only [dh, Function.iterate_succ_apply, derivative_He, iterate_derivative_C_mul, eval_mul, eval_C]
  rw [factorial_succ_real, Real.sqrt_mul (by positivity)]
  have hp : 0 < √((m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hq : 0 < √(m.factorial : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos m)
  have hs : √((m : ℝ) + 1) * √((m : ℝ) + 1) = (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  generalize √((m : ℝ) + 1) = s at hp hs ⊢
  rw [← hs]
  field_simp

lemma dh_zero_succ (k : ℕ) (x : ℝ) : dh 0 (k + 1) x = 0 := by
  simp [dh, Function.iterate_succ_apply, He_zero]

lemma abs_hh_le (n : ℕ) (x : ℝ) : |hh n x| ≤ 2 * Real.exp (x ^ 2 / 2) := by
  have h := hh_sq_le n x
  have e : (2 * Real.exp (x ^ 2 / 2)) ^ 2 = 4 * Real.exp (x ^ 2) := by
    rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have : hh n x ^ 2 ≤ (2 * Real.exp (x ^ 2 / 2)) ^ 2 := by
    rw [e]; nlinarith [Real.exp_pos (x ^ 2)]
  exact abs_le_of_sq_le_sq' this (by positivity) |> fun h => abs_le.2 h

theorem abs_dh_le (k : ℕ) : ∀ (n : ℕ) (x : ℝ),
    |dh n k x| ≤ ((n : ℝ) + 1) ^ k * (2 * Real.exp (x ^ 2 / 2)) := by
  induction k with
  | zero => intro n x; rw [dh_zero]; simpa using abs_hh_le n x
  | succ k ih =>
    intro n x
    rcases n with _ | m
    · rw [dh_zero_succ]; simp; positivity
    · rw [dh_succ_succ, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      have h1 := ih m x
      have h2 : √((m : ℝ) + 1) ≤ ((m + 1 : ℕ) : ℝ) + 1 := by
        push_cast
        have : √((m : ℝ) + 1) ≤ (m : ℝ) + 1 := by
          have h0 : (1 : ℝ) ≤ (m : ℝ) + 1 := by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
          calc √((m : ℝ) + 1) ≤ √(((m : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
            _ = (m : ℝ) + 1 := Real.sqrt_sq (by linarith)
        linarith
      have h3 : ((m : ℝ) + 1) ^ k ≤ (((m + 1 : ℕ) : ℝ) + 1) ^ k := by
        apply pow_le_pow_left₀ (by positivity); push_cast; linarith
      calc √((m : ℝ) + 1) * |dh m k x| ≤ (((m + 1 : ℕ) : ℝ) + 1) *
            (((m : ℝ) + 1) ^ k * (2 * Real.exp (x ^ 2 / 2))) :=
            mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
        _ ≤ (((m + 1 : ℕ) : ℝ) + 1) * ((((m + 1 : ℕ) : ℝ) + 1) ^ k * (2 * Real.exp (x ^ 2 / 2))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (by positivity)) (by positivity)
        _ = _ := by ring

/-- coefficient sequences with all polynomial moments summable -/
def Good (a : ℕ → ℝ) : Prop := ∀ m : ℕ, Summable (fun n : ℕ => ((n : ℝ) + 1) ^ m * |a n|)

/-- the `k`-th termwise derivative of the Hermite series -/
noncomputable def Tser (a : ℕ → ℝ) (k : ℕ) : ℝ → ℝ := fun x => ∑' n, a n * dh n k x

lemma summable_Tser {a : ℕ → ℝ} (ha : Good a) (k : ℕ) (x : ℝ) :
    Summable (fun n => a n * dh n k x) := by
  refine Summable.of_norm_bounded ((ha k).mul_right (2 * Real.exp (x ^ 2 / 2))) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul]
  calc |a n| * |dh n k x| ≤ |a n| * (((n : ℝ) + 1) ^ k * (2 * Real.exp (x ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_left (abs_dh_le k n x) (abs_nonneg _)
    _ = _ := by ring

lemma hasDerivAt_Tser {a : ℕ → ℝ} (ha : Good a) (k : ℕ) (x : ℝ) :
    HasDerivAt (Tser a k) (Tser a (k + 1) x) x := by
  set R : ℝ := |x| + 1 with hR
  have hRpos : 0 < R := by positivity
  refine hasDerivAt_tsum_of_isPreconnected (g := fun (n : ℕ) (z : ℝ) => a n * dh n k z)
    (g' := fun (n : ℕ) (z : ℝ) => a n * dh n (k + 1) z)
    (u := fun (n : ℕ) => ((n : ℝ) + 1) ^ (k + 1) * |a n| *
      (2 * Real.exp (R ^ 2 / 2))) (t := Metric.ball (0 : ℝ) R) (y₀ := x)
    ((ha (k + 1)).mul_right _) Metric.isOpen_ball (convex_ball (0 : ℝ) R).isPreconnected
    (fun n y _ => (hasDerivAt_dh n k y).const_mul (a n)) (fun n y hy => ?_)
    (by simp [hR, Metric.mem_ball]) (summable_Tser ha k x) (by simp [hR, Metric.mem_ball])
  rw [Real.norm_eq_abs, abs_mul]
  have hy' : |y| < R := by simpa [Metric.mem_ball] using hy
  have hexp : Real.exp (y ^ 2 / 2) ≤ Real.exp (R ^ 2 / 2) := by
    apply Real.exp_le_exp.2
    have : y ^ 2 ≤ R ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    linarith
  calc |a n| * |dh n (k + 1) y| ≤ |a n| * (((n : ℝ) + 1) ^ (k + 1) * (2 * Real.exp (y ^ 2 / 2))) :=
        mul_le_mul_of_nonneg_left (abs_dh_le (k + 1) n y) (abs_nonneg _)
    _ ≤ |a n| * (((n : ℝ) + 1) ^ (k + 1) * (2 * Real.exp (R ^ 2 / 2))) := by
        gcongr
    _ = _ := by ring

lemma deriv_Tser {a : ℕ → ℝ} (ha : Good a) (k : ℕ) : deriv (Tser a k) = Tser a (k + 1) :=
  funext fun x => (hasDerivAt_Tser ha k x).deriv

lemma Tser_contDiff {a : ℕ → ℝ} (ha : Good a) : ∀ m : ℕ, ∀ k, ContDiff ℝ m (Tser a k) := by
  intro m
  induction m with
  | zero =>
    intro k
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x => (hasDerivAt_Tser ha k x).continuousAt)
  | succ m ih =>
    intro k
    rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_deriv]
    refine ⟨fun x => (hasDerivAt_Tser ha k x).differentiableAt, by simp, ?_⟩
    rw [deriv_Tser ha k]
    exact ih (k + 1)

lemma Tser_sm {a : ℕ → ℝ} (ha : Good a) (k : ℕ) : Sm (Tser a k) :=
  contDiff_infty.2 fun m => Tser_contDiff ha m k

lemma Good.neg_mul_nat {a : ℕ → ℝ} (ha : Good a) : Good (fun n => -(n : ℝ) * a n) := by
  intro m
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) (ha (m + 1))
  rw [abs_mul, abs_neg, Nat.abs_cast, pow_succ]
  have : (n : ℝ) ≤ (n : ℝ) + 1 := by linarith
  calc ((n : ℝ) + 1) ^ m * ((n : ℝ) * |a n|) = (((n : ℝ) + 1) ^ m * (n : ℝ)) * |a n| := by ring
    _ ≤ (((n : ℝ) + 1) ^ m * ((n : ℝ) + 1)) * |a n| := by gcongr
    _ = _ := by ring

lemma Lo_Tser {a : ℕ → ℝ} (ha : Good a) :
    Lo (Tser a 0) = Tser (fun n => -(n : ℝ) * a n) 0 := by
  funext x
  have h1 : deriv (Tser a 0) = Tser a 1 := deriv_Tser ha 0
  have h2 : deriv (Tser a 1) = Tser a 2 := deriv_Tser ha 1
  simp only [Lo, h1]
  rw [show deriv (Tser a 1) x = Tser a 2 x from congrFun h2 x]
  simp only [Tser]
  rw [← tsum_mul_left, ← Summable.tsum_sub (summable_Tser ha 2 x)
    ((summable_Tser ha 1 x).mul_left x)]
  refine tsum_congr fun n => ?_
  have hd1 : deriv (hh n) = dh n 1 := by
    funext y; rw [← dh_zero]; exact (hasDerivAt_dh n 0 y).deriv
  have hd2 : deriv (dh n 1) = dh n 2 := by
    funext y; exact (hasDerivAt_dh n 1 y).deriv
  have := congrFun (Lo_hh n) x
  simp only [Lo, hd1, hd2] at this
  simp only [dh_zero]
  have e : a n * dh n 2 x - x * (a n * dh n 1 x) = a n * (dh n 2 x - x * dh n 1 x) := by ring
  rw [e, this]; ring

end MarkovTriple.Sanity.OU
