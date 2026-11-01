import MarkovTriple.Sanity.OU.Energy

/-! # OU (Part 12): pointwise bounds on normalised Hermite functions and their derivatives -/

open MeasureTheory Filter Topology Polynomial Set
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

lemma factorial_succ_real (m : ℕ) : (((m + 1).factorial : ℕ) : ℝ) = ((m : ℝ) + 1) * (m.factorial : ℝ) := by
  push_cast [Nat.factorial_succ]; ring

lemma hh_succ_deriv (m : ℕ) (x : ℝ) : deriv (hh (m + 1)) x = √((m : ℝ) + 1) * hh m x := by
  have e : hh (m + 1) = fun x => (√(((m + 1).factorial : ℕ) : ℝ))⁻¹ * (He (m + 1)).eval x := rfl
  have h1 : HasDerivAt (hh (m + 1)) ((√(((m + 1).factorial : ℕ) : ℝ))⁻¹ * (derivative (He (m + 1))).eval x) x := by
    rw [e]
    exact ((He (m + 1)).hasDerivAt x).const_mul _
  rw [h1.deriv, derivative_He]
  simp only [eval_mul, eval_C, hh]
  rw [factorial_succ_real, Real.sqrt_mul (by positivity)]
  have hp : 0 < √((m : ℝ) + 1) := Real.sqrt_pos.2 (by positivity)
  have hq : 0 < √(m.factorial : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos m)
  have hs : √((m : ℝ) + 1) * √((m : ℝ) + 1) = (m : ℝ) + 1 := Real.mul_self_sqrt (by positivity)
  generalize √((m : ℝ) + 1) = s at hp hs ⊢
  rw [← hs]
  field_simp

lemma hh_zero_deriv (x : ℝ) : deriv (hh 0) x = 0 := by
  rw [hh_zero]; simp

lemma hh_at_zero_sq (m : ℕ) : hh m 0 ^ 2 ≤ 1 ∧ hh (m + 1) 0 ^ 2 ≤ 1 := by
  induction m with
  | zero =>
    refine ⟨by simp [hh_zero], ?_⟩
    simp [hh, He_succ, He_zero]
  | succ m ih =>
    refine ⟨ih.2, ?_⟩
    have e : hh (m + 2) 0 = (√(((m + 2).factorial : ℕ) : ℝ))⁻¹ * (-((m : ℝ) + 1) * (He m).eval 0) := by
      simp only [hh]; rw [He_zero_val]
    have hf : (((m + 2).factorial : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) * (m.factorial : ℝ) := by
      rw [show m + 2 = (m + 1) + 1 from rfl, factorial_succ_real, factorial_succ_real]; push_cast; ring
    have hm : 0 < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    have e2 : hh (m + 2) 0 ^ 2 = ((m : ℝ) + 1) / ((m : ℝ) + 2) * hh m 0 ^ 2 := by
      rw [e]; simp only [hh]
      rw [mul_pow, mul_pow, mul_pow, inv_pow, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _),
        Real.sq_sqrt hm.le, neg_sq, hf]
      field_simp
    show hh (m + 1 + 1) 0 ^ 2 ≤ 1
    have := ih.1
    rw [show m + 1 + 1 = m + 2 from rfl, e2]
    have h3 : ((m : ℝ) + 1) / ((m : ℝ) + 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc ((m : ℝ) + 1) / ((m : ℝ) + 2) * hh m 0 ^ 2 ≤ 1 * 1 :=
          mul_le_mul h3 this (sq_nonneg _) (by norm_num)
      _ = 1 := by norm_num

lemma hh_abs_at_zero (m : ℕ) : hh m 0 ^ 2 ≤ 1 := (hh_at_zero_sq m).1

/-- **uniform pointwise bound**: `hh_n(x)² ≤ 2 e^{x²}` -/
theorem hh_sq_le (n : ℕ) (x : ℝ) : hh n x ^ 2 ≤ 2 * Real.exp (x ^ 2) := by
  rcases n with _ | m
  · rw [hh_zero]; simp; have := Real.add_one_le_exp (x ^ 2); nlinarith [sq_nonneg x]
  set y := hh (m + 1) with hy
  set n : ℝ := (m : ℝ) + 1 with hn
  have hnpos : 0 < n := by positivity
  have hysm : Sm y := hh_sm _
  have hz : ∀ x, deriv y x = √n * hh m x := fun x => hh_succ_deriv m x
  have hd1 : ∀ x, HasDerivAt y (deriv y x) x := fun x => hysm.hasDerivAt x
  have hd2 : ∀ x, HasDerivAt (deriv y) (deriv (deriv y) x) x := fun x => hysm.deriv'.hasDerivAt x
  have hlo : ∀ x, deriv (deriv y) x = x * deriv y x - n * y x := by
    intro x
    have := congrFun (Lo_hh (m + 1)) x
    simp only [Lo] at this
    push_cast at this
    simp only [hy, hn]
    linarith
  set E : ℝ → ℝ := fun x => n * y x ^ 2 + deriv y x ^ 2 with hE
  set G : ℝ → ℝ := fun x => E x * Real.exp (-(x ^ 2)) with hG
  have hEd : ∀ x, HasDerivAt E (2 * x * deriv y x ^ 2) x := by
    intro x
    have a1 := ((hd1 x).pow 2).const_mul n
    have a2 := (hd2 x).pow 2
    refine (a1.add a2).congr_deriv ?_
    simp only [Nat.cast_ofNat]
    rw [hlo x]; ring
  have hexp : ∀ x, HasDerivAt (fun x : ℝ => Real.exp (-(x ^ 2))) (Real.exp (-(x ^ 2)) * (-(2 * x))) x := by
    intro x
    have := ((hasDerivAt_pow 2 x).neg).exp
    simpa using this
  have hGd : ∀ x, HasDerivAt G (-(2 * n * x * y x ^ 2 * Real.exp (-(x ^ 2)))) x := by
    intro x
    refine ((hEd x).mul (hexp x)).congr_deriv ?_
    simp only [hE]; ring
  have hGle : ∀ x, G x ≤ G 0 := by
    intro x
    rcases le_total 0 x with hx | hx
    · have hanti : AntitoneOn G (Ici 0) := by
        refine antitoneOn_of_deriv_nonpos (convex_Ici 0) (fun x _ => (hGd x).continuousAt.continuousWithinAt)
          (fun x _ => (hGd x).differentiableAt.differentiableWithinAt) ?_
        intro x hx
        rw [interior_Ici] at hx
        rw [(hGd x).deriv]
        have : 0 < x := hx
        have := Real.exp_pos (-(x ^ 2))
        have := sq_nonneg (y x)
        nlinarith [mul_nonneg (mul_nonneg hnpos.le hx.le) (mul_nonneg (sq_nonneg (y x)) (Real.exp_pos (-(x ^ 2))).le)]
      exact hanti (mem_Ici.2 le_rfl) (mem_Ici.2 hx) hx
    · have hmono : MonotoneOn G (Iic 0) := by
        refine monotoneOn_of_deriv_nonneg (convex_Iic 0) (fun x _ => (hGd x).continuousAt.continuousWithinAt)
          (fun x _ => (hGd x).differentiableAt.differentiableWithinAt) ?_
        intro x hx
        rw [interior_Iic] at hx
        rw [(hGd x).deriv]
        have : x < 0 := hx
        nlinarith [mul_nonneg (mul_nonneg hnpos.le (neg_nonneg.2 this.le))
          (mul_nonneg (sq_nonneg (y x)) (Real.exp_pos (-(x ^ 2))).le)]
      exact hmono (mem_Iic.2 hx) (mem_Iic.2 le_rfl) hx
  have hE0 : E 0 ≤ 2 * n := by
    simp only [hE, hz]
    have h1 : hh m 0 ^ 2 ≤ 1 := hh_abs_at_zero m
    have h2 : hh (m + 1) 0 ^ 2 ≤ 1 := (hh_at_zero_sq m).2
    have : (√n * hh m 0) ^ 2 = n * hh m 0 ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hnpos.le]
    rw [this]
    have h3 : y 0 ^ 2 ≤ 1 := h2
    nlinarith
  have hEx : E x = G x * Real.exp (x ^ 2) := by
    simp only [hG]
    rw [mul_assoc, ← Real.exp_add]; simp
  have hnle : n * y x ^ 2 ≤ E x := by
    simp only [hE]; nlinarith [sq_nonneg (deriv y x)]
  have hfin : n * y x ^ 2 ≤ n * (2 * Real.exp (x ^ 2)) := by
    calc n * y x ^ 2 ≤ E x := hnle
      _ = G x * Real.exp (x ^ 2) := hEx
      _ ≤ G 0 * Real.exp (x ^ 2) := mul_le_mul_of_nonneg_right (hGle x) (Real.exp_pos _).le
      _ = E 0 * Real.exp (x ^ 2) := by simp [hG]
      _ ≤ (2 * n) * Real.exp (x ^ 2) := mul_le_mul_of_nonneg_right hE0 (Real.exp_pos _).le
      _ = n * (2 * Real.exp (x ^ 2)) := by ring
  exact le_of_mul_le_mul_left hfin hnpos

end MarkovTriple.Sanity.OU
