import MarkovTriple.BGL.Analysis.OU.Alg
import Mathlib.RingTheory.Polynomial.Hermite.Basic

/-! # OU (Part 4): polynomials, Hermite polynomials, orthogonality -/

open MeasureTheory Filter Topology ProbabilityTheory Polynomial
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

/-- the function of a polynomial -/
noncomputable abbrev pf (p : ℝ[X]) : ℝ → ℝ := fun x => p.eval x

lemma pf_sm (p : ℝ[X]) : Sm (pf p) := by
  have := Polynomial.contDiff_aeval (𝕜 := ℝ) p (⊤ : ℕ∞)
  simpa [pf, Polynomial.aeval_def] using this

lemma deriv_pf (p : ℝ[X]) : deriv (pf p) = pf (derivative p) := funext fun x => p.deriv

lemma pf_PG (p : ℝ[X]) : PG (pf p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have := hp.add hq
    have e : pf (p + q) = fun x => pf p x + pf q x := by funext x; simp [pf]
    rw [e]; exact this
  | monomial n c =>
    refine ⟨(pf_sm _).continuous, |c|, n, fun x => ?_⟩
    simp only [pf, eval_monomial, abs_mul, abs_pow]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    exact pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg x]) n

lemma Lo_pf (p : ℝ[X]) : Lo (pf p) = pf (derivative (derivative p) - X * derivative p) := by
  funext x
  simp [Lo, deriv_pf, pf, eval_sub, eval_mul]

lemma pf_add (p q : ℝ[X]) : pf (p + q) = fun x => pf p x + pf q x := by funext x; simp [pf]
lemma pf_mul (p q : ℝ[X]) : pf (p * q) = fun x => pf p x * pf q x := by funext x; simp [pf]

/-- generalized Gaussian IBP: `∫ F (G' − x G) dγ = −∫ F' G dγ` -/
theorem ibp_gen {F G : ℝ → ℝ} (hF : Sm F) (hG : Sm G)
    (h1 : Integrable (fun x => F x * (deriv G x - x * G x)) γ)
    (h2 : Integrable (fun x => deriv F x * G x) γ)
    (h3 : Integrable (fun x => F x * G x) γ) :
    ∫ x, F x * (deriv G x - x * G x) ∂γ = -∫ x, deriv F x * G x ∂γ := by
  have hv : ∀ x, HasDerivAt (fun x => G x * φ x) ((deriv G x - x * G x) * φ x) x := by
    intro x
    have := ((hG.hasDerivAt x).mul (φ_hasDerivAt x))
    convert this using 1
    ring
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := F) (v := fun x => G x * φ x) (u' := deriv F) (v' := fun x => (deriv G x - x * G x) * φ x)
    (fun x _ => hF.hasDerivAt x) (fun x _ => hv x)
    (by
      have := (integrable_γ_iff.1 h1)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      have := (integrable_γ_iff.1 h2)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
    (by
      have := (integrable_γ_iff.1 h3)
      refine this.congr (ae_of_all _ fun x => ?_)
      simp only [Pi.mul_apply]; ring)
  rw [integral_γ, integral_γ (F := fun x => deriv F x * G x)]
  have e1 : (fun x => φ x * (F x * (deriv G x - x * G x))) =
      fun x => F x * ((deriv G x - x * G x) * φ x) := by funext x; ring
  have e2 : (fun x => φ x * (deriv F x * G x)) = fun x => deriv F x * (G x * φ x) := by
    funext x; ring
  rw [e1, e2]
  exact key

/-- polynomial adjoint: `∫ p' q = ∫ p (x q − q')`. -/
theorem poly_adj (p q : ℝ[X]) :
    ∫ x, (derivative p).eval x * q.eval x ∂γ = ∫ x, p.eval x * (x * q.eval x - (derivative q).eval x) ∂γ := by
  have := ibp_gen (F := pf p) (G := pf q) (pf_sm p) (pf_sm q)
    (by
      have h := (pf_PG p).mul ((pf_PG q).sub (pf_PG q |> fun _ => (pf_PG (derivative q))) |> fun _ =>
        ((pf_PG (derivative q)).sub (pg_id.mul (pf_PG q))))
      simpa [deriv_pf, pf] using h.integrable)
    (by
      have h := (pf_PG (derivative p)).mul (pf_PG q)
      simpa [deriv_pf, pf] using h.integrable)
    (by
      have h := (pf_PG p).mul (pf_PG q)
      simpa [pf] using h.integrable)
  simp only [deriv_pf, pf] at this
  have e : ∫ x, p.eval x * ((derivative q).eval x - x * q.eval x) ∂γ =
      -∫ x, p.eval x * (x * q.eval x - (derivative q).eval x) ∂γ := by
    rw [← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only; ring
  rw [e] at this
  linarith

/-! ### Hermite polynomials -/

/-- probabilists' Hermite polynomial over `ℝ` -/
noncomputable def He (n : ℕ) : ℝ[X] := (hermite n).map (Int.castRingHom ℝ)

lemma He_zero : He 0 = 1 := by simp [He, hermite_zero]

lemma He_succ (n : ℕ) : He (n + 1) = X * He n - derivative (He n) := by
  simp [He, hermite_succ, Polynomial.map_sub, Polynomial.map_mul, derivative_map]

lemma He_monic (n : ℕ) : (He n).Monic := (hermite_monic n).map _

lemma He_natDegree (n : ℕ) : (He n).natDegree = n := by
  rw [He, (hermite_monic n).natDegree_map, natDegree_hermite]

lemma He_coeff_self (n : ℕ) : (He n).coeff n = 1 := by
  have h := (He_monic n)
  rw [Monic, leadingCoeff, He_natDegree] at h
  exact h

lemma derivative_He (n : ℕ) : derivative (He (n + 1)) = C ((n : ℝ) + 1) * He n := by
  induction n with
  | zero => simp [He_succ, He_zero]
  | succ n ih =>
    rw [He_succ (n + 1), derivative_sub, derivative_mul, derivative_X, one_mul]
    have h2 : derivative (derivative (He (n + 1))) = C ((n : ℝ) + 1) * derivative (He n) := by
      rw [ih, derivative_mul, derivative_C, zero_mul, zero_add]
    rw [h2, ih, He_succ n]
    simp only [C_add, C_1, map_natCast, Nat.cast_add, Nat.cast_one]
    push_cast
    ring

lemma Lpoly_He (n : ℕ) :
    derivative (derivative (He n)) - X * derivative (He n) = C (-(n : ℝ)) * He n := by
  cases n with
  | zero => simp [He_zero]
  | succ n =>
    rw [derivative_He, derivative_mul, derivative_C, zero_mul, zero_add, He_succ n]
    simp only [C_neg, Nat.cast_add, Nat.cast_one]
    push_cast
    simp only [C_add, C_1]
    ring

lemma Lo_He (n : ℕ) : Lo (pf (He n)) = fun x => -(n : ℝ) * (He n).eval x := by
  rw [Lo_pf, Lpoly_He]; funext x; simp

lemma He_zero_val (n : ℕ) : (He (n + 2)).eval 0 = -((n : ℝ) + 1) * (He n).eval 0 := by
  rw [He_succ, eval_sub, eval_mul, eval_X, zero_mul, zero_sub, derivative_He]
  simp; ring

/-- `∫ He_n q dγ = ∫ q^{(n)} dγ` -/
lemma integral_He_mul (n : ℕ) : ∀ q : ℝ[X],
    ∫ x, (He n).eval x * q.eval x ∂γ = ∫ x, (derivative^[n] q).eval x ∂γ := by
  induction n with
  | zero => intro q; simp [He_zero]
  | succ n ih =>
    intro q
    have h := poly_adj (He n) q
    have e : ∫ x, (He (n + 1)).eval x * q.eval x ∂γ =
        ∫ x, (He n).eval x * (derivative q).eval x ∂γ := by
      have hi1 : Integrable (fun x => x * ((He n).eval x * q.eval x)) γ := by
        have := (pg_id.mul ((pf_PG (He n)).mul (pf_PG q))).integrable
        simpa [pf] using this
      have hi2 : Integrable (fun x => (derivative (He n)).eval x * q.eval x) γ := by
        simpa [pf] using ((pf_PG (derivative (He n))).mul (pf_PG q)).integrable
      have hi3 : Integrable (fun x => (He n).eval x * (x * q.eval x - (derivative q).eval x)) γ := by
        have := ((pf_PG (He n)).mul ((pg_id.mul (pf_PG q)).sub (pf_PG (derivative q)))).integrable
        simpa [pf] using this
      have hi4 : Integrable (fun x => (He n).eval x * (derivative q).eval x) γ := by
        simpa [pf] using ((pf_PG (He n)).mul (pf_PG (derivative q))).integrable
      have : ∀ x, (He (n + 1)).eval x * q.eval x =
          x * ((He n).eval x * q.eval x) - (derivative (He n)).eval x * q.eval x := by
        intro x; rw [He_succ]; simp; ring
      simp_rw [this]
      rw [integral_sub hi1 hi2, h]
      have : ∀ x, x * ((He n).eval x * q.eval x) = (He n).eval x * (x * q.eval x) := fun x => by ring
      simp_rw [this]
      rw [← integral_sub (by simpa [pf] using ((pf_PG (He n)).mul (pg_id.mul (pf_PG q))).integrable) hi3]
      refine integral_congr_ae (ae_of_all _ fun x => ?_)
      simp only; ring
    rw [e, ih, Function.iterate_succ_apply]

lemma iterate_derivative_He (k n : ℕ) :
    derivative^[k] (He (n + k)) = C (((n + k).descFactorial k : ℕ) : ℝ) * He n := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    have e : n + (k + 1) = (n + k) + 1 := by ring
    rw [e, Function.iterate_succ_apply, derivative_He, iterate_derivative_C_mul, ih,
      ← mul_assoc, ← C_mul, Nat.succ_descFactorial_succ]
    congr 2
    push_cast
    ring

lemma integral_He_He_le (n j : ℕ) :
    ∫ x, (He n).eval x * (He (j + n)).eval x ∂γ = if j = 0 then (n.factorial : ℝ) else 0 := by
  rw [integral_He_mul, iterate_derivative_He]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [He_zero, Nat.descFactorial_self]
  · have h := integral_He_mul j (1 : ℝ[X])
    rw [iterate_derivative_one hj] at h
    simp only [eval_mul, eval_C, eval_zero, eval_one, mul_one, integral_zero] at h ⊢
    simp only [hj.ne', ite_false]
    rw [integral_const_mul, h, mul_zero]

lemma integral_He_He (n m : ℕ) :
    ∫ x, (He n).eval x * (He m).eval x ∂γ = if n = m then (n.factorial : ℝ) else 0 := by
  rcases lt_trichotomy n m with h | h | h
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    have := integral_He_He_le n (j + 1)
    rw [show n + j + 1 = (j + 1) + n by ring]
    rw [this]; simp [show ¬ (n = j + 1 + n) by omega]
  · subst h; have := integral_He_He_le n 0; simpa using this
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_lt h
    have := integral_He_He_le m (j + 1)
    rw [show m + j + 1 = (j + 1) + m by ring]
    simp_rw [mul_comm ((He (j + 1 + m)).eval _)]
    rw [this]; simp [show ¬ (m + (j + 1) = m) by omega]

/-- normalised Hermite function -/
noncomputable def hh (n : ℕ) : ℝ → ℝ := fun x => (√(n.factorial : ℝ))⁻¹ * (He n).eval x

lemma hh_PG (n : ℕ) : PG (hh n) := (pf_PG (He n)).const_mul _

lemma hh_sm (n : ℕ) : Sm (hh n) := contDiff_const.mul (pf_sm (He n))

lemma hh_memLp (n : ℕ) : MemLp (hh n) 2 γ := (hh_PG n).memLp_two

lemma integral_hh_hh (n m : ℕ) :
    ∫ x, hh n x * hh m x ∂γ = if n = m then 1 else 0 := by
  have e : ∀ x, hh n x * hh m x =
      ((√(n.factorial : ℝ))⁻¹ * (√(m.factorial : ℝ))⁻¹) * ((He n).eval x * (He m).eval x) := by
    intro x; simp only [hh]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_He_He]
  split_ifs with h
  · subst h
    have : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
    have hs : √(n.factorial : ℝ) * √(n.factorial : ℝ) = n.factorial := Real.mul_self_sqrt this.le
    have hp : 0 < √(n.factorial : ℝ) := Real.sqrt_pos.2 this
    rw [← mul_inv, hs]; exact inv_mul_cancel₀ this.ne'
  · simp

end MarkovTriple.Sanity.OU
