import MarkovTriple.BGL.Analysis.OU.Mehler

/-! # OU (Part 17): the Hermite identity `E He_n(a z + b W) = aⁿ He_n(z)` for `a² + b² = 1` -/

open MeasureTheory Filter Topology Polynomial
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

lemma pg_comp (p : ℝ[X]) (b z : ℝ) : PG (fun w => p.eval (z + b * w)) := by
  have e : (fun w : ℝ => p.eval (z + b * w)) = pf (p.comp (C z + C b * X)) := by
    funext w; simp [pf, eval_comp]
  rw [e]; exact pf_PG _

lemma integral_id_mul_poly (p : ℝ[X]) :
    ∫ w, w * p.eval w ∂γ = ∫ w, (derivative p).eval w ∂γ := by
  have := poly_adj p 1
  simp only [derivative_one, eval_one, mul_one, eval_zero, sub_zero] at this
  rw [this]
  exact integral_congr_ae (ae_of_all _ fun w => by ring)

lemma integral_id_mul_comp (p : ℝ[X]) (b z : ℝ) :
    ∫ w, w * p.eval (z + b * w) ∂γ = b * ∫ w, (derivative p).eval (z + b * w) ∂γ := by
  have := integral_id_mul_poly (p.comp (C b * X + C z))
  simp only [derivative_comp, derivative_add, derivative_mul, derivative_C, derivative_X,
    zero_mul, mul_one, zero_add, add_zero, eval_comp, eval_add, eval_mul, eval_C, eval_X,
    eval_mul] at this
  have e1 : (fun w : ℝ => w * p.eval (b * w + z)) = fun w => w * p.eval (z + b * w) := by
    funext w; rw [add_comm]
  have e2 : (fun w : ℝ => b * (derivative p).eval (b * w + z)) =
      fun w => b * (derivative p).eval (z + b * w) := by
    funext w; rw [add_comm]
  rw [e1, e2, integral_const_mul] at this
  exact this

lemma He_derivative_succ (m : ℕ) : derivative (He (m + 1)) = C ((m : ℝ) + 1) * He m :=
  derivative_He m

/-- one-step recurrence of `Q_n(z) = ∫ He_n(a z + b w) dγ(w)` -/
lemma Q_succ (a b z : ℝ) (n : ℕ) :
    ∫ w, (He (n + 1)).eval (a * z + b * w) ∂γ =
      a * z * ∫ w, (He n).eval (a * z + b * w) ∂γ +
        (b ^ 2 - 1) * ∫ w, (derivative (He n)).eval (a * z + b * w) ∂γ := by
  have i1 := (pg_comp (He n) b (a * z)).integrable
  have i2 := (pg_comp (derivative (He n)) b (a * z)).integrable
  have i3 := (pg_id.mul (pg_comp (He n) b (a * z))).integrable
  have e : ∀ w : ℝ, (He (n + 1)).eval (a * z + b * w) =
      a * z * (He n).eval (a * z + b * w) + b * (w * (He n).eval (a * z + b * w)) -
        (derivative (He n)).eval (a * z + b * w) := by
    intro w
    rw [He_succ]; simp only [eval_sub, eval_mul, eval_X]; ring
  simp_rw [e]
  have h1 : Integrable (fun w : ℝ => a * z * (He n).eval (a * z + b * w) +
      b * (w * (He n).eval (a * z + b * w))) γ := (i1.const_mul _).add (i3.const_mul _)
  have h2 : Integrable (fun w : ℝ => a * z * (He n).eval (a * z + b * w)) γ := i1.const_mul _
  have h3 : Integrable (fun w : ℝ => b * (w * (He n).eval (a * z + b * w))) γ := i3.const_mul _
  rw [integral_sub h1 i2, integral_add h2 h3, integral_const_mul, integral_const_mul,
    integral_id_mul_comp]
  ring

lemma Q_eq (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (n : ℕ) :
    (∀ z, ∫ w, (He n).eval (a * z + b * w) ∂γ = a ^ n * (He n).eval z) ∧
    (∀ z, ∫ w, (He (n + 1)).eval (a * z + b * w) ∂γ = a ^ (n + 1) * (He (n + 1)).eval z) := by
  induction n with
  | zero =>
    refine ⟨fun z => by simp [He_zero], fun z => ?_⟩
    rw [Q_succ]
    simp [He_zero]
    rw [He_succ]; simp [He_zero]
  | succ n ih =>
    refine ⟨ih.2, fun z => ?_⟩
    rw [Q_succ, ih.2 z]
    have hd : ∀ w : ℝ, (derivative (He (n + 1))).eval (a * z + b * w) =
        ((n : ℝ) + 1) * (He n).eval (a * z + b * w) := by
      intro w; rw [He_derivative_succ]; simp
    simp_rw [hd]
    rw [integral_const_mul, (ih.1 z), He_succ (n + 1)]
    simp only [eval_sub, eval_mul, eval_X]
    rw [He_derivative_succ]
    simp only [eval_mul, eval_C]
    have hb : b ^ 2 - 1 = -a ^ 2 := by linarith
    rw [hb]; ring

end MarkovTriple.Sanity.OU
