import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R27.Sphere2Calc

/-!
# `L` and `Γ` of the coordinate functions of `S²` in a stereographic chart

With `F_a = Fc a` the coordinate functions, `L F_a = -2 F_a` (eigenvalue `-2 = -d` of `S²`) and
`Γ(F_a, F_b) = δ_{ab} - F_a F_b` (BGL Sect. 2.2 / the sphere example), computed from the chartwise formulas.
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

lemma lap_Fc0 (x : Ev 2) : ∑ k, pderiv (pderiv (Fc 0) k) k x = -16 * x 0 * qf x ^ 3 := by
  have e0 : pderiv (Fc 0) 0 = fun y => 2 * qf y - 4 * (y 0 * y 0) * qf y ^ 2 := funext fun y => by
    rw [pd_Fc0]; simp only [Fin.isValue, ↓reduceIte]; ring
  have e1 : pderiv (Fc 0) 1 = fun y => -4 * (y 0 * y 1) * qf y ^ 2 := funext fun y => by
    rw [pd_Fc0]; simp only [Fin.isValue, zero_ne_one, ↓reduceIte]; ring
  rw [Fin.sum_univ_two, e0, e1]
  simp (disch := first | fun_prop | assumption) only [pderiv_sub, pderiv_mul,
    pderiv_coord, pderiv_qf, pderiv_qf_sq, pderiv_const]
  norm_num
  have h : qf x * (1 + x 0 ^ 2 + x 1 ^ 2) = 1 := by
    unfold qf r2; field_simp; ring
  linear_combination (16 * x 0 * qf x ^ 2) * h

lemma lap_Fc1 (x : Ev 2) : ∑ k, pderiv (pderiv (Fc 1) k) k x = -16 * x 1 * qf x ^ 3 := by
  have e0 : pderiv (Fc 1) 0 = fun y => -4 * (y 1 * y 0) * qf y ^ 2 := funext fun y => by
    rw [pd_Fc1]; simp only [Fin.isValue, one_ne_zero, ↓reduceIte]; ring
  have e1 : pderiv (Fc 1) 1 = fun y => 2 * qf y - 4 * (y 1 * y 1) * qf y ^ 2 := funext fun y => by
    rw [pd_Fc1]; simp only [Fin.isValue, ↓reduceIte]; ring
  rw [Fin.sum_univ_two, e0, e1]
  simp (disch := first | fun_prop | assumption) only [pderiv_sub, pderiv_mul,
    pderiv_coord, pderiv_qf, pderiv_qf_sq, pderiv_const]
  norm_num
  have h : qf x * (1 + x 0 ^ 2 + x 1 ^ 2) = 1 := by
    unfold qf r2; field_simp; ring
  linear_combination (16 * x 1 * qf x ^ 2) * h

lemma lap_Fc2 (x : Ev 2) : ∑ k, pderiv (pderiv (Fc 2) k) k x = 8 * qf x ^ 3 * (1 - r2 x) := by
  have e : ∀ k : Fin 2, pderiv (Fc 2) k = fun y => 4 * y k * qf y ^ 2 := fun k => funext fun y => pd_Fc2 k y
  simp only [e]
  rw [Fin.sum_univ_two]
  simp (disch := first | fun_prop | assumption) only [pderiv_mul,
    pderiv_coord, pderiv_qf_sq, pderiv_const]
  norm_num
  have h' := one_add_r2_ne x
  unfold r2 at h' ⊢
  simp only [qf, r2]
  field_simp
  ring

lemma lap_Fc (a : Fin 3) (x : Ev 2) : ∑ k, pderiv (pderiv (Fc a) k) k x =
    match a with
    | 0 => -16 * x 0 * qf x ^ 3
    | 1 => -16 * x 1 * qf x ^ 3
    | 2 => 8 * qf x ^ 3 * (1 - r2 x) := by
  fin_cases a
  · exact lap_Fc0 x
  · exact lap_Fc1 x
  · exact lap_Fc2 x

/-- `Fc` is an eigenfunction of the chartwise Laplace-Beltrami operator: `L F = -2 F` -/
theorem Lch_Fc (a : Fin 3) (x : Ev 2) : Lch gS wS (Fc a) x = -2 * Fc a x := by
  rw [Lch_conformal, lap_Fc]
  have h := one_add_r2_ne x
  have h' : (1 + x 0 ^ 2 + x 1 ^ 2) ≠ 0 := by unfold r2 at h; rwa [← add_assoc] at h
  fin_cases a
  · simp only [wS, qf, r2, Fc, Fin.isValue]
    field_simp
    ring
  · simp only [wS, qf, r2, Fc, Fin.isValue]
    field_simp
    ring
  · simp only [wS, qf, r2, Fc, Fin.isValue]
    field_simp
    ring

/-- `Γ(F_a, F_b) = δ_{ab} - F_a F_b` in the chart -/
theorem Gch_Fc (a b : Fin 3) (x : Ev 2) :
    Gch gS (Fc a) (Fc b) x = (if a = b then 1 else 0) - Fc a x * Fc b x := by
  rw [Gch_conformal, Fin.sum_univ_two]
  have h := one_add_r2_ne x
  have h' : (1 + x 0 ^ 2 + x 1 ^ 2) ≠ 0 := by unfold r2 at h; rwa [← add_assoc] at h
  have c3 : ∀ a : Fin 3, a = 0 ∨ a = 1 ∨ a = 2 := by decide
  rcases c3 a with rfl | rfl | rfl <;> rcases c3 b with rfl | rfl | rfl <;>
    simp only [pd_Fc0, pd_Fc1, pd_Fc2] <;> simp [Fc, qf, r2] <;> field_simp <;> ring

end MarkovTriple.BGL.Instances.Riemannian.R27
