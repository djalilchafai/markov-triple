import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R27.Basic

/-!
# Calculus on the stereographic chart of `S²`: `r² = |y|²`, `q = 1/(1+r²)` and the coordinate functions

`pderiv` formulas for `r2 y = y₀² + y₁²`, `q = (1+r²)⁻¹`, the inversion `y ↦ y/|y|²`, and the closed forms of the
first partial derivatives of the three coordinate functions `2y₀ q`, `2y₁ q`, `1 - 2q` of the sphere.
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

/-- `|y|²` on `ℝ²` -/
def r2 (y : Ev 2) : ℝ := y 0 ^ 2 + y 1 ^ 2

/-- `q = 1/(1+|y|²)` -/
noncomputable def qf (y : Ev 2) : ℝ := (1 + r2 y)⁻¹

lemma r2_nonneg (y : Ev 2) : 0 ≤ r2 y := by unfold r2; positivity
lemma one_add_r2_pos (y : Ev 2) : 0 < 1 + r2 y := by have := r2_nonneg y; linarith
lemma one_add_r2_ne (y : Ev 2) : 1 + r2 y ≠ 0 := (one_add_r2_pos y).ne'

section calc_lemmas
variable {d : ℕ} {f h : Ev d → ℝ} {x : Ev d}

lemma pderiv_inv (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) (k : Fin d) :
    pderiv (fun y => (f y)⁻¹) k x = -(pderiv f k x) / (f x) ^ 2 := by
  have h := pderiv_eq_of_hasFDerivAt (f := fun y => (f y)⁻¹) ((hasDerivAt_inv hx).comp_hasFDerivAt x hf.hasFDerivAt) k
  rw [h]
  simp [pderiv, div_eq_mul_inv]
  ring

lemma pderiv_sq_coord (i k : Fin d) (x : Ev d) :
    pderiv (fun y : Ev d => y i ^ 2) k x = if i = k then 2 * x i else 0 := by
  have : (fun y : Ev d => y i ^ 2) = fun y => y i * y i := funext fun y => sq _
  rw [this, pderiv_mul (differentiableAt_apply i x) (differentiableAt_apply i x),
    pderiv_coord]
  split_ifs <;> ring

end calc_lemmas

lemma r2_diff (x : Ev 2) : DifferentiableAt ℝ r2 x := by unfold r2; fun_prop

lemma pderiv_r2 (k : Fin 2) (x : Ev 2) : pderiv r2 k x = 2 * x k := by
  unfold r2
  rw [pderiv_add (by fun_prop) (by fun_prop), pderiv_sq_coord, pderiv_sq_coord]
  fin_cases k <;> simp

lemma qf_diff (x : Ev 2) : DifferentiableAt ℝ qf x := by
  unfold qf
  exact ((differentiableAt_const _).add (r2_diff x)).inv (one_add_r2_ne x)

lemma pderiv_qf (k : Fin 2) (x : Ev 2) : pderiv qf k x = -2 * x k * qf x ^ 2 := by
  unfold qf
  rw [pderiv_inv (by have := r2_diff x; fun_prop) (one_add_r2_ne x), pderiv_add (differentiableAt_const _) (r2_diff x),
    pderiv_const, pderiv_r2]
  have := one_add_r2_ne x
  field_simp
  ring

/-! ### Co-metric and density of the stereographic chart -/

/-- co-metric `g^{ij} = ((1+|y|²)/2)² δ_{ij}` of the round `S²` in a stereographic chart -/
noncomputable def gS (i j : Fin 2) (y : Ev 2) : ℝ := if i = j then ((1 + r2 y) / 2) ^ 2 else 0

/-- Riemannian density `w = det(g)^{-1/2} = 4/(1+|y|²)²` -/
noncomputable def wS (y : Ev 2) : ℝ := 4 / (1 + r2 y) ^ 2

lemma wS_pos (y : Ev 2) : 0 < wS y := by unfold wS; have := one_add_r2_pos y; positivity

lemma wS_mul_gS (k : Fin 2) (y : Ev 2) (G : Fin 2 → ℝ) : wS y * ∑ j, gS k j y * G j = G k := by
  have := one_add_r2_ne y
  unfold wS gS
  fin_cases k <;> simp <;> field_simp <;> ring

lemma Lch_conformal (F : Ev 2 → ℝ) (x : Ev 2) :
    Lch gS wS F x = (wS x)⁻¹ * ∑ k, pderiv (pderiv F k) k x := by
  unfold Lch
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  funext y
  exact wS_mul_gS k y _

lemma Gch_conformal (F H : Ev 2 → ℝ) (x : Ev 2) :
    Gch gS F H x = ((1 + r2 x) / 2) ^ 2 * ∑ k, pderiv F k x * pderiv H k x := by
  unfold Gch gS
  simp
  ring

/-! ### The coordinate functions of `S²` in the chart (north-pole-type stereographic projection) -/

/-- `(2y₀, 2y₁, |y|²-1)/(1+|y|²)` -/
noncomputable def Fc : Fin 3 → Ev 2 → ℝ
  | 0 => fun y => 2 * y 0 * qf y
  | 1 => fun y => 2 * y 1 * qf y
  | 2 => fun y => 1 - 2 * qf y

lemma Fc_diff (a : Fin 3) (x : Ev 2) : DifferentiableAt ℝ (Fc a) x := by
  have hq := qf_diff x
  fin_cases a
  · exact ((differentiableAt_const _).mul (differentiableAt_apply 0 x)).mul hq
  · exact ((differentiableAt_const _).mul (differentiableAt_apply 1 x)).mul hq
  · exact (differentiableAt_const _).sub ((differentiableAt_const _).mul hq)

attribute [fun_prop] qf_diff

lemma pderiv_qf_sq(k : Fin 2) (x : Ev 2) :
    pderiv (fun y => qf y ^ 2) k x = -4 * x k * qf x ^ 3 := by
  have : (fun y => qf y ^ 2) = fun y => qf y * qf y := funext fun y => sq _
  rw [this, pderiv_mul (qf_diff x) (qf_diff x), pderiv_qf]
  ring

/-- first partial derivatives of the coordinate functions -/
lemma pd_Fc0 (k : Fin 2) (y : Ev 2) :
    pderiv (Fc 0) k y = 2 * (if (0 : Fin 2) = k then 1 else 0) * qf y - 4 * y 0 * y k * qf y ^ 2 := by
  show pderiv (fun y => 2 * y 0 * qf y) k y = _
  rw [pderiv_mul (by fun_prop) (qf_diff y), pderiv_qf,
    pderiv_const_mul, pderiv_coord]
  ring

lemma pd_Fc1 (k : Fin 2) (y : Ev 2) :
    pderiv (Fc 1) k y = 2 * (if (1 : Fin 2) = k then 1 else 0) * qf y - 4 * y 1 * y k * qf y ^ 2 := by
  show pderiv (fun y => 2 * y 1 * qf y) k y = _
  rw [pderiv_mul (by fun_prop) (qf_diff y), pderiv_qf,
    pderiv_const_mul, pderiv_coord]
  ring

lemma pd_Fc2 (k : Fin 2) (y : Ev 2) : pderiv (Fc 2) k y = 4 * y k * qf y ^ 2 := by
  show pderiv (fun y => 1 - 2 * qf y) k y = _
  rw [pderiv_sub (differentiableAt_const _) (by have := qf_diff y; fun_prop), pderiv_const,
    pderiv_const_mul, pderiv_qf]
  ring

lemma pderiv_qf_cube (k : Fin 2) (x : Ev 2) :
    pderiv (fun y => qf y ^ 3) k x = -6 * x k * qf x ^ 4 := by
  have : (fun y => qf y ^ 3) = fun y => qf y * qf y ^ 2 := funext fun y => by ring
  rw [this, pderiv_mul (qf_diff x) (by fun_prop), pderiv_qf, pderiv_qf_sq]
  ring


end MarkovTriple.BGL.Instances.Riemannian.R27
