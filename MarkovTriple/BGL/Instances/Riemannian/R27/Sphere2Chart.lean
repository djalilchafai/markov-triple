import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R27.Atlas
import MarkovTriple.BGL.Instances.Riemannian.R27.Sphere2Calc

/-!
# The two stereographic charts of `S²`: parametrisations, overlaps, inversion

`S2 = {p ∈ ℝ³ | p₀² + p₁² + p₂² = 1}`.  The chart `b : Bool` is `y ↦ (2y₀, 2y₁, σ_b(|y|²-1))/(1+|y|²)`
(`σ_true = 1`, `σ_false = -1`), defined on all of `ℝ²`; chart `true` misses `(0,0,1)`, chart `false` misses `(0,0,-1)`.
Overlap: `y ≠ 0`, transition `y ↦ y/|y|²`.
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

/-- the unit sphere of `ℝ³` -/
def S2 : Type := {p : Fin 3 → ℝ // p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 = 1}

/-- the sign `σ_b` -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]
lemma sgn_ne (b : Bool) : sgn b ≠ 0 := by cases b <;> simp [sgn]

lemma qf_pos (y : Ev 2) : 0 < qf y := inv_pos.2 (one_add_r2_pos y)

lemma Fc_sphere (y : Ev 2) : Fc 0 y ^ 2 + Fc 1 y ^ 2 + Fc 2 y ^ 2 = 1 := by
  have h := one_add_r2_ne y
  have h' : (1 + y 0 ^ 2 + y 1 ^ 2) ≠ 0 := by unfold r2 at h; rwa [← add_assoc] at h
  simp only [Fc, qf, r2]
  field_simp
  ring

/-- the point of the sphere with stereographic coordinates `y` in chart `b` -/
noncomputable def ptS (b : Bool) (y : Ev 2) : S2 :=
  ⟨![Fc 0 y, Fc 1 y, sgn b * Fc 2 y], by
    have := Fc_sphere y
    have h2 := sgn_sq b
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_pow, h2]
    linarith⟩

lemma ptS_val0 (b : Bool) (y : Ev 2) : (ptS b y).1 0 = Fc 0 y := rfl
lemma ptS_val1 (b : Bool) (y : Ev 2) : (ptS b y).1 1 = Fc 1 y := rfl
lemma ptS_val2 (b : Bool) (y : Ev 2) : (ptS b y).1 2 = sgn b * Fc 2 y := rfl

lemma ptS_inj (b : Bool) : Function.Injective (ptS b) := by
  intro y y' h
  have h0 : Fc 0 y = Fc 0 y' := congrArg (fun p : S2 => p.1 0) h
  have h1 : Fc 1 y = Fc 1 y' := congrArg (fun p : S2 => p.1 1) h
  have h2 : sgn b * Fc 2 y = sgn b * Fc 2 y' := congrArg (fun p : S2 => p.1 2) h
  have h2' : Fc 2 y = Fc 2 y' := mul_left_cancel₀ (sgn_ne b) h2
  have hq : qf y = qf y' := by simp only [Fc] at h2'; linarith
  have hq0 : qf y ≠ 0 := (qf_pos y).ne'
  funext i
  fin_cases i
  · simp only [Fc] at h0; rw [← hq] at h0
    have := mul_right_cancel₀ hq0 h0
    simpa using this
  · simp only [Fc] at h1; rw [← hq] at h1
    have := mul_right_cancel₀ hq0 h1
    simpa using this

/-- the inversion `y ↦ y/|y|²` -/
noncomputable def invS (y : Ev 2) : Ev 2 := fun i => y i / r2 y

lemma r2_ne_zero {x : Ev 2} (hx : x ≠ 0) : r2 x ≠ 0 := by
  intro h
  apply hx
  unfold r2 at h
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  have h1 : x 1 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  funext i; fin_cases i <;> simp [h0, h1]

lemma r2_pos {x : Ev 2} (hx : x ≠ 0) : 0 < r2 x := lt_of_le_of_ne (r2_nonneg x) (r2_ne_zero hx).symm

lemma r2_invS {x : Ev 2} (hx : x ≠ 0) : r2 (invS x) = (r2 x)⁻¹ := by
  have h := r2_ne_zero hx
  show (x 0 / r2 x) ^ 2 + (x 1 / r2 x) ^ 2 = (r2 x)⁻¹
  have e : x 0 ^ 2 + x 1 ^ 2 = r2 x := rfl
  rw [div_pow, div_pow, ← add_div, e]
  field_simp

lemma qf_invS {x : Ev 2} (hx : x ≠ 0) : qf (invS x) = r2 x * qf x := by
  have h := r2_ne_zero hx
  have h1 := one_add_r2_ne x
  have h2 : r2 x + 1 ≠ 0 := by rwa [add_comm]
  unfold qf
  rw [r2_invS hx]
  field_simp
  ring

lemma ptS_invS {a b : Bool} (hab : a ≠ b) {x : Ev 2} (hx : x ≠ 0) : ptS b (invS x) = ptS a x := by
  have h := r2_ne_zero hx
  have h1 := one_add_r2_ne x
  have hs : sgn b = - sgn a := by cases a <;> cases b <;> simp_all [sgn]
  have e : r2 x = x 0 ^ 2 + x 1 ^ 2 := rfl
  apply Subtype.ext
  funext i
  fin_cases i
  · show Fc 0 (invS x) = Fc 0 x
    simp only [Fc, qf_invS hx, invS]
    simp only [qf]
    field_simp
  · show Fc 1 (invS x) = Fc 1 x
    simp only [Fc, qf_invS hx, invS]
    simp only [qf]
    field_simp
  · show sgn b * Fc 2 (invS x) = sgn a * Fc 2 x
    rw [hs]
    simp only [Fc, qf_invS hx]
    simp only [qf]
    field_simp
    ring

end MarkovTriple.BGL.Instances.Riemannian.R27
