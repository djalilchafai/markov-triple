import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Atlas.Vol1

/-!
# The cone map `Φ_b(y, r) = r · P_b(y)` and its Jacobian (Round 29, stream R, R2)

`Φ_b : ℝ³ → ℝ³`, `v ↦ v₂ · P_b(v₀, v₁)`.  Its Jacobian matrix has columns `(v₂ ∂₀P, v₂ ∂₁P, P)`; by the isometry data (`Vol1`)
its Gram matrix is `diag(v₂² w, v₂² w, 1)`, so `|det| = v₂² w_S(v₀,v₁)`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.SphereN.Atlas

open MarkovTriple.BGL.Instances.Riemannian.R27
open LebesgueRd (dd)

/-- the chart coordinates `(v₀, v₁)` -/
def yv (v : Fin 3 → ℝ) : Ev 2 := fun j => v (Fin.castSucc j)

/-- the cone map -/
noncomputable def Φ (b : Bool) (v : Fin 3 → ℝ) : Fin 3 → ℝ := fun a => v 2 * Pc b (yv v) a

/-- the Jacobian matrix -/
noncomputable def Mjac (b : Bool) (v : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ := fun a j =>
  if h : (j : ℕ) < 2 then v 2 * dd ⟨j, h⟩ (fun z => Pc b z a) (yv v) else Pc b (yv v) a

/-- the Jacobian as a continuous linear map -/
noncomputable def Ljac (b : Bool) (v : Fin 3 → ℝ) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' (Mjac b v))

noncomputable def yvL : (Fin 3 → ℝ) →L[ℝ] (Ev 2) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) (Fin.castSucc j)

lemma yvL_apply (v : Fin 3 → ℝ) : yvL v = yv v := rfl

lemma hasFDerivAt_Φ_comp (b : Bool) (a : Fin 3) (v : Fin 3 → ℝ) :
    HasFDerivAt (fun v => Φ b v a)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) a).comp (Ljac b v)) v := by
  have h1 : HasFDerivAt (fun v : Fin 3 → ℝ => Pc b (yv v) a)
      ((fderiv ℝ (fun z => Pc b z a) (yv v)).comp yvL) v :=
    (diff_Pc b a (yv v)).hasFDerivAt.comp v yvL.hasFDerivAt
  have h2 := (hasFDerivAt_apply (2 : Fin 3) v).mul h1
  refine h2.congr_fderiv ?_
  ext1 w
  simp only [ContinuousLinearMap.comp_apply, add_apply, smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [MarkovTriple.BGL.Lebesgue.clm_pi_apply (fderiv ℝ (fun z => Pc b z a) (yv v)) (yvL w)]
  simp only [Ljac, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_three, Mjac, Fin.sum_univ_two]
  simp [yvL_apply, yv, dd]
  ring

lemma hasFDerivAt_Φ (b : Bool) (v : Fin 3 → ℝ) : HasFDerivAt (Φ b) (Ljac b v) v := by
  rw [hasFDerivAt_pi']
  exact fun a => hasFDerivAt_Φ_comp b a v

lemma det_Ljac (b : Bool) (v : Fin 3 → ℝ) : (Ljac b v).det = (Mjac b v).det := by
  unfold Ljac
  rw [ContinuousLinearMap.det]
  exact LinearMap.det_toLin' _

lemma gram_M (b : Bool) (v : Fin 3 → ℝ) :
    (Mjac b v).transpose * Mjac b v =
      Matrix.diagonal ![v 2 ^ 2 * wS (yv v), v 2 ^ 2 * wS (yv v), 1] := by
  have g00 := gram_Pc b 0 0 (yv v)
  have g01 := gram_Pc b 0 1 (yv v)
  have g11 := gram_Pc b 1 1 (yv v)
  have d0 := dot_Pc b 0 (yv v)
  have d1 := dot_Pc b 1 (yv v)
  have n1 := norm_Pc b (yv v)
  simp only [Fin.sum_univ_three] at g00 g01 g11 d0 d1 n1
  simp only [Fin.isValue, ↓reduceIte, Fin.reduceEq] at g00 g01 g11
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Mjac]
  fin_cases j <;> fin_cases k <;> simp [Fin.sum_univ_three]
  · linear_combination v 2 ^ 2 * g00
  · linear_combination v 2 ^ 2 * g01
  · linear_combination v 2 * d0
  · linear_combination v 2 ^ 2 * g01
  · linear_combination v 2 ^ 2 * g11
  · linear_combination v 2 * d1
  · linear_combination v 2 * d0
  · linear_combination v 2 * d1
  · linear_combination n1

lemma abs_det_Mjac (b : Bool) (v : Fin 3 → ℝ) : |(Mjac b v).det| = v 2 ^ 2 * wS (yv v) := by
  have h := congrArg Matrix.det (gram_M b v)
  rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at h
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val] at h
  have hw := wS_pos (yv v)
  have : |(Mjac b v).det| ^ 2 = (v 2 ^ 2 * wS (yv v)) ^ 2 := by
    rw [sq_abs]; nlinarith [h]
  have h2 : 0 ≤ v 2 ^ 2 * wS (yv v) := by positivity
  exact (sq_eq_sq₀ (abs_nonneg _) h2).1 this

end MarkovTriple.BGL.SphereN.Atlas
