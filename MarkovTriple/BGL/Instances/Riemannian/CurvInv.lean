import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.Data

/-!
# The metric `G = (g_{ij})` as the inverse of the co-metric `(g^{ij})`: smoothness, derivatives, Jacobi's formula

BGL App. C.3: "`G*(x) = (g^{ij}(x))` the inverse matrix, the co-metric".  Everything is for `R : RiemData d`.

* `gl i j` : the entries of `(R.mat x)⁻¹`; `sm_gl`; `gl_symm`; `Σ_j g^{ij} g_{jk} = δ` and `Σ_j g_{ij} g^{jk} = δ`;
* `pderiv_g_eq`: `∂_k g^{ij} = − Σ g^{ib} ∂_k g_{bc} g^{cj}` and the converse;
* `pderiv_detg`: Jacobi's formula `∂_k det(g^{··}) = det · Σ_{bc} g_{bc} ∂_k g^{cb}`, hence
  `pderiv_log_wg : ∂_k log w_g = ½ Σ g^{bc} ∂_k g_{bc}`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

/-- determinant of a matrix field with smooth entries is smooth -/
lemma sm_det_field {M : Rd d → Matrix (Fin d) (Fin d) ℝ} (hM : ∀ i j, Sm (fun x => M x i j)) :
    Sm (fun x => (M x).det) := by
  have : (fun x => (M x).det) = fun x => ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, M x (σ i) i := by
    funext x
    rw [Matrix.det_apply']
  rw [this]
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hM (σ i) i)

namespace RiemData
variable (R : RiemData d)

/-- the metric `g_{ij}(x) = ((g^{ij}(x))⁻¹)_{ij}` -/
noncomputable def gl (i j : Fin d) (x : Rd d) : ℝ := (R.mat x)⁻¹ i j

lemma mat_apply (i j : Fin d) (x : Rd d) : R.mat x i j = R.g i j x := rfl

lemma gl_eq_adj (i j : Fin d) (x : Rd d) :
    R.gl i j x = (R.detg x)⁻¹ * (R.mat x).adjugate i j := by
  unfold gl
  rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

lemma sm_gl (i j : Fin d) : Sm (R.gl i j) := by
  have h : R.gl i j = fun x => (R.detg x)⁻¹ * (R.mat x).adjugate i j := funext (R.gl_eq_adj i j)
  rw [h]
  refine (R.sm_detg.inv fun x => (R.detg_pos x).ne').mul ?_
  have : (fun x => (R.mat x).adjugate i j) =
      fun x => ((R.mat x).updateRow j (Pi.single i 1)).det := by
    funext x; rw [Matrix.adjugate_apply]
  rw [this]
  refine sm_det_field fun a b => ?_
  by_cases ha : a = j
  · subst ha
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simp only [Matrix.updateRow_ne ha]
    exact R.g_smooth a b

lemma mat_symm (x : Rd d) : (R.mat x).IsSymm := by
  ext i j; exact R.g_symm j i x

lemma gl_symm (i j : Fin d) (x : Rd d) : R.gl i j x = R.gl j i x := by
  unfold gl
  have h : ((R.mat x)⁻¹).transpose = (R.mat x)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv, (R.mat_symm x).eq]
  have := congrFun (congrFun h i) j
  simpa [Matrix.transpose_apply] using this.symm

lemma mat_mul_gl (x : Rd d) (i k : Fin d) :
    ∑ j, R.g i j x * R.gl j k x = if i = k then 1 else 0 := by
  have h : R.mat x * (R.mat x)⁻¹ = 1 := Matrix.mul_nonsing_inv _ (R.detg_pos x).ne'.isUnit
  have := congrFun (congrFun h i) k
  simpa [Matrix.mul_apply, Matrix.one_apply, gl, mat_apply] using this

lemma gl_mul_mat (x : Rd d) (i k : Fin d) :
    ∑ j, R.gl i j x * R.g j k x = if i = k then 1 else 0 := by
  have h : (R.mat x)⁻¹ * R.mat x = 1 := Matrix.nonsing_inv_mul _ (R.detg_pos x).ne'.isUnit
  have := congrFun (congrFun h i) k
  simpa [Matrix.mul_apply, Matrix.one_apply, gl, mat_apply] using this

end RiemData

/-- derivative of a finite product -/
lemma pderiv_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) {F : ι → Rd d → ℝ} (hF : ∀ j, Sm (F j))
    (k : Fin d) (x : Rd d) :
    pderiv (fun y => ∏ j ∈ s, F j y) k x = ∑ i ∈ s, (∏ j ∈ s.erase i, F j x) * pderiv (F i) k x := by
  unfold pderiv
  rw [fderiv_finsetProd (fun j _ => (hF j).differentiableAt x)]
  simp [smul_eq_mul]

namespace RiemData
variable (R : RiemData d)

lemma pderiv_detg (k : Fin d) (x : Rd d) :
    pderiv R.detg k x = R.detg x * ∑ b, ∑ c, R.gl b c x * pderiv (R.g c b) k x := by
  have hdet : R.detg = fun y => ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, R.g (σ i) i y := by
    funext y; unfold detg mat; rw [Matrix.det_apply']; rfl
  have hP : ∀ σ : Equiv.Perm (Fin d), Sm (fun y => ∏ i, R.g (σ i) i y) := fun σ =>
    contDiff_prod fun i _ => R.g_smooth (σ i) i
  have e : pderiv R.detg k x = pderiv (fun y => ∑ σ : Equiv.Perm (Fin d),
      ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, R.g (σ i) i y) k x := by rw [← hdet]
  rw [e, pderiv_sum _ (fun σ => contDiff_const.mul (hP σ))]
  have h1 : ∀ σ : Equiv.Perm (Fin d), pderiv (fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∏ i, R.g (σ i) i y) k x = ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∑ j, (∏ i ∈ Finset.univ.erase j, R.g (σ i) i x) * pderiv (R.g (σ j) j) k x := by
    intro σ
    have := pderiv_mul' (contDiff_const : Sm (fun _ : Rd d => ((Equiv.Perm.sign σ : ℤ) : ℝ))) (hP σ) k x
    rw [this, pderiv_const, zero_mul, zero_add]
    congr 1
    exact pderiv_prod _ (fun i => R.g_smooth (σ i) i) k x
  simp only [h1]
  -- the matrix `A_j` with column `j` replaced by `∂_k g_{·j}`
  have h2 : ∀ j, ((R.mat x).updateCol j (fun c => pderiv (R.g c j) k x)).det =
      ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
        ((∏ i ∈ Finset.univ.erase j, R.g (σ i) i x) * pderiv (R.g (σ j) j) k x) := by
    intro j
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    congr 1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [Matrix.updateCol_self]
    rw [mul_comm]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have : i ≠ j := Finset.ne_of_mem_erase hi
    simp [Matrix.updateCol_ne this, mat_apply]
  have h3 : ∑ σ : Equiv.Perm (Fin d), ((Equiv.Perm.sign σ : ℤ) : ℝ) *
      ∑ j, (∏ i ∈ Finset.univ.erase j, R.g (σ i) i x) * pderiv (R.g (σ j) j) k x =
      ∑ j, ((R.mat x).updateCol j (fun c => pderiv (R.g c j) k x)).det := by
    simp only [h2, Finset.mul_sum]
    exact Finset.sum_comm
  rw [h3]
  have h4 : ∀ j, ((R.mat x).updateCol j (fun c => pderiv (R.g c j) k x)).det =
      R.detg x * ∑ c, R.gl j c x * pderiv (R.g c j) k x := by
    intro j
    rw [← Matrix.cramer_apply, Matrix.cramer_eq_adjugate_mulVec, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hA : (R.mat x).adjugate j c = R.detg x * R.gl j c x := by
      rw [R.gl_eq_adj, ← mul_assoc, mul_inv_cancel₀ (R.detg_pos x).ne', one_mul]
    rw [hA]; ring
  simp only [h4, Finset.mul_sum]

lemma pderiv_log_detg (k : Fin d) (x : Rd d) :
    pderiv (fun y => Real.log (R.detg y)) k x =
      ∑ b, ∑ c, R.gl b c x * pderiv (R.g c b) k x := by
  have h := (R.sm_detg.hasFDerivAt' x).log (R.detg_pos x).ne'
  unfold pderiv
  rw [h.fderiv]
  have := R.pderiv_detg k x
  unfold pderiv at this
  simp only [smul_apply, smul_eq_mul]
  rw [this]
  field_simp [(R.detg_pos x).ne']

end RiemData

/-- derivative of an inverse matrix field: if `A B = 1 = B A` (entrywise sums) then `∂ B = − B (∂ A) B`. -/
lemma pderiv_inv_aux (A B : Fin d → Fin d → Rd d → ℝ) (hA : ∀ i j, Sm (A i j)) (hB : ∀ i j, Sm (B i j))
    (hAB : ∀ x i k, ∑ j, A i j x * B j k x = if i = k then 1 else 0)
    (hBA : ∀ x i k, ∑ j, B i j x * A j k x = if i = k then 1 else 0)
    (k : Fin d) (x : Rd d) (i m : Fin d) :
    pderiv (B i m) k x = -∑ b, ∑ c, B i b x * pderiv (A b c) k x * B c m x := by
  have hd : ∀ i j, ∑ b, (pderiv (B i b) k x * A b j x + B i b x * pderiv (A b j) k x) =
      0 := by
    intro i j
    have e : (fun y => ∑ b, B i b y * A b j y) = fun _ => if i = j then (1 : ℝ) else 0 := by
      funext y; exact hBA y i j
    have := congrArg (fun F => pderiv F k x) e
    simp only [pderiv_const] at this
    rw [pderiv_sum _ (fun b => (hB i b).mul (hA b j))] at this
    rw [← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact (pderiv_mul' (hB i b) (hA b j) k x).symm
  have h1 : pderiv (B i m) k x = ∑ j, (∑ b, pderiv (B i b) k x * A b j x) * B j m x := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    have : ∀ b, ∑ j, pderiv (B i b) k x * A b j x * B j m x = pderiv (B i b) k x *
        (if b = m then 1 else 0) := by
      intro b
      simp only [mul_assoc]
      rw [← Finset.mul_sum, hAB x b m]
    simp only [this]
    simp
  have h2 : ∀ j, ∑ b, pderiv (B i b) k x * A b j x = -∑ b, B i b x * pderiv (A b j) k x := by
    intro j
    have := hd i j
    rw [Finset.sum_add_distrib] at this
    linarith
  rw [h1]
  simp only [h2, neg_mul, Finset.sum_mul, Finset.sum_neg_distrib]
  congr 1
  exact Finset.sum_comm

namespace RiemData
variable (R : RiemData d)

/-- `∂_k g_{im} = − Σ_{bc} g_{ib} ∂_k g^{bc} g_{cm}` -/
lemma pderiv_gl_eq (k : Fin d) (x : Rd d) (i m : Fin d) :
    pderiv (R.gl i m) k x = -∑ b, ∑ c, R.gl i b x * pderiv (R.g b c) k x * R.gl c m x :=
  pderiv_inv_aux R.g R.gl R.g_smooth R.sm_gl (fun x i k => R.mat_mul_gl x i k)
    (fun x i k => R.gl_mul_mat x i k) k x i m

/-- `∂_k g^{im} = − Σ_{bc} g^{ib} ∂_k g_{bc} g^{cm}` -/
lemma pderiv_g_eq (k : Fin d) (x : Rd d) (i m : Fin d) :
    pderiv (R.g i m) k x = -∑ b, ∑ c, R.g i b x * pderiv (R.gl b c) k x * R.g c m x :=
  pderiv_inv_aux R.gl R.g R.sm_gl R.g_smooth (fun x i k => R.gl_mul_mat x i k)
    (fun x i k => R.mat_mul_gl x i k) k x i m

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
