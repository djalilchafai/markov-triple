import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.Curvature
import MarkovTriple.BGL.Instances.Riemannian.CurvSum

/-!
# The Laplace–Beltrami operator in terms of the Hessian (BGL (C.3.3), (1.11.10))

`Σ_b γ_{ib}^b = ∂_i log w_g` (Jacobi's formula and `∂g^{ij} = −g^{ib} ∂g_{bc} g^{cj}`), hence for `C^∞` `u`
`L u = Σ_{ij} g^{ij} ∇_i∇_j u − Σ_{ij} g^{ij} ∂_iW ∂_j u`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

lemma pderiv_neg' {f : Rd d → ℝ} (i : Fin d) (x : Rd d) :
    pderiv (fun y => -f y) i x = -pderiv f i x := by
  unfold pderiv
  rw [fderiv_fun_neg]
  rfl

namespace RiemData
variable (R : RiemData d)

lemma trace_chr (i : Fin d) (x : Rd d) :
    ∑ b, R.chr b i b x = (1 / 2) * ∑ b, ∑ p, R.g b p x * pderiv (R.gl b p) i x := by
  unfold chr chr1
  have h3 : ∑ b, ∑ p, R.g b p x * pderiv (R.gl i b) p x =
      ∑ b, ∑ p, R.g b p x * pderiv (R.gl i p) b x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun p _ => ?_
    rw [R.g_symm p b x]
  have e : ∀ b p, R.g b p x * ((1 / 2) * (pderiv (R.gl b p) i x + pderiv (R.gl i p) b x -
      pderiv (R.gl i b) p x)) = (1 / 2) * (R.g b p x * pderiv (R.gl b p) i x) +
      (1 / 2) * (R.g b p x * pderiv (R.gl i p) b x - R.g b p x * pderiv (R.gl i b) p x) := by
    intro b p; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, h3]
  simp

lemma pderiv_log_wg (i : Fin d) (x : Rd d) :
    pderiv (fun y => Real.log (R.wg y)) i x =
      (1 / 2) * ∑ b, ∑ p, R.g b p x * pderiv (R.gl b p) i x := by
  have hfun : (fun y => Real.log (R.wg y)) = fun y => (-(1 / 2 : ℝ)) * Real.log (R.detg y) := by
    funext y
    unfold wg
    rw [Real.log_rpow (R.detg_pos y)]
  have hsm : Sm (fun y => Real.log (R.detg y)) := R.sm_detg.log fun y => (R.detg_pos y).ne'
  rw [hfun, pderiv_mul' contDiff_const hsm i x, pderiv_const, zero_mul, zero_add,
    R.pderiv_log_detg i x]
  have key : ∑ b, ∑ c, R.gl b c x * pderiv (R.g c b) i x =
      -∑ p, ∑ q, R.g q p x * pderiv (R.gl p q) i x := by
    have e1 : ∀ b c, R.gl b c x * pderiv (R.g c b) i x =
        -∑ p, ∑ q, R.gl b c x * R.g c p x * pderiv (R.gl p q) i x * R.g q b x := by
      intro b c
      rw [R.pderiv_g_eq i x c b, mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun q _ => by ring
    simp only [e1, Finset.sum_neg_distrib]
    congr 1
    -- Σ_b Σ_c Σ_p Σ_q gl b c g c p D p q g q b = Σ_p Σ_q g q p D p q
    have e2 : ∀ b, ∑ c, ∑ p, ∑ q, R.gl b c x * R.g c p x * pderiv (R.gl p q) i x * R.g q b x =
        ∑ p, ∑ q, (if b = p then 1 else 0) * pderiv (R.gl p q) i x * R.g q b x := by
      intro b
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [← R.gl_mul_mat x b p, Finset.sum_mul, Finset.sum_mul]
    simp only [e2]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [mul_comm]
  rw [key]
  have : ∑ p, ∑ q, R.g q p x * pderiv (R.gl p q) i x =
      ∑ b, ∑ p, R.g b p x * pderiv (R.gl b p) i x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [R.gl_fun_symm q p]
  rw [this]
  ring

lemma pderiv_log_wt (i : Fin d) (x : Rd d) :
    pderiv (fun y => Real.log (R.toEll.w y)) i x = -pderiv R.W i x + ∑ b, R.chr b i b x := by
  have hfun : (fun y => Real.log (R.toEll.w y)) = fun y => -R.W y + Real.log (R.wg y) := by
    funext y
    show Real.log (Real.exp (-R.W y) * R.wg y) = _
    rw [Real.log_mul (Real.exp_pos _).ne' (R.wg_pos y).ne', Real.log_exp]
  have hsm : Sm (fun y => Real.log (R.wg y)) := R.sm_wg.log fun y => (R.wg_pos y).ne'
  rw [hfun, pderiv_add' R.W_smooth.neg hsm i x, pderiv_neg', R.pderiv_log_wg, R.trace_chr]

/-- `Σ_i ∂_i g^{ij} + Σ_i g^{ij} Σ_b γ_{ib}^b = − Σ_{im} g^{im} γ_{im}^j` -/
lemma div_g (j : Fin d) (x : Rd d) :
    ∑ i, pderiv (R.g i j) i x + ∑ i, R.g i j x * ∑ b, R.chr b i b x =
      -∑ i, ∑ m, R.g i m x * R.chr j i m x := by
  have h1 : ∑ i, pderiv (R.g i j) i x =
      -∑ i, ∑ m, R.chr i i m x * R.g m j x - ∑ i, ∑ m, R.chr j i m x * R.g i m x := by
    simp only [R.pderiv_g_chr, Finset.sum_neg_distrib, Finset.sum_add_distrib]
    ring
  have h2 : ∑ i, ∑ m, R.chr i i m x * R.g m j x = ∑ i, R.g i j x * ∑ b, R.chr b i b x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => R.chr_symm i i m x ▸ rfl
  rw [h1, ← h2]
  have h3 : ∑ i, ∑ m, R.chr j i m x * R.g i m x = ∑ i, ∑ m, R.g i m x * R.chr j i m x :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => mul_comm _ _
  rw [h3]
  ring

/-- **`L u = Σ g^{ij} ∇_i∇_j u − Σ g^{ij} ∂_iW ∂_j u`** (BGL (C.3.3) and (1.11.10)), for `C^∞` `u`. -/
theorem L_eq_hess {u : Rd d → ℝ} (hu : Sm u) (x : Rd d) :
    R.toEll.L u x = ∑ i, ∑ j, R.g i j x * R.hess u i j x -
      ∑ i, ∑ j, R.g i j x * pderiv R.W i x * pderiv u j x := by
  have h : R.toEll.L u x = ∑ i, ∑ j, R.g i j x * pderiv (pderiv u j) i x +
      ∑ j, (∑ i, pderiv (R.g i j) i x + ∑ i, R.g i j x *
        pderiv (fun y => Real.log (R.toEll.w y)) i x) * pderiv u j x := ell_L_coord hu x
  simp only [R.pderiv_log_wt] at h
  rw [h]
  have hA : ∑ i, ∑ j, R.g i j x * R.hess u i j x =
      ∑ i, ∑ j, R.g i j x * pderiv (pderiv u j) i x -
        ∑ j, (∑ i, ∑ m, R.g i m x * R.chr j i m x) * pderiv u j x := by
    unfold hess
    simp only [mul_sub, Finset.sum_sub_distrib]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul]
    -- Σ_i Σ_j Σ_k g^{ij} γ^k_{ij} u_k = Σ_k Σ_i Σ_m g^{im} γ^k_{im} u_k
    rw [s3b, s3a]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun m _ => by ring
  have hB : ∑ j, (∑ i, pderiv (R.g i j) i x + ∑ i, R.g i j x * (-pderiv R.W i x +
        ∑ b, R.chr b i b x)) * pderiv u j x =
      -∑ j, (∑ i, ∑ m, R.g i m x * R.chr j i m x) * pderiv u j x -
        ∑ i, ∑ j, R.g i j x * pderiv R.W i x * pderiv u j x := by
    have e : ∀ j, (∑ i, pderiv (R.g i j) i x + ∑ i, R.g i j x * (-pderiv R.W i x +
        ∑ b, R.chr b i b x)) = (-∑ i, ∑ m, R.g i m x * R.chr j i m x) -
          ∑ i, R.g i j x * pderiv R.W i x := by
      intro j
      have := R.div_g j x
      simp only [mul_add, Finset.sum_add_distrib, mul_neg, Finset.sum_neg_distrib]
      linarith
    simp only [e, sub_mul, Finset.sum_sub_distrib, neg_mul, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
  rw [hA]
  have : ∀ j, (∑ i, pderiv (R.g i j) i x + ∑ i, R.g i j x * (-pderiv R.W i x +
        ∑ b, R.chr b i b x)) = _ := fun j => rfl
  linarith [hB]

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
