import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R27.Basic

/-!
# The Piola identity (BGL Appendix C.3; classical): `Σₖ ∂ₖ (adj Dτ)_{ki} = 0` for `τ ∈ C²`

Proof: `adj(J)_{ki} = det (J with row i replaced by eₖ)` (`Matrix.adjugate_apply`), Jacobi's formula
(`pderiv_det`) differentiates the remaining rows `∇τ_m`, `m ≠ i`; for each such `m` the sum over `k` of
`det (rows: i ↦ eₖ, m ↦ ∂ₖ∇τ_m)` vanishes because the Hessian of `τ_m` is symmetric while the determinant is
antisymmetric under the exchange of the rows `i`, `m`.
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

section matrix_algebra
variable {n : Type*} [Fintype n] [DecidableEq n]

lemma det_updateRow_expand (A : Matrix n n ℝ) (m : n) (r : n → ℝ) :
    (A.updateRow m r).det = ∑ b, r b * (A.updateRow m (Pi.single b 1)).det := by
  have key : ∀ s : Finset n, (A.updateRow m (∑ b ∈ s, r b • (Pi.single b 1 : n → ℝ))).det =
      ∑ b ∈ s, r b * (A.updateRow m (Pi.single b 1)).det := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact Matrix.det_eq_zero_of_row_eq_zero m (fun j => by simp)
    | insert c s hc ih =>
      rw [Finset.sum_insert hc, Finset.sum_insert hc, ← ih, Matrix.det_updateRow_add,
        Matrix.det_updateRow_smul]
  have hr : (∑ b, r b • (Pi.single b 1 : n → ℝ)) = r := by
    funext c; simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [hr] at this

omit [Fintype n] in
lemma swap_rows_eq (A : Matrix n n ℝ) {i m : n} (him : i ≠ m) (b k : n) :
    (A.updateRow i (Pi.single b 1)).updateRow m (Pi.single k 1) =
      ((A.updateRow i (Pi.single k 1)).updateRow m (Pi.single b 1)).submatrix (Equiv.swap i m) id := by
  ext a c
  by_cases ha : a = i
  · subst ha
    simp [Matrix.updateRow_apply, him, Equiv.swap_apply_left]
  · by_cases ham : a = m
    · subst ham
      simp [Matrix.updateRow_apply, him, Equiv.swap_apply_right]
    · simp [Matrix.updateRow_apply, ha, ham, Equiv.swap_apply_of_ne_of_ne ha ham]

lemma antisym_sum (A : Matrix n n ℝ) {i m : n} (hmi : m ≠ i) (S : n → n → ℝ)
    (hS : ∀ b k, S b k = S k b) :
    ∑ k, ((A.updateRow i (Pi.single k 1)).updateRow m (fun b => S b k)).det = 0 := by
  set D : n → n → ℝ := fun b k => ((A.updateRow i (Pi.single k 1)).updateRow m (Pi.single b 1)).det with hD
  have hanti : ∀ b k, D k b = - D b k := by
    intro b k
    simp only [hD]
    rw [swap_rows_eq A hmi.symm b k, Matrix.det_permute, Equiv.Perm.sign_swap hmi.symm]
    simp
  have hsum : ∑ k, ((A.updateRow i (Pi.single k 1)).updateRow m (fun b => S b k)).det =
      ∑ k, ∑ b, S b k * D b k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [det_updateRow_expand]
  rw [hsum]
  have h2 : ∑ k, ∑ b, S b k * D b k = - ∑ k, ∑ b, S b k * D b k := by
    calc ∑ k, ∑ b, S b k * D b k = ∑ b, ∑ k, S b k * D b k := Finset.sum_comm
      _ = ∑ k, ∑ b, S k b * D k b := rfl
      _ = ∑ k, ∑ b, S b k * (- D b k) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => ?_
          rw [hS k b, hanti b k]
      _ = _ := by simp [mul_neg]
  linarith

end matrix_algebra

section analytic
variable {d : ℕ} {f : Ev d → ℝ} {x : Ev d}

lemma contDiffAt_pderiv (hf : ContDiffAt ℝ 2 f x) (b : Fin d) : ContDiffAt ℝ 1 (pderiv f b) x := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  exact h1.clm_apply contDiffAt_const

lemma pderiv_pderiv_eq (hf : ContDiffAt ℝ 2 f x) (b k : Fin d) :
    pderiv (pderiv f b) k x = fderiv ℝ (fderiv ℝ f) x (Pi.single k 1) (Pi.single b 1) := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x := h1.differentiableAt (by norm_num)
  have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (Pi.single b (1 : ℝ) : Ev d) x)
  rw [pderiv_eq_of_hasFDerivAt (f := pderiv f b) h k]
  simp

lemma pderiv_pderiv_symm (hf : ContDiffAt ℝ 2 f x) (b k : Fin d) :
    pderiv (pderiv f b) k x = pderiv (pderiv f k) b x := by
  rw [pderiv_pderiv_eq hf, pderiv_pderiv_eq hf]
  exact (hf.isSymmSndFDerivAt (by simp)) _ _

/-- **Piola identity**: the columns of the adjugate of the Jacobian of a `C²` map are divergence free. -/
theorem piola_identity (τ : Ev d → Ev d) (x : Ev d) (hτ : ContDiffAt ℝ 2 τ x) (i : Fin d) :
    ∑ k, pderiv (fun y => (jac τ y).adjugate k i) k x = 0 := by
  classical
  have hτa : ∀ a, ContDiffAt ℝ 2 (fun y => τ y a) x := fun a => contDiffAt_pi.1 hτ a
  have hJ : ∀ a b, DifferentiableAt ℝ (fun y => jac τ y a b) x := fun a b =>
    (contDiffAt_pderiv (hτa a) b).differentiableAt (by norm_num)
  -- the matrix field `M k y = J y with row i replaced by eₖ`
  have hM : ∀ (k : Fin d) (a b : Fin d), DifferentiableAt ℝ
      (fun y => ((jac τ y).updateRow i (Pi.single k 1)) a b) x := by
    intro k a b
    by_cases ha : a = i
    · subst ha; simp
    · simpa [Matrix.updateRow_apply, ha] using hJ a b
  have h1 : ∀ k, pderiv (fun y => (jac τ y).adjugate k i) k x =
      ∑ m, ((((jac τ x).updateRow i (Pi.single k 1))).updateRow m
        (fun b => if m = i then 0 else pderiv (fun y => jac τ y m b) k x)).det := by
    intro k
    simp_rw [Matrix.adjugate_apply]
    rw [pderiv_det (fun y => (jac τ y).updateRow i (Pi.single k 1)) x (hM k) k]
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 2
    funext b
    by_cases hm : m = i
    · subst hm
      simp only [Matrix.updateRow_self, ite_true]
      exact pderiv_const _ k
    · simp only [hm, ite_false]
      refine pderiv_congr_eventually (Filter.Eventually.of_forall fun y => ?_) k
      simp [Matrix.updateRow_apply, hm]
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_comm]
  refine Finset.sum_eq_zero fun m _ => ?_
  by_cases hm : m = i
  · subst hm
    refine Finset.sum_eq_zero fun k _ => ?_
    exact Matrix.det_eq_zero_of_row_eq_zero m (fun j => by simp)
  · simp only [hm, ite_false]
    exact antisym_sum (jac τ x) hm (fun b k => pderiv (fun y => jac τ y m b) k x)
      (fun b k => pderiv_pderiv_symm (hτa m) b k)

end analytic

end MarkovTriple.BGL.Instances.Riemannian.R27
