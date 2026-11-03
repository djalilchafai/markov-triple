import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.CurvCov

/-!
# Antisymmetry of the lowered Riemann tensor (BGL App. C.3, p. 507)

`Σ_p g_{sp} R_{ia}{}^p{}_j + Σ_p g_{jp} R_{ia}{}^p{}_s = 0` (the tensor `R_{iasj}` is antisymmetric in `(s, j)`), proved
from the coordinate formulas of `Curvature.lean` (second derivatives of `g_{ij}` and the symmetry of the Christoffel
symbols).  Together with `Σ_j g^{ij} g_{jp} = δ` this identifies the curvature term of Bochner's formula with
`Ric_{ij} = Σ_k R_{ki}{}^k{}_j` ((C.3.1)).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

/-- pair symmetry of `Σ_p Γ_{p,is} γ_{aj}^p` -/
lemma X_symm (i s a j : Fin d) (x : Rd d) :
    ∑ p, R.chr1 p i s x * R.chr p a j x = ∑ p, R.chr1 p a j x * R.chr p i s x := by
  unfold chr
  simp only [Finset.mul_sum]
  sums2s [fun i j => R.g_symm i j x]

lemma pderiv_chr1 (i a j s : Fin d) (x : Rd d) :
    pderiv (R.chr1 s a j) i x = (1 / 2) * (pderiv (pderiv (R.gl j s) a) i x +
      pderiv (pderiv (R.gl a s) j) i x - pderiv (pderiv (R.gl a j) s) i x) := by
  have : R.chr1 s a j = fun y => (1 / 2) * (pderiv (R.gl j s) a y + pderiv (R.gl a s) j y -
      pderiv (R.gl a j) s y) := rfl
  rw [this, pderiv_mul' contDiff_const (((R.sm_gl j s).pderiv a).add ((R.sm_gl a s).pderiv j) |>.sub
    ((R.sm_gl a j).pderiv s)) i x, pderiv_const, zero_mul, zero_add,
    pderiv_sub' (((R.sm_gl j s).pderiv a).add ((R.sm_gl a s).pderiv j)) ((R.sm_gl a j).pderiv s) i x,
    pderiv_add' ((R.sm_gl j s).pderiv a) ((R.sm_gl a s).pderiv j) i x]

lemma gl_dchr (i a j s : Fin d) (x : Rd d) :
    ∑ p, R.gl s p x * pderiv (R.chr p a j) i x =
      pderiv (R.chr1 s a j) i x - ∑ p, pderiv (R.gl s p) i x * R.chr p a j x := by
  have h : R.chr1 s a j = fun y => ∑ p, R.gl s p y * R.chr p a j y :=
    funext fun y => (R.gl_chr s a j y).symm
  rw [h, pderiv_sum _ (fun p => (R.sm_gl s p).mul (R.sm_chr p a j)) i x]
  simp only [pderiv_mul' (R.sm_gl s _) (R.sm_chr _ a j) i x, Finset.sum_add_distrib]
  ring

/-- the lowered Riemann tensor in terms of second derivatives of the metric -/
lemma lowered_riem (i a s j : Fin d) (x : Rd d) :
    ∑ p, R.gl s p x * R.riem i a p j x =
      (1 / 2) * (pderiv (pderiv (R.gl a s) j) i x - pderiv (pderiv (R.gl a j) s) i x -
        pderiv (pderiv (R.gl i s) j) a x + pderiv (pderiv (R.gl i j) s) a x) -
      ∑ p, R.chr1 p i s x * R.chr p a j x + ∑ p, R.chr1 p a s x * R.chr p i j x := by
  unfold riem
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [R.gl_dchr i a j s x, R.gl_dchr a i j s x, R.pderiv_chr1 i a j s x, R.pderiv_chr1 a i j s x]
  have hsym : ∀ p q, pderiv (pderiv (R.gl p q) a) i x = pderiv (pderiv (R.gl p q) i) a x :=
    fun p q => pderiv_symm_fun (R.sm_gl p q) a i ▸ rfl
  have e1 : ∑ p, R.gl s p x * ∑ m, R.chr p i m x * R.chr m a j x =
      ∑ m, R.chr1 s i m x * R.chr m a j x := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← R.gl_chr s i m x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have e2 : ∑ p, R.gl s p x * ∑ m, R.chr p a m x * R.chr m i j x =
      ∑ m, R.chr1 s a m x * R.chr m i j x := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← R.gl_chr s a m x, Finset.sum_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have e3 : ∀ k, ∑ p, pderiv (R.gl s p) k x * R.chr p a j x =
      ∑ p, R.chr1 p k s x * R.chr p a j x + ∑ p, R.chr1 s k p x * R.chr p a j x := by
    intro k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [R.pderiv_gl_chr1 k s p x]; ring
  have e4 : ∀ k, ∑ p, pderiv (R.gl s p) k x * R.chr p i j x =
      ∑ p, R.chr1 p k s x * R.chr p i j x + ∑ p, R.chr1 s k p x * R.chr p i j x := by
    intro k
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [R.pderiv_gl_chr1 k s p x]; ring
  linarith [e1, e2, e3 i, e4 a, hsym j s]

/-- **Antisymmetry** `R_{ia sj} = − R_{ia js}` of the lowered Riemann tensor -/
lemma riem_antisymm (i a s j : Fin d) (x : Rd d) :
    ∑ p, R.gl s p x * R.riem i a p j x + ∑ p, R.gl j p x * R.riem i a p s x = 0 := by
  rw [R.lowered_riem i a s j x, R.lowered_riem i a j s x]
  linarith [R.X_symm i s a j x, R.X_symm a s i j x]

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
