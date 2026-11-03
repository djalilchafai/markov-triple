import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.CurvInv

/-!
# Christoffel symbols, Hessian, Riemann and Ricci tensors of a weighted Riemannian chart (BGL App. C.3)

For `R : RiemData d` (global chart `ℝ^d`, co-metric `g^{ij}`, metric `g_{ij} = (g^{ij})⁻¹`, weight `W`), the coordinate
formulas of the book, as functions `ℝ^d → ℝ`:

* `chr1 q i j := ½ (∂_i g_{jq} + ∂_j g_{iq} − ∂_q g_{ij})` and the Christoffel symbols
  `chr k i j = γ_{ij}^k := Σ_p g^{kp} chr1 p i j` (Thm C.3.2);
* the Hessian `hess u i j = ∂_i∂_j u − Σ_k γ_{ij}^k ∂_k u` (`∇_i w_j = ∂_i w_j − γ_{ij}^k w_k`, `w = du`);
* the Riemann tensor `riem i j k l = R_{ij}{}^k{}_l = ∂_iγ_{jl}^k − ∂_jγ_{il}^k + Σ_p(γ_{ip}^kγ_{jl}^p − γ_{jp}^kγ_{il}^p)`
  (defined by `(∇_i∇_j − ∇_j∇_i) Z^k = R_{ij}{}^k{}_l Z^l`), `ricci i j = Σ_k R_{ki}{}^k{}_j` ((C.3.1)) and the weighted
  Bakry–Émery tensor `beRicci = ricci + hess W`.

First-order identities proved here: symmetry of `γ`, `∂_k g_{pq} = γ_{q,kp} + γ_{p,kq}`, metric compatibility
`∂_k g^{ij} = −Σ_m (γ_{km}^i g^{mj} + γ_{km}^j g^{im})` (`∇ g^{ij} = 0`, Thm C.3.2), `Σ_b γ_{ib}^b = ∂_i log w_g` and the
formula `L u = Σ g^{ij} ∇_i∇_j u − Σ g^{ij} ∂_iW ∂_j u` (the Laplace–Beltrami operator (C.3.3) with (1.11.10)).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

/-- Christoffel symbols of the first kind `½(∂_i g_{jq} + ∂_j g_{iq} − ∂_q g_{ij})` -/
noncomputable def chr1 (q i j : Fin d) (x : Rd d) : ℝ :=
  (1 / 2) * (pderiv (R.gl j q) i x + pderiv (R.gl i q) j x - pderiv (R.gl i j) q x)

/-- **Christoffel symbols** `γ_{ij}^k = ½ Σ_p g^{kp}(∂_i g_{jp} + ∂_j g_{ip} − ∂_p g_{ij})` (BGL Thm C.3.2). -/
noncomputable def chr (k i j : Fin d) (x : Rd d) : ℝ := ∑ p, R.g k p x * R.chr1 p i j x

/-- the Hessian `∇∇u = (∂_i∂_j u − Σ_k γ_{ij}^k ∂_k u)` -/
noncomputable def hess (u : Rd d → ℝ) (i j : Fin d) (x : Rd d) : ℝ :=
  pderiv (pderiv u j) i x - ∑ k, R.chr k i j x * pderiv u k x

/-- the Riemann tensor `R_{ij}{}^k{}_l` -/
noncomputable def riem (i j k l : Fin d) (x : Rd d) : ℝ :=
  pderiv (R.chr k j l) i x - pderiv (R.chr k i l) j x +
    ∑ p, (R.chr k i p x * R.chr p j l x - R.chr k j p x * R.chr p i l x)

/-- the Ricci tensor `Ric_{ij} = Σ_k R_{ki}{}^k{}_j` ((C.3.1)) -/
noncomputable def ricci (i j : Fin d) (x : Rd d) : ℝ := ∑ k, R.riem k i k j x

/-- the weighted Bakry–Émery tensor `Ric_g + ∇∇W` -/
noncomputable def beRicci (i j : Fin d) (x : Rd d) : ℝ := R.ricci i j x + R.hess R.W i j x

lemma sm_chr1 (q i j : Fin d) : Sm (R.chr1 q i j) := by
  unfold chr1
  exact contDiff_const.mul ((((R.sm_gl j q).pderiv i).add ((R.sm_gl i q).pderiv j)).sub
    ((R.sm_gl i j).pderiv q))

lemma sm_chr (k i j : Fin d) : Sm (R.chr k i j) :=
  ContDiff.sum fun p _ => (R.g_smooth k p).mul (R.sm_chr1 p i j)

lemma gl_fun_symm (i j : Fin d) : R.gl i j = R.gl j i := funext fun x => R.gl_symm i j x

lemma chr1_symm (q i j : Fin d) (x : Rd d) : R.chr1 q i j x = R.chr1 q j i x := by
  unfold chr1
  rw [R.gl_fun_symm i j]
  ring

lemma chr_symm (k i j : Fin d) (x : Rd d) : R.chr k i j x = R.chr k j i x := by
  unfold chr
  exact Finset.sum_congr rfl fun p _ => by rw [R.chr1_symm p i j x]

/-- lowering: `Σ_k g_{qk} γ_{ij}^k = chr1 q i j` -/
lemma gl_chr (q i j : Fin d) (x : Rd d) : ∑ k, R.gl q k x * R.chr k i j x = R.chr1 q i j x := by
  unfold chr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ p, ∑ k, R.gl q k x * (R.g k p x * R.chr1 p i j x) =
      (if q = p then 1 else 0) * R.chr1 p i j x := by
    intro p
    rw [← R.gl_mul_mat x q p, Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp only [this]
  simp

/-- `∂_k g_{pq} = γ_{q,kp} + γ_{p,kq}` -/
lemma pderiv_gl_chr1 (k p q : Fin d) (x : Rd d) :
    pderiv (R.gl p q) k x = R.chr1 q k p x + R.chr1 p k q x := by
  unfold chr1
  rw [R.gl_fun_symm k q, R.gl_fun_symm q p, R.gl_fun_symm k p]
  rw [R.gl_fun_symm p q]
  ring

/-- **Metric compatibility** `∇ g^{ij} = 0`: `∂_k g^{ij} = −Σ_m(γ_{km}^i g^{mj} + γ_{km}^j g^{im})` -/
lemma pderiv_g_chr (k i j : Fin d) (x : Rd d) :
    pderiv (R.g i j) k x = -∑ m, (R.chr i k m x * R.g m j x + R.chr j k m x * R.g i m x) := by
  rw [R.pderiv_g_eq]
  simp only [R.pderiv_gl_chr1, mul_add, add_mul, Finset.sum_add_distrib, Finset.sum_add_distrib]
  congr 1
  have hC : ∑ m, R.chr i k m x * R.g m j x =
      ∑ b, ∑ c, R.g i b x * R.chr1 b k c x * R.g c j x := by
    unfold chr
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
  have hD : ∑ m, R.chr j k m x * R.g i m x =
      ∑ b, ∑ c, R.g i b x * R.chr1 c k b x * R.g c j x := by
    unfold chr
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [R.g_symm j c x]; ring
  rw [hC, hD, add_comm]

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
