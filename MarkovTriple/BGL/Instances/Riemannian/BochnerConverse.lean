import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.BochnerChecks

/-!
# The converse of the curvature criterion: `Curv ρ ⇒ Ric_g + ∇∇W ≥ ρ g` (BGL (1.16.8), both directions)

BGL Sect. 1.16: for the weighted Riemannian operator, `Γ₂(f) ≥ ρ Γ(f)` for all `f` iff `Ric_g + ∇∇W ≥ ρ g`.
Given `x` and a vector `c = (∂_k f(x))_k`, the polynomial
`f(y) = Σ_k c_k (y_k − x_k) + ½ Σ_{ijk} γ_{ij}^k(x) c_k (y_i − x_i)(y_j − x_j)`
is `C^∞`, has `∂_k f(x) = c_k` and `∇∇f(x) = 0` (the Hessian in the sense of `Curvature.lean`); Bochner's formula
(`riem_bochner`, (1.16.4)) at `x` then reads `Γ₂(f)(x) = (Ric_g + ∇∇W)(∇f, ∇f)`, while `Γ(f)(x) = g^{ij} c_i c_j`.
No hypothesis beyond `Curv ρ` is used: it is stated for all `C^∞` functions, and `f` is polynomial.

* `hessZeroPoly`, `sm_hessZeroPoly`, `pderiv_hessZeroPoly_self`, `hess_hessZeroPoly_self`;
* `riem_ricci_of_curv`: `ρ Σ g_{ij} ξ^iξ^j ≤ Σ (Ric + ∇∇W)_{ij} ξ^iξ^j` for all `x`, `ξ` (`ξ = ∇f(x)`);
* `riem_curv_iff_ricci`: `Curv ρ ↔ Ric_g + ∇∇W ≥ ρ g`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

/-- the Hessian-corrected linear function at `x`: `f(y) = Σ c_k z_k + ½ Σ A_{ij} z_i z_j`, `z = y − x`,
`A_{ij} = Σ_k γ_{ij}^k(x) c_k` -/
noncomputable def hessZeroPoly (x c : Rd d) (y : Rd d) : ℝ :=
  ∑ k, c k * (y k - x k) +
    (1 / 2) * ∑ i, ∑ j, (∑ k, R.chr k i j x * c k) * ((y i - x i) * (y j - x j))

lemma sm_shift (x : Rd d) (i : Fin d) : Sm (fun y : Rd d => y i - x i) :=
  (contDiff_apply ℝ ℝ i).sub contDiff_const

lemma pderiv_shift (x : Rd d) (i m : Fin d) (y : Rd d) :
    pderiv (fun y : Rd d => y i - x i) m y = if m = i then 1 else 0 := by
  rw [pderiv_sub' (contDiff_apply ℝ ℝ i) contDiff_const, pderiv_const, pderiv_coord]
  simp

lemma sm_hessZeroPoly (x c : Rd d) : Sm (R.hessZeroPoly x c) := by
  unfold hessZeroPoly
  exact (ContDiff.sum fun k _ => contDiff_const.mul (sm_shift x k)).add
    (contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
      contDiff_const.mul ((sm_shift x i).mul (sm_shift x j))))

lemma A_symm (x c : Rd d) (i j : Fin d) :
    ∑ k, R.chr k i j x * c k = ∑ k, R.chr k j i x * c k :=
  Finset.sum_congr rfl fun k _ => by rw [R.chr_symm k i j x]

/-- `∂_m f = c_m + Σ_j A_{mj} (y_j − x_j)` -/
lemma pderiv_hessZeroPoly (x c : Rd d) (m : Fin d) (y : Rd d) :
    pderiv (R.hessZeroPoly x c) m y = c m + ∑ j, (∑ k, R.chr k m j x * c k) * (y j - x j) := by
  have hq : ∀ i j, Sm (fun y : Rd d => (∑ k, R.chr k i j x * c k) * ((y i - x i) * (y j - x j))) :=
    fun i j => contDiff_const.mul ((sm_shift x i).mul (sm_shift x j))
  unfold hessZeroPoly
  rw [pderiv_add' (ContDiff.sum fun k _ => contDiff_const.mul (sm_shift x k))
      (contDiff_const.mul (ContDiff.sum fun i _ => ContDiff.sum fun j _ => hq i j)),
    pderiv_sum _ (fun k => contDiff_const.mul (sm_shift x k)),
    pderiv_mul' contDiff_const (ContDiff.sum fun i _ => ContDiff.sum fun j _ => hq i j),
    pderiv_const, zero_mul, zero_add,
    pderiv_sum _ (fun i => ContDiff.sum fun j _ => hq i j)]
  have e1 : ∑ k, pderiv (fun y : Rd d => c k * (y k - x k)) m y = c m := by
    have : ∀ k, pderiv (fun y : Rd d => c k * (y k - x k)) m y = if m = k then c k else 0 := by
      intro k
      rw [pderiv_mul' contDiff_const (sm_shift x k), pderiv_const, pderiv_shift]
      split_ifs <;> simp
    simp [this]
  have e2 : ∀ i, pderiv (fun y : Rd d => ∑ j, (∑ k, R.chr k i j x * c k) * ((y i - x i) * (y j - x j))) m y
      = ∑ j, (∑ k, R.chr k i j x * c k) *
          ((if m = i then 1 else 0) * (y j - x j) + (y i - x i) * (if m = j then 1 else 0)) := by
    intro i
    rw [pderiv_sum _ (fun j => hq i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [pderiv_mul' contDiff_const ((sm_shift x i).mul (sm_shift x j)), pderiv_const, zero_mul,
      zero_add, pderiv_mul' (sm_shift x i) (sm_shift x j), pderiv_shift, pderiv_shift]
  simp only [e1, e2]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib, ite_mul, mul_ite, one_mul, mul_one, mul_zero, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
  have e5 : ∑ i, (∑ k, R.chr k i m x * c k) * (y i - x i) =
      ∑ j, (∑ k, R.chr k m j x * c k) * (y j - x j) :=
    Finset.sum_congr rfl fun i _ => by rw [R.A_symm x c i m]
  rw [e5]; ring

lemma pderiv_hessZeroPoly_self (x c : Rd d) (m : Fin d) : pderiv (R.hessZeroPoly x c) m x = c m := by
  rw [pderiv_hessZeroPoly]; simp

lemma pderiv_pderiv_hessZeroPoly (x c : Rd d) (i j : Fin d) (y : Rd d) :
    pderiv (pderiv (R.hessZeroPoly x c) j) i y = ∑ k, R.chr k j i x * c k := by
  have : pderiv (R.hessZeroPoly x c) j =
      fun y => c j + ∑ l, (∑ k, R.chr k j l x * c k) * (y l - x l) :=
    funext fun y => R.pderiv_hessZeroPoly x c j y
  rw [this, pderiv_add' contDiff_const (ContDiff.sum fun l _ => contDiff_const.mul (sm_shift x l)),
    pderiv_const, zero_add, pderiv_sum _ (fun l => contDiff_const.mul (sm_shift x l))]
  have : ∀ l, pderiv (fun y : Rd d => (∑ k, R.chr k j l x * c k) * (y l - x l)) i y =
      if i = l then ∑ k, R.chr k j l x * c k else 0 := by
    intro l
    rw [pderiv_mul' contDiff_const (sm_shift x l), pderiv_const, pderiv_shift]
    split_ifs <;> simp
  simp [this]

/-- the Hessian of `hessZeroPoly x c` vanishes at `x` -/
lemma hess_hessZeroPoly_self (x c : Rd d) (i j : Fin d) : R.hess (R.hessZeroPoly x c) i j x = 0 := by
  unfold hess
  rw [R.pderiv_pderiv_hessZeroPoly]
  simp only [R.pderiv_hessZeroPoly_self]
  rw [R.A_symm x c j i]; ring

/-- **Converse of (1.16.8)** (BGL Sect. 1.16): `Curv ρ ⇒ Ric_g + ∇∇W ≥ ρ g` at every point, as quadratic forms. -/
theorem riem_ricci_of_curv {ρ : ℝ} (h : R.Curv ρ) (x ξ : Rd d) :
    ρ * ∑ i, ∑ j, R.gl i j x * ξ i * ξ j ≤ ∑ i, ∑ j, R.beRicci i j x * ξ i * ξ j := by
  set c : Rd d := fun k => ∑ s, R.gl k s x * ξ s with hc
  set f := R.hessZeroPoly x c with hfdef
  have hf : Sm f := R.sm_hessZeroPoly x c
  have hgrad : ∀ i, R.grad f i x = ξ i := by
    intro i
    unfold grad
    simp only [hfdef, R.pderiv_hessZeroPoly_self, hc, Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ s, ∑ k, R.g i k x * (R.gl k s x * ξ s) = (if i = s then 1 else 0) * ξ s := by
      intro s
      rw [← R.mat_mul_gl x i s, Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by ring
    simp [this]
  have h1 := h f hf x
  have h2 : R.toEll.diff.ΓA f f x = R.GamF f f x := by rw [R.toEll.ΓA_eq hf hf]; rfl
  have hb : R.toEll.diff.Γ₂ f f x = _ := R.riem_bochner hf x
  rw [hb, h2, R.Gam_eq_gl_grad f x] at h1
  have h3 : ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * R.hess f i j x * R.hess f k l x = 0 := by
    simp [hfdef, R.hess_hessZeroPoly_self]
  simp only [hgrad, h3, zero_add] at h1
  exact h1

/-- **BGL (1.16.8), both directions**: `CD(ρ,∞)` on `C^∞` functions for the weighted Riemannian chart iff
`Ric_g + ∇∇W ≥ ρ g`. -/
theorem riem_curv_iff_ricci {ρ : ℝ} :
    R.Curv ρ ↔ ∀ (x ξ : Rd d), ρ * ∑ i, ∑ j, R.gl i j x * ξ i * ξ j ≤
      ∑ i, ∑ j, R.beRicci i j x * ξ i * ξ j :=
  ⟨fun h x ξ => R.riem_ricci_of_curv h x ξ, fun h => R.riem_curv_of_ricci h⟩

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
