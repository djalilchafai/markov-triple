import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.CurvRiem
import MarkovTriple.BGL.Instances.Riemannian.Main

/-!
# Bochner's formula for a weighted Riemannian chart with variable co-metric (BGL (1.16.4), Thm C.3.3)

For `R : RiemData d` and every `C^∞` function `f`, at every point `x`,
`Γ₂(f) = ‖∇∇f‖²_HS + (Ric_g + ∇∇W)(∇f, ∇f)`,
where `Γ₂ = R.riemDiff.Γ₂ f f = ½ (L Γ(f) − 2 Γ(f, Lf))` is the formula-defined iterated carré du champ of the library, and
`∇∇f = hess f`, `Ric = ricci`, `∇∇W = hess W` are the coordinate formulas of `Curvature.lean`
(Christoffel symbols of Thm C.3.2, `Ric_{ij} = R_{ki}{}^k{}_j` (C.3.1)).  Consequently
`riem_curv_of_ricci`: `Ric_g + ∇∇W ≥ ρ g` implies `Curv ρ` (BGL (1.16.8)).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

/-- the gradient `∇^i f = Σ_k g^{ik} ∂_k f` -/
noncomputable def grad (f : Rd d → ℝ) (i : Fin d) (x : Rd d) : ℝ := ∑ k, R.g i k x * pderiv f k x

/-- `∂_p f = Σ_s g_{ps} ∇^s f` -/
lemma pderiv_eq_gl_grad (f : Rd d → ℝ) (p : Fin d) (x : Rd d) :
    pderiv f p x = ∑ s, R.gl p s x * R.grad f s x := by
  unfold grad
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  have : ∀ k, ∑ s, R.gl p s x * (R.g s k x * pderiv f k x) =
      (if p = k then 1 else 0) * pderiv f k x := by
    intro k
    rw [← R.gl_mul_mat x p k, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp only [this]
  simp

/-- `Σ_{ij} g^{ij} (−Σ_p R_{ia}{}^p{}_j g_{ps}) = Ric_{as}` -/
lemma curv_inner (a s : Fin d) (x : Rd d) :
    ∑ i, ∑ j, R.g i j x * (-∑ p, R.riem i a p j x * R.gl p s x) = R.ricci a s x := by
  have h1 : ∀ i j, -∑ p, R.riem i a p j x * R.gl p s x = ∑ p, R.gl j p x * R.riem i a p s x := by
    intro i j
    have := R.riem_antisymm i a s j x
    have e : ∑ p, R.riem i a p j x * R.gl p s x = ∑ p, R.gl s p x * R.riem i a p j x :=
      Finset.sum_congr rfl fun p _ => by rw [R.gl_symm p s x]; ring
    linarith
  simp only [h1]
  unfold ricci
  have : ∀ i, ∑ j, R.g i j x * ∑ p, R.gl j p x * R.riem i a p s x = R.riem i a i s x := by
    intro i
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have : ∀ p, ∑ j, R.g i j x * (R.gl j p x * R.riem i a p s x) =
        (if i = p then 1 else 0) * R.riem i a p s x := by
      intro p
      rw [← R.mat_mul_gl x i p, Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp only [this]
    simp
  simp only [this]

/-- the curvature part of Bochner's identity: `Σ_{ab} g^{ab} f_b Σ_{ij} g^{ij}(−Σ_p R_{ia}{}^p{}_j f_p) = Ric(∇f,∇f)` -/
lemma curv_part (f : Rd d → ℝ) (x : Rd d) :
    ∑ a, ∑ b, R.g a b x * pderiv f b x *
        ∑ i, ∑ j, R.g i j x * (-∑ p, R.riem i a p j x * pderiv f p x) =
      ∑ a, ∑ s, R.ricci a s x * R.grad f a x * R.grad f s x := by
  have hY : ∀ a, ∑ i, ∑ j, R.g i j x * (-∑ p, R.riem i a p j x * pderiv f p x) =
      ∑ s, R.ricci a s x * R.grad f s x := by
    intro a
    have e : ∑ i, ∑ j, R.g i j x * (-∑ p, R.riem i a p j x * pderiv f p x) =
        ∑ s, (∑ i, ∑ j, R.g i j x * (-∑ p, R.riem i a p j x * R.gl p s x)) * R.grad f s x := by
      simp only [R.pderiv_eq_gl_grad f, Finset.mul_sum, Finset.sum_mul, mul_neg, neg_mul,
        Finset.sum_neg_distrib, mul_assoc]
      congr 1
      sums4
    rw [e]
    exact Finset.sum_congr rfl fun s _ => by rw [R.curv_inner a s x]
  simp only [hY]
  have : ∀ a, ∑ b, R.g a b x * pderiv f b x = R.grad f a x := fun a => rfl
  have e2 : ∀ a, ∑ b, R.g a b x * pderiv f b x * ∑ s, R.ricci a s x * R.grad f s x =
      R.grad f a x * ∑ s, R.ricci a s x * R.grad f s x := by
    intro a; rw [← Finset.sum_mul, this a]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [e2 a, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Bochner–Lichnerowicz formula** (BGL (1.16.4), Thm C.3.3) for the weighted Riemannian chart:
`Γ₂(f) = ‖∇∇f‖²_HS + (Ric_g + ∇∇W)(∇f,∇f)` for every `C^∞` function `f`, everywhere. -/
theorem riem_bochner {f : Rd d → ℝ} (hf : Sm f) (x : Rd d) :
    R.riemDiff.Γ₂ f f x =
      ∑ i, ∑ j, ∑ k, ∑ l, R.g i k x * R.g j l x * R.hess f i j x * R.hess f k l x +
      ∑ i, ∑ j, R.beRicci i j x * R.grad f i x * R.grad f j x := by
  have h0 : R.riemDiff.Γ₂ f f x = (R.toEll.L (R.toEll.Γ f f) x - R.toEll.Γ f (R.toEll.L f) x -
      R.toEll.Γ (R.toEll.L f) f x) / 2 := congrFun (R.toEll.Γ₂_eq_comb hf) x
  have hLG : R.toEll.L (R.toEll.Γ f f) x = ∑ i, ∑ j, R.g i j x * R.hess (R.GamF f f) i j x -
      ∑ i, ∑ j, R.g i j x * pderiv R.W i x * pderiv (R.GamF f f) j x :=
    R.L_eq_hess (R.sm_GamF hf hf) x
  have hQ : R.toEll.Γ f (R.toEll.L f) x = ∑ k, ∑ l, R.g k l x * pderiv f k x *
      pderiv (R.toEll.L f) l x := rfl
  have hQ' : R.toEll.Γ (R.toEll.L f) f x = ∑ k, ∑ l, R.g k l x * pderiv f k x *
      pderiv (R.toEll.L f) l x := by
    show ∑ k, ∑ l, R.g k l x * pderiv (R.toEll.L f) k x * pderiv f l x = _
    sums2s [fun i j => R.g_symm i j x]
  rw [h0, hLG, hQ, hQ']
  simp only [R.hess_GamF hf, R.pderiv_GamF_self hf, R.pderiv_L hf]
  have key := alg_assemble (fun i j => R.g i j x) (fun i j => R.hess f i j x)
    (fun i j => R.hess R.W i j x) (fun i j a => R.cov3 f i j a x) (fun i => pderiv f i x)
    (fun i => pderiv R.W i x) (fun i j => R.g_symm i j x) (fun i j => R.hess_symm hf i j x)
  beta_reduce at key
  have hT : ∀ a i j, R.cov3 f i j a x - R.cov3 f a i j x = -∑ p, R.riem i a p j x * pderiv f p x := by
    intro a i j
    rw [R.cov3_symm hf i j a x]
    exact R.cov3_ricci hf i a j x
  simp only [hT] at key
  rw [R.curv_part f x] at key
  have h3 : ∑ k, ∑ l, ∑ i, ∑ j, R.g k l x * pderiv f k x * R.g i j x * R.hess R.W l i x *
      pderiv f j x = ∑ i, ∑ j, R.hess R.W i j x * R.grad f i x * R.grad f j x := by
    simp only [grad, Finset.mul_sum, Finset.sum_mul]
    sums4s [fun i j => R.g_symm i j x]
  have h4 : ∑ i, ∑ j, R.beRicci i j x * R.grad f i x * R.grad f j x =
      ∑ a, ∑ s, R.ricci a s x * R.grad f a x * R.grad f s x +
        ∑ i, ∑ j, R.hess R.W i j x * R.grad f i x * R.grad f j x := by
    unfold beRicci
    simp only [add_mul, Finset.sum_add_distrib]
  rw [h4, ← h3]
  linarith [key]

end RiemData

end MarkovTriple.BGL.Instances.Riemannian
