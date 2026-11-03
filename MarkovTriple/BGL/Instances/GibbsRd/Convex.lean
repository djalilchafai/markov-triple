import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Bochner
import MarkovTriple.BGL.Instances.Gibbs.Convex
import MarkovTriple.BGL.Instances.Gibbs.Calculus

/-!
# Uniformly convex potentials on `ℝ^d`: `e^{-V}` is integrable; `Hess V ≥ ρ ⇒ Curv ρ`; the Gaussian case

`HessGe V ρ` is `Hess V ≥ ρ`: `∀ x v, ρ Σ vᵢ² ≤ Σᵢⱼ ∂ⱼ∂ᵢV(x) vᵢ vⱼ`.

* `quad_lower_rd`: `V(x) ≥ V(0) + ∇V(0)·x + ρ|x|²/2` (restriction to the ray `t ↦ t x` and the one-dimensional
  `Gibbs.quad_lower`), hence `e^{-V}` is dominated by a Gaussian: `integrable_of_convex_rd` (non-vacuity of
  `GibbsRdData`), `ofConvex`.
* `gibbsRd_curv` (proved in `GibbsRd/Main.lean`): `HessGe V ρ ⇒ Curv ρ` (pointwise `Γ₂ ≥ ρ Γ` for the Gibbs triple, from the Bochner identity).
* `gaussData d`: `V = |x|²/2`, `Hess V = I`, the standard Gaussian on `ℝ^d`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv pderiv₂ DiffusionTriple)

variable {d : ℕ}

/-- `Hess V ≥ ρ` -/
def HessGe (V : Rd d → ℝ) (ρ : ℝ) : Prop :=
  ∀ (x v : Rd d), ρ * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, pderiv (pderiv V i) j x * v i * v j

section ray
variable {g : Rd d → ℝ}

lemma hasDerivAt_ray (hg : Sm g) (x : Rd d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => g (s • x)) (∑ i, x i * pderiv g i (t • x)) t := by
  have h1 : HasDerivAt (fun s : ℝ => s • x) x t := by
    simpa using (hasDerivAt_id t).smul_const x
  have h2 := (hg.hasFDerivAt' (t • x)).comp_hasDerivAt t h1
  refine h2.congr_deriv ?_
  rw [MarkovTriple.Sanity.OU.clm_pi_apply]
  rfl

lemma sm_ray (hg : Sm g) (x : Rd d) : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => g (s • x)) :=
  hg.comp (contDiff_id.smul contDiff_const)

lemma deriv_ray (hg : Sm g) (x : Rd d) :
    deriv (fun s : ℝ => g (s • x)) = fun t => ∑ i, x i * pderiv g i (t • x) :=
  funext fun t => (hasDerivAt_ray hg x t).deriv

lemma deriv_deriv_ray (hg : Sm g) (x : Rd d) (t : ℝ) :
    deriv (deriv (fun s : ℝ => g (s • x))) t =
      ∑ i, ∑ j, pderiv (pderiv g i) j (t • x) * x i * x j := by
  rw [deriv_ray hg x]
  have : ∀ i, HasDerivAt (fun s : ℝ => x i * pderiv g i (s • x))
      (x i * ∑ j, x j * pderiv (pderiv g i) j (t • x)) t := fun i =>
    (hasDerivAt_ray (hg.pderiv i) x t).const_mul (x i)
  have h := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => this i)
  rw [h.deriv]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

end ray

/-- quadratic lower bound `V(x) ≥ V(0) + ∇V(0)·x + ρ|x|²/2` from `Hess V ≥ ρ`. -/
lemma quad_lower_rd {V : Rd d → ℝ} (hV : Sm V) {ρ : ℝ} (hρ : HessGe V ρ) (x : Rd d) :
    V 0 + ∑ i, pderiv V i 0 * x i + ρ * qd x / 2 ≤ V x := by
  have hφ : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => V (s • x)) := sm_ray hV x
  have hge : ∀ t : ℝ, ρ * qd x ≤ deriv (deriv (fun s : ℝ => V (s • x))) t := by
    intro t
    rw [deriv_deriv_ray hV x t]
    exact hρ (t • x) x
  have key := MarkovTriple.BGL.Instances.Gibbs.quad_lower (V := fun s : ℝ => V (s • x))
    hφ (ρ := ρ * qd x) hge 1
  have e0 : deriv (fun s : ℝ => V (s • x)) 0 = ∑ i, x i * pderiv V i 0 := by
    rw [deriv_ray hV x]; simp
  rw [e0] at key
  simp only [zero_smul, one_smul] at key
  have e1 : ∑ i, pderiv V i 0 * x i = ∑ i, x i * pderiv V i 0 :=
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [e1]
  nlinarith [key]

/-- `e^{-V}` is integrable for `Hess V ≥ ρ > 0`. -/
lemma integrable_of_convex_rd {V : Rd d → ℝ} (hV : Sm V) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : HessGe V ρ) : Integrable (fun x => Real.exp (-V x)) volume := by
  set a : Fin d → ℝ := fun i => pderiv V i 0
  set C := Real.exp (-V 0 + ∑ i, a i ^ 2 / ρ)
  have hg : Integrable (fun x : Rd d => C * ∏ i, Real.exp (-(ρ / 4) * x i ^ 2)) volume := by
    refine Integrable.const_mul ?_ C
    exact Integrable.fintype_prod (f := fun (_ : Fin d) (v : ℝ) => Real.exp (-(ρ / 4) * v ^ 2))
      (fun _ => by simpa [neg_mul] using integrable_exp_neg_mul_sq (by positivity : 0 < ρ / 4))
  refine Integrable.mono' hg (Real.continuous_exp.comp hV.continuous.neg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_sum]
  simp only [C]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := quad_lower_rd hV hρ x
  have h2 : ∀ i, -(a i * x i) - ρ * x i ^ 2 / 4 ≤ a i ^ 2 / ρ := by
    intro i
    have : 0 ≤ (ρ / 4) * (x i + 2 * a i / ρ) ^ 2 := by positivity
    have e : (ρ / 4) * (x i + 2 * a i / ρ) ^ 2 = ρ * x i ^ 2 / 4 + a i * x i + a i ^ 2 / ρ := by
      field_simp; ring
    linarith
  have h3 : ∑ i, (-(a i * x i) - ρ * x i ^ 2 / 4) ≤ ∑ i, a i ^ 2 / ρ :=
    Finset.sum_le_sum fun i _ => h2 i
  have h4 : ∑ i, (-(a i * x i) - ρ * x i ^ 2 / 4) = -∑ i, a i * x i - ρ * qd x / 4 := by
    have : ρ * qd x / 4 = ∑ i, ρ * x i ^ 2 / 4 := by
      unfold qd; rw [Finset.mul_sum, Finset.sum_div]
    rw [this, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have h5 : ∑ i, -(ρ / 4) * x i ^ 2 = -(ρ / 4) * qd x := by
    unfold qd; rw [Finset.mul_sum]
  rw [h5]
  have : ρ * qd x / 4 ≤ ρ * qd x / 2 := by
    have := qd_nonneg x; nlinarith
  linarith

end MarkovTriple.BGL.Instances.GibbsRd
