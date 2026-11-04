import Mathlib
import MarkovTriple.BGL.Frozen.PartialDeriv

/-!
# Coordinate invariance of the carré du champ under a change of chart (BGL Appendix C.3)

If `τ` is a transition map and the co-metrics are related by the pushforward `g_b(τ x) = J g_a(x) Jᵀ`
(`J = Dτ`), then `Γ_b(F,H)(τ x) = Γ_a(F∘τ, H∘τ)(x)`.  Chain rule only (any dimension `d`).
-/

namespace MarkovTriple.BGL.Instances.Riemannian.R26

open MarkovTriple.BGL (pderiv)

/-- a linear functional on `ℝ^d` is the sum of its partial derivatives weighted by the components -/
lemma clm_apply_eq_sum {d : ℕ} (l : (Fin d → ℝ) →L[ℝ] ℝ) (v : Fin d → ℝ) :
    l v = ∑ i, v i * l (Pi.single i 1) := by
  conv_lhs => rw [pi_eq_sum_univ v]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  funext j
  rcases eq_or_ne j i with h | h
  · subst h; simp
  · simp [h, Ne.symm h]

lemma pderiv_comp_eq {d : ℕ} (τ : (Fin d → ℝ) → (Fin d → ℝ)) (F : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (hτ : DifferentiableAt ℝ τ x) (hF : DifferentiableAt ℝ F (τ x)) (k : Fin d) :
    pderiv (F ∘ τ) k x = ∑ i, pderiv F i (τ x) * pderiv (fun y => τ y i) k x := by
  unfold pderiv
  rw [fderiv_comp x hF hτ]
  simp only [ContinuousLinearMap.comp_apply]
  rw [clm_apply_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
  congr 1
  have hi : DifferentiableAt ℝ (fun y => τ y i) x := (differentiableAt_pi.1 hτ) i
  have : fderiv ℝ (fun y => τ y i) x = (ContinuousLinearMap.proj i).comp (fderiv ℝ τ x) := by
    have h := (hasFDerivAt_apply i (τ x)).comp x hτ.hasFDerivAt
    exact h.fderiv
  rw [this]; rfl

/-- **H1.** Coordinate invariance of `Γ` under a change of chart (any dimension). -/
theorem gamma_chart_change {d : ℕ} (ga gb : Fin d → Fin d → (Fin d → ℝ) → ℝ)
    (τ : (Fin d → ℝ) → (Fin d → ℝ)) (F H : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ)
    (hτ : DifferentiableAt ℝ τ x) (hF : DifferentiableAt ℝ F (τ x)) (hH : DifferentiableAt ℝ H (τ x))
    (hg : ∀ i j, gb i j (τ x) = ∑ k, ∑ l, pderiv (fun y => τ y i) k x * ga k l x *
      pderiv (fun y => τ y j) l x) :
    ∑ i, ∑ j, gb i j (τ x) * pderiv F i (τ x) * pderiv H j (τ x) =
      ∑ k, ∑ l, ga k l x * pderiv (F ∘ τ) k x * pderiv (H ∘ τ) l x := by
  simp only [pderiv_comp_eq τ F x hτ hF, pderiv_comp_eq τ H x hτ hH, hg]
  simp only [Finset.sum_mul, Finset.mul_sum]
  -- reorder the four-fold sums
  have e : ∀ (i j k l : Fin d), pderiv (fun y => τ y i) k x * ga k l x * pderiv (fun y => τ y j) l x *
        pderiv F i (τ x) * pderiv H j (τ x) =
      ga k l x * (pderiv F i (τ x) * pderiv (fun y => τ y i) k x) *
        (pderiv H j (τ x) * pderiv (fun y => τ y j) l x) := fun i j k l => by ring
  simp only [e]
  calc _ = ∑ i, ∑ k, ∑ j, ∑ l, _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ k, ∑ l, ∑ j, _ :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ l, ∑ j, _ := Finset.sum_comm
    _ = ∑ k, ∑ l, ∑ i, ∑ j, _ := Finset.sum_congr rfl fun k _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => Finset.sum_comm
