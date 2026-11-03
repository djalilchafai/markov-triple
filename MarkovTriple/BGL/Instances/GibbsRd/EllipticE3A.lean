import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE2E

/-!
# E3, part A: the commutator identity `∂_m(w L a) = Σᵢ ∂ᵢ(Σⱼ Bᵢⱼ ∂ⱼ a) + w L(∂_m a)`, `Bᵢⱼ = ∂_m(w aᵢⱼ)`

Statements: `STATEMENTS_R16_E3.md` (E3.1).  Pure `C^∞` calculus (symmetry of the Hessian); Evans §6.3.1 Thm 2, Step 1.
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- `Bᵢⱼ = ∂_m(w aᵢⱼ)`, the differentiated coefficient `∂_mAᵢⱼ`. -/
noncomputable def Bc (m i j : Fin d) : Rd d → ℝ := pderiv (fun y => E.w y * E.a i j y) m

lemma sm_Bc (m i j : Fin d) : Sm (E.Bc m i j) :=
  Sm.pderiv (f := fun y => E.w y * E.a i j y) (E.w_smooth.mul (E.a_smooth i j)) m

/-- the vector field `Qᵢ(a) = Σⱼ Bᵢⱼ ∂ⱼ a`. -/
noncomputable def Qf (m : Fin d) (a : Rd d → ℝ) (i : Fin d) : Rd d → ℝ :=
  fun y => ∑ j, E.Bc m i j y * pderiv a j y

lemma sm_Qf (m : Fin d) {a : Rd d → ℝ} (ha : Sm a) (i : Fin d) : Sm (E.Qf m a i) :=
  ContDiff.sum fun j _ => (E.sm_Bc m i j).mul (ha.pderiv j)

lemma hcs_Qf (m : Fin d) {a : Rd d → ℝ} (hc : HasCompactSupport a) (i : Fin d) :
    HasCompactSupport (E.Qf m a i) :=
  hcs_sum _ fun j _ => hcs_of_factor (hc.fderiv_apply ℝ (Pi.single j 1)) fun x hx => by
    have : pderiv a j x = 0 := hx
    simp only [this]; ring

/-- `∂_m(Pᵢ a) = Qᵢ a + Pᵢ(∂_m a)`. -/
lemma pderiv_P (m : Fin d) {a : Rd d → ℝ} (ha : Sm a) (i : Fin d) :
    pderiv (E.P a i) m = fun y => E.Qf m a i y + E.P (pderiv a m) i y := by
  funext x
  have e : E.P a i = fun y => ∑ j, (E.w y * E.a i j y) * pderiv a j y := by
    funext y; unfold P; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e, pderiv_sum _ (fun j => (E.w_smooth.mul (E.a_smooth i j)).mul (ha.pderiv j))]
  unfold Qf P
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 := pderiv_mul (E.w_smooth.mul (E.a_smooth i j)) (ha.pderiv j) m x
  have h2 : pderiv (fun y => (E.w y * E.a i j y) * pderiv a j y) m x =
      pderiv ((fun y => E.w y * E.a i j y) * pderiv a j) m x := rfl
  rw [h2, h1, pderiv_symm ha j m x]
  unfold Bc
  ring

/-- `w L f = Σᵢ ∂ᵢ(Pᵢ f)`. -/
lemma w_L_eq (f : Rd d → ℝ) : (fun x => E.w x * E.L f x) = fun x => ∑ i, pderiv (E.P f i) i x := by
  funext x
  rw [L_eq, ← mul_assoc, mul_inv_cancel₀ (E.w_pos x).ne', one_mul]

/-- **commutator identity**: `∂_m(w L a) = Σᵢ ∂ᵢ(Qᵢ a) + w L(∂_m a)` for `a ∈ C^∞`. -/
theorem comm_identity (m : Fin d) {a : Rd d → ℝ} (ha : Sm a) (x : Rd d) :
    pderiv (fun y => E.w y * E.L a y) m x =
      ∑ i, pderiv (E.Qf m a i) i x + E.w x * E.L (pderiv a m) x := by
  have hP : ∀ i, Sm (E.P a i) := fun i => E.sm_P ha i
  rw [E.w_L_eq a, pderiv_sum _ (fun i => (hP i).pderiv i)]
  have e1 : ∀ i, pderiv (pderiv (E.P a i) i) m x = pderiv (pderiv (E.P a i) m) i x := fun i =>
    pderiv_symm (hP i) i m x
  simp only [e1, E.pderiv_P m ha]
  have hQ : ∀ i, Sm (E.Qf m a i) := fun i => E.sm_Qf m ha i
  have hP' : ∀ i, Sm (E.P (pderiv a m) i) := fun i => E.sm_P (ha.pderiv m) i
  have e2 : ∀ i, pderiv (fun y => E.Qf m a i y + E.P (pderiv a m) i y) i x =
      pderiv (E.Qf m a i) i x + pderiv (E.P (pderiv a m) i) i x := fun i => by
    have := pderiv_add (hQ i) (hP' i) i x
    exact this
  simp only [e2, Finset.sum_add_distrib]
  congr 1
  exact (congrFun (E.w_L_eq (pderiv a m)) x).symm

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
