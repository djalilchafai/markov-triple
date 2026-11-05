import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Atlas.Chart3Ops

/-!
# Isometry data of the stereographic chart (Round 29, stream R, R2)

The pulled-back metric of `y ↦ P_b(y)` is `w_S δ`, `w_S = 4/(1+|y|²)²`, and `P_b ⟂ ∂_jP_b`, `|P_b| = 1`.
-/

open MeasureTheory Filter Topology
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.SphereN.Atlas

open MarkovTriple.BGL.Instances.Riemannian.R27
open LebesgueRd (dd)

lemma gram_Fc (j k : Fin 2) (y : Ev 2) :
    ∑ a, pderiv (Fc a) j y * pderiv (Fc a) k y = if j = k then wS y else 0 := by
  have h := one_add_r2_ne y
  have h' : (1 + y 0 ^ 2 + y 1 ^ 2) ≠ 0 := by unfold r2 at h; rwa [← add_assoc] at h
  simp only [Fin.sum_univ_three, pd_Fc0, pd_Fc1, pd_Fc2]
  fin_cases j <;> fin_cases k <;> simp [wS, qf, r2] <;> field_simp <;> ring

lemma dot_Fc (j : Fin 2) (y : Ev 2) : ∑ a, Fc a y * pderiv (Fc a) j y = 0 := by
  have h := one_add_r2_ne y
  have h' : (1 + y 0 ^ 2 + y 1 ^ 2) ≠ 0 := by unfold r2 at h; rwa [← add_assoc] at h
  simp only [Fin.sum_univ_three, pd_Fc0, pd_Fc1, pd_Fc2]
  fin_cases j <;> simp [Fc, qf, r2] <;> field_simp <;> ring

lemma dd_Pc (b : Bool) (a : Fin 3) (j : Fin 2) (y : Ev 2) :
    dd j (fun z => Pc b z a) y = csign b a * pderiv (Fc a) j y := by
  have : (fun z => Pc b z a) = fun z => csign b a * Fc a z := funext fun z => Pc_apply b z a
  rw [this]
  exact pderiv_const_mul _ j

lemma gram_Pc (b : Bool) (j k : Fin 2) (y : Ev 2) :
    ∑ a, dd j (fun z => Pc b z a) y * dd k (fun z => Pc b z a) y = if j = k then wS y else 0 := by
  rw [← gram_Fc]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dd_Pc, dd_Pc]
  have := csign_sq b a
  linear_combination (pderiv (Fc a) j y * pderiv (Fc a) k y) * this

lemma dot_Pc (b : Bool) (j : Fin 2) (y : Ev 2) :
    ∑ a, Pc b y a * dd j (fun z => Pc b z a) y = 0 := by
  rw [← dot_Fc j y]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [dd_Pc, Pc_apply]
  have := csign_sq b a
  linear_combination (Fc a y * pderiv (Fc a) j y) * this

lemma norm_Pc (b : Bool) (y : Ev 2) : ∑ a, Pc b y a ^ 2 = 1 := by
  have := (ptS b y).2
  simpa [Fin.sum_univ_three, Pc] using this

end MarkovTriple.BGL.SphereN.Atlas
