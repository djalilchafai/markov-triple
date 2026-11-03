import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE3C
import MarkovTriple.BGL.Instances.GibbsRd.SobMain

/-!
# E3, part D: core interface for the glue, compatibility `Sobolev ↔ HasSobL2`, non-vacuity of H

Statements: `STATEMENTS_R16_E3.md` (E3.3).  Evans §6.3.1 Thm 3 (infinite differentiability) is the combination of `interior_sobolev` for all
orders with the Sobolev embedding `Sob.smooth_of_weak_all_orders`.
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

/-- the two standalone `WeakDeriv` definitions coincide -/
theorem weakDeriv_iff_sob {f g : Rd d → ℝ} {i : Fin d} : Elliptic.WeakDeriv f g i ↔ Sob.WeakDeriv f g i :=
  Iff.rfl

theorem locL2_iff_sob {f : Rd d → ℝ} : Elliptic.LocL2 f ↔ Sob.LocL2 f := Iff.rfl

/-- compatibility of the two `H^k_loc` predicates -/
theorem sobolev_iff_hasSobL2 : ∀ (k : ℕ) {f : Rd d → ℝ}, Elliptic.Sobolev k f ↔ Sob.HasSobL2 k f
  | 0, _ => Iff.rfl
  | k + 1, f => by
    refine and_congr Iff.rfl (forall_congr' fun i => exists_congr fun g => and_congr Iff.rfl ?_)
    exact sobolev_iff_hasSobL2 k

namespace EllData
variable (E : EllData d)

/-- **E3.3 (core interface)**: if `L u = h` (very weakly) with all `∂^α h ∈ L²_loc`, then `u ∈ H^k_loc` for all `k`. -/
theorem interior_regularity_all_orders {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hW : E.VeryWeakSol u h)
    (hh : ∀ k, Sobolev k h) : ∀ k, Sobolev k u := fun k =>
  Sobolev.mono (Sobolev.mono (E.interior_sobolev k hu hg hgL hW (hh k)))

/-- **E3.3 (smooth representative)**: under the same hypotheses `u` agrees a.e. with a `C^∞` function (Sobolev embedding). -/
theorem interior_smooth_rep {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hW : E.VeryWeakSol u h)
    (hh : ∀ k, Sobolev k h) : ∃ φ : Rd d → ℝ, Sm φ ∧ u =ᵐ[volume] φ :=
  Sob.smooth_of_weak_all_orders fun k => (sobolev_iff_hasSobL2 k).1 (E.interior_regularity_all_orders hu hg hgL hW hh k)

/-- **non-vacuity of H**: a smooth `u` solves `L u = h := L u` in the very weak sense (symmetry of `L` for `w dx`). -/
theorem veryWeakSol_of_smooth {u : Rd d → ℝ} (hu : Sm u) : E.VeryWeakSol u (E.L u) := by
  intro a ha
  obtain ⟨has, hac⟩ := ha
  have m1 := E.ibp_master (f := u) (g := a) hu has (Or.inl hac)
  have m2 := E.ibp_master (f := a) (g := u) has hu (Or.inr hac)
  have c1 : HasCompactSupport (fun x => E.w x * a x * E.L u x) :=
    hcs_of_factor hac fun x hx => by rw [hx]; ring
  have c2 : HasCompactSupport (fun x => E.w x * E.Γ a u x) :=
    hcs_of_factor (E.hcs_Γ_left (g := u) hac) fun x hx => by rw [hx]; ring
  have c3 : HasCompactSupport (fun x => E.w x * u x * E.L a x) :=
    hcs_of_factor (E.hcs_L hac) fun x hx => by rw [hx]; ring
  have c4 : HasCompactSupport (fun x => E.w x * E.Γ u a x) :=
    hcs_of_factor (E.hcs_Γ_right (f := u) hac) fun x hx => by rw [hx]; ring
  have i1 : Integrable (fun x => E.w x * a x * E.L u x) volume :=
    (((E.w_smooth.mul has).mul (E.sm_L hu)).continuous).integrable_of_hasCompactSupport c1
  have i2 : Integrable (fun x => E.w x * E.Γ a u x) volume :=
    ((E.w_smooth.mul (E.sm_Γ has hu)).continuous).integrable_of_hasCompactSupport c2
  have i3 : Integrable (fun x => E.w x * u x * E.L a x) volume :=
    (((E.w_smooth.mul hu).mul (E.sm_L has)).continuous).integrable_of_hasCompactSupport c3
  have i4 : Integrable (fun x => E.w x * E.Γ u a x) volume :=
    ((E.w_smooth.mul (E.sm_Γ hu has)).continuous).integrable_of_hasCompactSupport c4
  rw [integral_add i1 i2] at m1
  rw [integral_add i3 i4] at m2
  have hΓ : ∀ x, E.Γ a u x = E.Γ u a x := fun x => by
    unfold Γ
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [E.a_symm i j x]; ring
  have e : ∫ x, E.w x * E.Γ a u x = ∫ x, E.w x * E.Γ u a x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hΓ x])
  have e1 : ∫ x, u x * E.L a x * E.w x = ∫ x, E.w x * u x * E.L a x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have e2 : ∫ x, E.L u x * a x * E.w x = ∫ x, E.w x * a x * E.L u x :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [e1, e2]
  linarith

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
