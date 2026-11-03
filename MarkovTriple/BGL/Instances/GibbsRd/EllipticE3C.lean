import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE3B

/-!
# E3, part C: higher interior regularity `h ∈ H^k_loc ⇒ u ∈ H^{k+2}_loc` (induction on `k`)

Statements: `STATEMENTS_R16_E3.md` (E3.2).  Evans §6.3.1 Thm 2: differentiate the equation (`veryWeakSol_deriv`), apply the
`H²` theorem (`interior_H2_sobolev`) to `∂_m u`, whose right-hand side `h'` lies in `H^{k-1}_loc` by `Sobolev.smooth_mul`.
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

namespace Elliptic

lemma Sobolev.finset_sum {ι : Type*} (k : ℕ) (s : Finset ι) {F : ι → Rd d → ℝ}
    (hF : ∀ i ∈ s, Sobolev k (F i)) : Sobolev k (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using Sobolev.of_smooth k (f := fun _ : Rd d => (0 : ℝ)) contDiff_const
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact Sobolev.add (hF j (Finset.mem_insert_self _ _)) (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

end Elliptic

namespace EllData
variable (E : EllData d)

/-- regularity of the new right-hand side: `h' ∈ H^k_loc` when `h, H ∈ H^k`, `gᵢ ∈ H^{k}`, `Gᵢⱼ ∈ H^k`. -/
lemma sobolev_hprime {k : ℕ} (m : Fin d) {h H : Rd d → ℝ} {g : Fin d → Rd d → ℝ}
    {G : Fin d → Fin d → Rd d → ℝ} (hh : Sobolev k h) (hH : Sobolev k H) (hg : ∀ i, Sobolev k (g i))
    (hG : ∀ i j, Sobolev k (G i j)) : Sobolev k (E.hprime m h H g G) := by
  have t1 : Sobolev k (fun x => E.w x * H x) := Sobolev.smooth_mul hH E.w_smooth
  have t2 : Sobolev k (fun x => pderiv E.w m x * h x) := Sobolev.smooth_mul hh (E.w_smooth.pderiv m)
  have t3 : Sobolev k (fun x => ∑ i, ∑ j, (E.Bc m i j x * G i j x + pderiv (E.Bc m i j) j x * g i x)) :=
    Sobolev.finset_sum k _ fun i _ => Sobolev.finset_sum k _ fun j _ =>
      Sobolev.add (Sobolev.smooth_mul (hG i j) (E.sm_Bc m i j))
        (Sobolev.smooth_mul (hg i) ((E.sm_Bc m i j).pderiv j))
  have t4 : Sobolev k (fun x => (-1 : ℝ) * ∑ i, ∑ j, (E.Bc m i j x * G i j x + pderiv (E.Bc m i j) j x * g i x)) :=
    Sobolev.smooth_mul t3 (contDiff_const : Sm (fun _ : Rd d => (-1 : ℝ)))
  have t5 := Sobolev.add (Sobolev.add t1 t2) t4
  have t6 := Sobolev.smooth_mul t5 (E.w_smooth.inv fun x => (E.w_pos x).ne')
  have e : E.hprime m h H g G = fun x => (E.w x)⁻¹ * ((E.w x * H x + pderiv E.w m x * h x) +
      (-1 : ℝ) * ∑ i, ∑ j, (E.Bc m i j x * G i j x + pderiv (E.Bc m i j) j x * g i x)) := by
    funext x; unfold hprime; ring
  rw [e]
  exact t6

include E in
/-- **E3.2** (Evans §6.3.1 Thm 2): `h ∈ H^k_loc` and `L u = h` (very weakly) give `u ∈ H^{k+2}_loc`. -/
theorem interior_sobolev : ∀ (k : ℕ) {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ}, LocL2 u →
    (∀ i, WeakDeriv u (g i) i) → (∀ i, LocL2 (g i)) → E.VeryWeakSol u h → Sobolev k h →
    Sobolev (k + 2) u
  | 0, _, _, _, hu, hg, hgL, hW, hh => E.interior_H2_sobolev hu hg hgL hh hW
  | k + 1, u, h, g, hu, hg, hgL, hW, hh => by
    have hS2 : Sobolev (k + 2) u := interior_sobolev k hu hg hgL hW hh.mono
    obtain ⟨-, hu2⟩ := hS2
    choose g' hg' hgS using hu2
    have hGex := fun i => (hgS i).2
    choose G' hG' hGS using hGex
    refine ⟨hu, fun m => ⟨g' m, hg' m, ?_⟩⟩
    choose H hH hHS using hh.2
    have hkh : Sobolev k h := hh.mono
    have hh' : Sobolev k (E.hprime m h (H m) g' G') :=
      E.sobolev_hprime m hkh (hHS m) (fun i => (hgS i).mono) (fun i j => hGS i j)
    exact interior_sobolev k (hgS m).1 (hG' m) (fun i => (hGS m i).locL2)
      (E.veryWeakSol_deriv m hg' hG' (hH m) hW) hh'

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
