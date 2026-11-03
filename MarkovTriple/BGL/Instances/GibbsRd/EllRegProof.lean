import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.RegReduction
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE3D
import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsEll

/-!
# Proof of `EllData.EllReg` (R16 glue): interior elliptic regularity for every `EllData d`

Chain of `L²(μ)` weak solutions `(1 − L) x_k = x_{k+1}`: Friedrichs (`H¹_loc`), then the interior `H^{k+2}` bootstrap
(`interior_sobolev`), then the Sobolev embedding.  Statements: `STATEMENTS_R16_Glue.md`.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

open Elliptic

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- G1: the `μ`-weak equation is the `VeryWeakSol` equation (`μ = Z⁻¹ w dx`). -/
lemma veryWeakSol_of_mu {u h : Rd d → ℝ}
    (hw : ∀ a ∈ A₀ d, ∫ y, u y * E.L a y ∂E.μ = ∫ y, h y * a y ∂E.μ) : E.VeryWeakSol u h := by
  intro a ha
  have h1 := hw a ha
  rw [E.integral_μ, E.integral_μ] at h1
  have key : ∀ F : Rd d → ℝ, ∫ x, F x * E.w x = E.Z * ∫ x, E.dens x * F x := by
    intro F
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have := E.Z_pos.ne'
    simp only [dens]; field_simp
  rw [key, key, h1]

lemma Sobolev.sub_aux {k : ℕ} {f g : Rd d → ℝ} (hf : Sobolev k f) (hg : Sobolev k g) :
    Sobolev k (fun x => f x - g x) := by
  have := Sobolev.add hf (Sobolev.smooth_mul hg (contDiff_const : Sm (fun _ : Rd d => (-1 : ℝ))))
  simpa [sub_eq_add_neg] using this

/-- G2: regularity along a chain. -/
theorem chain_sobolev {n : ℕ} {x : ℕ → (Rd d → ℝ)} (hx : ∀ k ≤ n, MemLp (x k) 2 E.μ)
    (hW : ∀ k < n, ∀ a ∈ A₀ d, ∫ y, x k y * E.L a y ∂E.μ = ∫ y, (x k y - x (k + 1) y) * a y ∂E.μ) :
    ∀ j k, k + j ≤ n → Sobolev j (x k) := by
  have hV : ∀ k < n, E.VeryWeakSol (x k) (fun y => x k y - x (k + 1) y) := fun k hk =>
    E.veryWeakSol_of_mu (hW k hk)
  have hL : ∀ k ≤ n, LocL2 (x k) := fun k hk => E.locL2_of_memLp (hx k hk)
  have H1 : ∀ k, k + 1 ≤ n → Sobolev 1 (x k) := fun k hk =>
    E.sobolev_one_of_veryWeak (hL k (by omega))
      (Sobolev.sub_aux (k := 0) (hL k (by omega)) (hL (k + 1) hk)) (hV k (by omega))
  have main : ∀ j, (∀ k, k + j ≤ n → Sobolev j (x k)) ∧ (∀ k, k + (j + 1) ≤ n → Sobolev (j + 1) (x k)) := by
    intro j
    induction j with
    | zero => exact ⟨fun k hk => hL k (by omega), fun k hk => H1 k (by omega)⟩
    | succ j ih =>
      refine ⟨ih.2, fun k hk => ?_⟩
      -- Sobolev (j+2) (x k) from Sobolev j (x k), Sobolev j (x (k+1))
      have hS1 : Sobolev 1 (x k) := H1 k (by omega)
      obtain ⟨-, hg⟩ := hS1
      choose g hg1 hg2 using hg
      have hh : Sobolev j (fun y => x k y - x (k + 1) y) :=
        Sobolev.sub_aux (ih.1 k (by omega)) (ih.1 (k + 1) (by omega))
      exact E.interior_sobolev j (hL k (by omega)) hg1 hg2 (hV k (by omega)) hh
  exact fun j k hk => (main j).1 k hk

/-- **G3: interior elliptic regularity for every `EllData d`**. -/
theorem ellReg : E.EllReg := by
  intro m
  refine ⟨m + d, fun x hx hW => ?_⟩
  have hS := E.chain_sobolev hx hW (m + d) 0 (by omega)
  obtain ⟨g, hg, hae⟩ := Sob.sob_contDiff_rep_L2 m ((sobolev_iff_hasSobL2 _).1 hS)
  exact ⟨g, hg, (Measure.AbsolutelyContinuous.ae_eq (withDensity_absolutelyContinuous _ _) hae)⟩

theorem weakHypo_unconditional : E.WeakHypo := E.weakHypo_of_reg E.ellReg
theorem f8_unconditional : E.F8 := E.f8_of_reg E.ellReg

end EllData
end MarkovTriple.BGL.Instances.GibbsRd
