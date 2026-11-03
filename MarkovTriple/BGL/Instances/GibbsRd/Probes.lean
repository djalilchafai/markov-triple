import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Main

/-!
# Self-audit probes for `GibbsRd` (Armstrong method (b): attack the statements)

* `gauss_not_curv_two`: the curvature hypothesis `Curv ρ` is *not* trivially true: for the standard Gaussian on
  `ℝ^d` (`d ≥ 1`) `Curv 2` is false, witnessed by the coordinate function `f(x) = x₀` (`Γ f = 1`,
  `Γ₂ f = Hess V(e₀,e₀) = 1`), so the constant `ρ = 1` of `gaussData_curv` is sharp and the Bochner identity
  `gibbsRd_Γ₂_eq` is not an empty identity (it is evaluated on a function with `‖Hess f‖ = 0` and nonzero `∇f`).
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

lemma pderiv_pderiv_coord {d : ℕ} (i0 i j : Fin d) (x : Rd d) :
    pderiv (pderiv (fun y : Rd d => y i0) i) j x = 0 := by
  have : pderiv (fun y : Rd d => y i0) i = fun _ => (if i = i0 then (1 : ℝ) else 0) :=
    funext fun y => pderiv_coord i0 i y
  rw [this]
  exact pderiv_const _ j x

/-- sharpness of the Gaussian curvature: `Curv 2` fails for `N(0, I_d)`, `d ≥ 1`. -/
theorem gauss_not_curv_two (d : ℕ) [NeZero d] : ¬ (gaussData d).toEll.Curv 2 := by
  intro h
  set i0 : Fin d := 0 with hi0
  have hf : Sm (fun y : Rd d => y i0) := contDiff_apply ℝ ℝ i0
  have h0 := h _ hf 0
  have e1 : (gaussData d).toEll.diff.ΓA (fun y : Rd d => y i0) (fun y : Rd d => y i0) 0 = 1 := by
    rw [(gaussData d).toEll.ΓA_eq hf hf, (gaussData d).toEll_Γ]
    simp [Gr, pderiv_coord]
  have e2 : (gaussData d).toEll.diff.Γ₂ (fun y : Rd d => y i0) (fun y : Rd d => y i0) 0 = 1 := by
    have := (gaussData d).gibbsRd_Γ₂_eq hf 0
    have hV : (gaussData d).V = fun x : Rd d => qd x / 2 := rfl
    rw [show (gaussData d).toEll.diff.Γ₂ (fun y : Rd d => y i0) (fun y : Rd d => y i0) 0 =
      (gaussData d).gibbsRdDiff.Γ₂ (fun y : Rd d => y i0) (fun y : Rd d => y i0) 0 from rfl, this]
    simp only [pderiv_pderiv_coord, hV, hess_gauss, pderiv_coord]
    simp
  rw [e1, e2] at h0
  norm_num at h0

end MarkovTriple.BGL.Instances.GibbsRd
