import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.Unconditional
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllGibbs

/-!
# `Core2` and the converse of BGL Prop. 3.3.17 for weighted Riemannian charts (R19, Stream A6; target T3)

`R.toEll` is the weighted elliptic datum of `R`, `R.riemFull_unconditional = R.toEll.fullU` (definitionally), so the general
theorems `EllData.ell_core2`, `EllData.ell_mem_domain_of_Γ₂` apply verbatim.  Flat consistency: `ofGibbs`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open MarkovTriple.BGL (FullTriple pderiv)

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

/-- **T3**: `Core2` for the Riemannian Full triple, from `Curv ρ` (any sign) and a cut-off family for `R.toEll`. -/
theorem riem_core2 {ρ : ℝ} (hρ : R.Curv ρ) (hC : R.toEll.CoreCut) : R.riemFull_unconditional.Core2 :=
  R.toEll.ell_core2 hρ hC

/-- **T3**: the unconditional converse of BGL Prop. 3.3.17 for weighted Riemannian charts. -/
theorem riem_mem_domain_of_Γ₂ {ρ : ℝ} (hρ : R.Curv ρ) (hC : R.toEll.CoreCut) {f : Rd d → ℝ}
    (hf : f ∈ R.riemFull_unconditional.A) (hf2 : MemLp f 2 R.toEll.μ)
    (hG : Integrable (FullTriple.G R.riemFull_unconditional f f) R.toEll.μ)
    (hG2 : Integrable (R.riemFull_unconditional.toDiffusionTriple.Γ₂ f f) R.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ R.riemFull_unconditional.toDiffusionTriple.generator.domain,
      ((R.riemFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 R.toEll.μ) :
        Rd d → ℝ) =ᵐ[R.toEll.μ] R.riemFull_unconditional.L f :=
  R.toEll.ell_mem_domain_of_Γ₂ hρ hC hf hf2 hG hG2

end RiemData

/-! ### the flat case `ofGibbs` -/

/-- `CutFamily` depends on `E` only through `Γ` and `L`. -/
lemma EllData.CutFamily.of_same {E E' : EllData d} (hΓ : ∀ f g, E.Γ f g = E'.Γ f g)
    (hL : ∀ f, E.L f = E'.L f) {χ : ℕ → Rd d → ℝ} (h : E'.CutFamily χ) : E.CutFamily χ := by
  refine ⟨h.smooth, h.cs, h.mem, h.eventually_one, ?_⟩
  obtain ⟨K, hK⟩ := h.bound
  refine ⟨K, fun n x => ?_⟩
  have e : E.G2 (χ n) (χ n) x = E'.G2 (χ n) (χ n) x := by
    simp only [EllData.G2, hΓ, hL]
  simp only [hΓ, hL, e]
  exact hK n x

/-- the flat Riemannian chart `ofGibbs G` has `CoreCut` as soon as `G` does (e.g. `BddHess3`). -/
theorem ofGibbs_coreCut (G : GibbsRdData d) (h : G.toEll.CoreCut) : (RiemData.ofGibbs G).toEll.CoreCut := by
  obtain ⟨χ, hχ⟩ := h
  refine ⟨χ, EllData.CutFamily.of_same (fun f g => ?_) (fun f => ?_) hχ⟩
  · rfl
  · exact RiemData.ofGibbs_toEll_L G f

/-- `Curv` is determined by the formula `Γ₂` : transfer along equal `Γ`, `L`. -/
lemma EllData.curv_of_G2 {E : EllData d} {ρ : ℝ}
    (h : ∀ f : Rd d → ℝ, Sm f → ∀ x, ρ * E.Γ f f x ≤ E.G2 f f x) : E.Curv ρ := by
  intro f hf x
  have := h f hf x
  rw [E.ΓA_eq hf hf, E.Γ₂_eq_comb hf]
  have h' : ρ * E.Γ f f x ≤ (E.L (E.Γ f f) x - E.Γ f (E.L f) x - E.Γ (E.L f) f x) / 2 := by
    unfold EllData.G2 at this
    linarith [E.Γ_symm_apply (E.L f) f x]
  exact h'

theorem ofGibbs_curv (G : GibbsRdData d) {ρ : ℝ} (hρ : HessGe G.V ρ) : (RiemData.ofGibbs G).Curv ρ := by
  refine EllData.curv_of_G2 fun f hf x => ?_
  have h := G.toEll.curv_G2 (G.gibbsRd_curv hρ) hf x
  have e1 : (RiemData.ofGibbs G).toEll.Γ f f x = G.toEll.Γ f f x := rfl
  have e2 : (RiemData.ofGibbs G).toEll.G2 f f x = G.toEll.G2 f f x := by
    simp only [EllData.G2, RiemData.ofGibbs_toEll_L G]
    rfl
  rw [e1, e2]
  exact h

/-- **Flat Riemannian case**: `Core2` for `ofGibbs G` (co-metric `δ`) under `BddHess3`, any `ρ`-convex `G`. -/
theorem ofGibbs_core2 (G : GibbsRdData d) (hb : G.BddHess3) : (RiemData.ofGibbs G).riemFull_unconditional.Core2 := by
  obtain ⟨ρ, hρ⟩ := GibbsRdData.BddHess3.hessGe hb
  exact (RiemData.ofGibbs G).riem_core2 (ofGibbs_curv G hρ) (ofGibbs_coreCut G hb.coreCut)

end MarkovTriple.BGL.Instances.Riemannian
