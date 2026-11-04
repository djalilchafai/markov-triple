import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.DirectRiemMain

/-!
# Non-`𝒜₀` instance of the direct converse for `EllData`: `f ≡ 1` (R22, Stream E1, C1)

`EllData.ell_mem_domain_of_Γ₂_direct` (R20, D5) is exercised by the constant function `f ≡ 1 ∉ 𝒜₀` (`d ≥ 1`):
all hypotheses (`f ∈ 𝒜`, `f ∈ L²`, `Γ f, Γ₂ f ∈ L¹`) are discharged and the theorem is applied (not re-derived).
See `STATEMENTS_R22_E1.md`.

## DIFFERENCE FROM BGL
`f ≡ 1` has `Γ = Γ₂ = L f = 0`: the conclusion `1 ∈ 𝒟(L)`, `L 1 = 0` is trivially true in BGL, so this is a (weak) non-vacuity
check of the hypotheses of the direct converse outside `𝒜₀`, not new mathematics.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (FullTriple pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

lemma Γ_const_left (c : ℝ) (g : Rd d → ℝ) : E.Γ (fun _ => c) g = fun _ => 0 := by
  funext x; simp [Γ, pderiv_const]

lemma Γ_const_right (f : Rd d → ℝ) (c : ℝ) : E.Γ f (fun _ => c) = fun _ => 0 := by
  funext x; simp [Γ, pderiv_const]

lemma L_const_fn (c : ℝ) : E.L (fun _ => c) = fun _ => 0 := by
  funext x
  simp [L, pderiv_const]

/-- **C1**: the constant `f ≡ 1` (not in `𝒜₀`) satisfies the hypotheses of `ell_mem_domain_of_Γ₂_direct`; the conclusion holds
with `L 1 = 0`. -/
theorem ell_const_mem_domain_direct {ρ : ℝ} (hρ : E.Curv ρ) :
    ∃ hf2 : MemLp (fun _ : Rd d => (1 : ℝ)) 2 E.μ,
      ∃ hF : hf2.toLp _ ∈ E.fullU.toDiffusionTriple.generator.domain,
      ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp _, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ]
        E.fullU.L (fun _ => (1 : ℝ)) := by
  have hfS : Sm (fun _ : Rd d => (1 : ℝ)) := contDiff_const
  have hf2 : MemLp (fun _ : Rd d => (1 : ℝ)) 2 E.μ := memLp_const 1
  have hG : Integrable (FullTriple.G E.fullU (fun _ : Rd d => (1 : ℝ)) (fun _ => 1)) E.μ := by
    have e : FullTriple.G E.fullU (fun _ : Rd d => (1 : ℝ)) (fun _ => 1) =
        E.Γ (fun _ => 1) (fun _ => 1) := E.ΓA_eq hfS hfS
    rw [e, E.Γ_const_left]
    exact integrable_zero _ _ _
  have hG2 : Integrable (E.fullU.toDiffusionTriple.Γ₂ (fun _ : Rd d => (1 : ℝ)) (fun _ => 1)) E.μ := by
    have e : E.fullU.toDiffusionTriple.Γ₂ (fun _ : Rd d => (1 : ℝ)) (fun _ => 1) =
        fun x => (E.L (E.Γ (fun _ => 1) (fun _ => 1)) x - E.Γ (fun _ => 1) (E.L fun _ => 1) x -
          E.Γ (E.L fun _ => 1) (fun _ => 1) x) / 2 := E.Γ₂_eq_comb hfS
    rw [e, E.Γ_const_left, E.L_const_fn, Γ_const_left, Γ_const_right]
    simp
  exact ⟨hf2, E.ell_mem_domain_of_Γ₂_direct hρ hfS hf2 hG hG2⟩

/-- `L 1 = 0` for the full triple. -/
lemma fullU_L_const_fn : E.fullU.L (fun _ : Rd d => (1 : ℝ)) = 0 := by
  have : E.fullU.L (fun _ : Rd d => (1 : ℝ)) = E.L (fun _ => 1) := rfl
  rw [this, E.L_const_fn]; rfl

end EllData

end MarkovTriple.BGL.Instances.GibbsRd

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd

/-- `hypRiem` (hyperbolic plane, `Curv 1`, no `CoreCut`): the constant `1 ∉ 𝒜₀` in the domain of the generator. -/
theorem hypRiem_const_mem_domain_direct :
    ∃ hf2 : MemLp (fun _ : Rd 2 => (1 : ℝ)) 2 hypRiem.toEll.μ,
      ∃ hF : hf2.toLp _ ∈ hypRiem.toEll.fullU.toDiffusionTriple.generator.domain,
      ((hypRiem.toEll.fullU.toDiffusionTriple.generator ⟨hf2.toLp _, hF⟩ : Lp ℝ 2 hypRiem.toEll.μ) :
        Rd 2 → ℝ) =ᵐ[hypRiem.toEll.μ] hypRiem.toEll.fullU.L (fun _ => (1 : ℝ)) :=
  hypRiem.toEll.ell_const_mem_domain_direct hypRiem.curv

end MarkovTriple.BGL.Instances.Riemannian
