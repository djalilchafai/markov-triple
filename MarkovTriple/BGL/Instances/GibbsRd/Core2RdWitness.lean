import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdExample

/-!
# The `ℝ^d` `Core2` theorem and converse hold for concrete `ρ > 0` potentials (R18, Stream A3, B6)

`gaussData d` (`V = |x|²/2`, `ρ = 1`) and the non-Gaussian `cosData d` (`V = |x|²/2 + cos(x₀)/2`, `ρ = 1/2`): both have
`BddHess3` and `Hess V ≥ ρ > 0` (so `∇V` is unbounded), hence `Core2` and the unconditional converse of BGL Prop. 3.3.17.
-/

open MeasureTheory

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (FullTriple)

theorem gaussData_core2 (d : ℕ) : (gaussData d).gibbsRdFull_unconditional.Core2 :=
  (gaussData d).gibbsRd_core2 (gaussData_bddHess3 d)

theorem cosData_core2 (d : ℕ) : (cosData d).gibbsRdFull_unconditional.Core2 :=
  (cosData d).gibbsRd_core2 (cosData_bddHess3 d)

/-- the converse of Prop. 3.3.17 for the non-Gaussian `ρ = 1/2 > 0` potential `|x|²/2 + cos(x₀)/2`. -/
theorem cosData_mem_domain_of_Γ₂ (d : ℕ) {f : Rd (d + 1) → ℝ}
    (hf : f ∈ (cosData d).gibbsRdFull_unconditional.A) (hf2 : MemLp f 2 (cosData d).toEll.μ)
    (hG : Integrable (FullTriple.G (cosData d).gibbsRdFull_unconditional f f) (cosData d).toEll.μ)
    (hG2 : Integrable ((cosData d).gibbsRdFull_unconditional.toDiffusionTriple.Γ₂ f f) (cosData d).toEll.μ) :
    ∃ hF : hf2.toLp f ∈ (cosData d).gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      (((cosData d).gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 (cosData d).toEll.μ) : Rd (d + 1) → ℝ) =ᵐ[(cosData d).toEll.μ]
        (cosData d).gibbsRdFull_unconditional.L f :=
  (cosData d).gibbsRd_mem_domain_of_Γ₂ (cosData_bddHess3 d) (hessGe_cosV d) hf hf2 hG hG2

/-- the same for the standard Gaussian (`ρ = 1`). -/
theorem gaussData_mem_domain_of_Γ₂ (d : ℕ) {f : Rd d → ℝ}
    (hf : f ∈ (gaussData d).gibbsRdFull_unconditional.A) (hf2 : MemLp f 2 (gaussData d).toEll.μ)
    (hG : Integrable (FullTriple.G (gaussData d).gibbsRdFull_unconditional f f) (gaussData d).toEll.μ)
    (hG2 : Integrable ((gaussData d).gibbsRdFull_unconditional.toDiffusionTriple.Γ₂ f f)
      (gaussData d).toEll.μ) :
    ∃ hF : hf2.toLp f ∈ (gaussData d).gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      (((gaussData d).gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 (gaussData d).toEll.μ) : Rd d → ℝ) =ᵐ[(gaussData d).toEll.μ]
        (gaussData d).gibbsRdFull_unconditional.L f :=
  (gaussData d).gibbsRd_mem_domain_of_Γ₂ (gaussData_bddHess3 d) hessGe_gauss hf hf2 hG hG2

end MarkovTriple.BGL.Instances.GibbsRd
