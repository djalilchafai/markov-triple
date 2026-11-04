import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.DirectMain
import MarkovTriple.BGL.Instances.Gibbs.Core2PolyExample
import MarkovTriple.BGL.Instances.Gibbs.Core2WExample

/-!
# The direct converse applied to the earlier witnesses (R20, Stream D1)

The potentials `exp(x²)` (R19), `x⁴/4 + x²/2` (R18), `cos`-type (R17) satisfy `V'' ≥ ρ`; the direct theorem applies to them using ONLY
that convexity statement (`expGibbs_convex`, `quarGibbs_convex`, `cosGibbs_convex`), without `PolyHess`, `GrowHess`, `BddJet`, `Core2`.

## DIFFERENCE FROM BGL

Same as `DirectMain.lean`: BGL's route needs the core of `L²` (`Core2`); these corollaries use ESA of `L` and the cut-off Γ₂ identity
(Caccioppoli, BGL Prop. 3.2.1 technique) instead, so no growth lemma enters.
-/

open MeasureTheory
open MarkovTriple.BGL (FullTriple)

namespace MarkovTriple.BGL.Instances.Gibbs

/-- `V = exp(x²)`, `ρ = 2`: direct route, only `expGibbs_convex` used. -/
theorem expGibbs_mem_domain_of_Γ₂_direct {f : ℝ → ℝ} (hf : f ∈ expGibbs.gibbsFull_unconditional.A)
    (hf2 : MemLp f 2 expGibbs.μ)
    (hG : Integrable (FullTriple.G expGibbs.gibbsFull_unconditional f f) expGibbs.μ)
    (hG2 : Integrable (expGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) expGibbs.μ) :
    ∃ hF : hf2.toLp f ∈ expGibbs.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((expGibbs.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 expGibbs.μ) : ℝ → ℝ) =ᵐ[expGibbs.μ] expGibbs.gibbsFull_unconditional.L f :=
  expGibbs.gibbs_mem_domain_of_Γ₂_direct expGibbs_convex hf hf2 hG hG2

/-- `V = x⁴/4 + x²/2`-type, `ρ = 1`: direct route. -/
theorem quarGibbs_mem_domain_of_Γ₂_direct {f : ℝ → ℝ} (hf : f ∈ quarGibbs.gibbsFull_unconditional.A)
    (hf2 : MemLp f 2 quarGibbs.μ)
    (hG : Integrable (FullTriple.G quarGibbs.gibbsFull_unconditional f f) quarGibbs.μ)
    (hG2 : Integrable (quarGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) quarGibbs.μ) :
    ∃ hF : hf2.toLp f ∈ quarGibbs.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((quarGibbs.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 quarGibbs.μ) : ℝ → ℝ) =ᵐ[quarGibbs.μ] quarGibbs.gibbsFull_unconditional.L f :=
  quarGibbs.gibbs_mem_domain_of_Γ₂_direct quarGibbs_convex hf hf2 hG hG2

/-- the `cos`-perturbed quadratic, `ρ = 1/2`: direct route. -/
theorem cosGibbs_mem_domain_of_Γ₂_direct {f : ℝ → ℝ} (hf : f ∈ cosGibbs.gibbsFull_unconditional.A)
    (hf2 : MemLp f 2 cosGibbs.μ)
    (hG : Integrable (FullTriple.G cosGibbs.gibbsFull_unconditional f f) cosGibbs.μ)
    (hG2 : Integrable (cosGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) cosGibbs.μ) :
    ∃ hF : hf2.toLp f ∈ cosGibbs.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((cosGibbs.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 cosGibbs.μ) : ℝ → ℝ) =ᵐ[cosGibbs.μ] cosGibbs.gibbsFull_unconditional.L f :=
  cosGibbs.gibbs_mem_domain_of_Γ₂_direct cosGibbs_convex hf hf2 hG hG2

end MarkovTriple.BGL.Instances.Gibbs
