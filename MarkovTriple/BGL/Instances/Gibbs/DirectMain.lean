import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.DirectCore
import MarkovTriple.BGL.Instances.Gibbs.RegMain
import MarkovTriple.BGL.Theory.Extension.ClosedIdent

/-!
# Gibbs on `ℝ`: the converse of BGL Prop. 3.3.17 with only `V'' ≥ ρ` — no `Core2`, no growth hypothesis (R20, Stream D1)

Statements: `STATEMENTS_R20_Direct.md` (D1-1).

## DIFFERENCE FROM BGL

BGL (Prop. 3.3.17, p. 161-162) proves the converse (`f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹` ⇒ `f ∈ 𝒟(L)`) through the functional `b ↦ ∫ f L(b − Lb)` on
`(1−L)𝒜₀`, Cauchy-Schwarz for `Γ₂ − ρΓ` and Riesz; identifying the representing vector silently needs that `𝒜₀` is a core for `L²`
(ERRATA R15-1; the repo's `FullTriple.mem_domain_of_Γ₂` takes `Core2` as hypothesis, and R17-R19 proved `Core2` for Gibbs only under growth conditions).
Here:
1. `GibbsData.memLp_Lg_of_Γ₂` (`DirectCore.lean`): a cut-off Caccioppoli estimate (BGL Prop. 3.2.1, p. 142, applied to `Γ₂`) gives `L f ∈ L²(μ)`;
2. `FullTriple.mem_domain_of_ESA` (BGL Prop. 3.3.6 (i): essential self-adjointness of `L`, F10, proved for every Gibbs triple) gives `[f] ∈ 𝒟(L̄)`, `L̄[f] = [Lf]`.
Hypotheses: `V'' ≥ ρ` only (plus `f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹` as in the book).  ESA of `L` replaces ESA of `L²`; `Core2` is not used,
and the `Core2*` theorems stay as independent facts.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL (FullTriple DiffusionTriple)

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- **D1-1: the converse of BGL Prop. 3.3.17 (p. 162) for Gibbs triples on `ℝ`, with only `V'' ≥ ρ`.**
`f ∈ 𝒜 ∩ L²(μ)` with `Γ(f), Γ₂(f) ∈ L¹(μ)` ⇒ `[f] ∈ 𝒟(L)` and `L[f] = [L f]`.  No `Core2`, no growth condition on `V`
(contrast `gibbs_mem_domain_of_Γ₂`, `gibbs_mem_domain_of_Γ₂_polyHess`). -/
theorem gibbs_mem_domain_of_Γ₂_direct {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) {f : ℝ → ℝ}
    (hf : f ∈ G.gibbsFull_unconditional.A) (hf2 : MemLp f 2 G.μ)
    (hG : Integrable (FullTriple.G G.gibbsFull_unconditional f f) G.μ)
    (hG2 : Integrable (G.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) G.μ) :
    ∃ hF : hf2.toLp f ∈ G.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((G.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 G.μ) : ℝ → ℝ)
        =ᵐ[G.μ] G.gibbsFull_unconditional.L f := by
  have hfS : Sm f := hf
  have hGo : FullTriple.G G.gibbsFull_unconditional f f = Go f f := G.gibbsDiff_ΓA hfS hfS
  have hG' : Integrable (fun x => deriv f x * deriv f x) G.μ := by
    rw [hGo] at hG; exact hG
  have hΓ₂ : ∀ x, G.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f x =
      deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2 := by
    intro x
    have e1 : G.gibbsDiff.ΓA f f = Go f f := G.gibbsDiff_ΓA hfS hfS
    have e2 : G.gibbsDiff.ΓA f (Lg G.V f) = Go f (Lg G.V f) := G.gibbsDiff_ΓA hfS (sm_Lg G.smooth hfS)
    have e3 : G.gibbsDiff.ΓA (Lg G.V f) f = Go (Lg G.V f) f := G.gibbsDiff_ΓA (sm_Lg G.smooth hfS) hfS
    have e : G.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f x =
        (Lg G.V (Go f f) x - 2 * Go f (Lg G.V f) x) / 2 := by
      show (Lg G.V (G.gibbsDiff.ΓA f f) x - G.gibbsDiff.ΓA f (Lg G.V f) x -
        G.gibbsDiff.ΓA (Lg G.V f) f x) / 2 = _
      rw [e1, e2, e3]
      simp only [Go]; ring
    rw [e]
    exact Γ₂_eq G.smooth hfS x
  have hG2' : Integrable (fun x => deriv (deriv f) x ^ 2 + deriv (deriv G.V) x * deriv f x ^ 2) G.μ :=
    hG2.congr (Eventually.of_forall hΓ₂)
  have hL2 : MemLp (G.gibbsFull_unconditional.L f) 2 G.μ :=
    G.memLp_Lg_of_Γ₂ hρ hfS hG' hG2'
  obtain ⟨hF, hFe⟩ := FullTriple.mem_domain_of_ESA hf hf2 hL2
  refine ⟨hF, ?_⟩
  rw [hFe]
  exact hL2.coeFn_toLp

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
