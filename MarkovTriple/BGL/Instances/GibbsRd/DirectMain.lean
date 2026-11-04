import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.DirectCore
import MarkovTriple.BGL.Instances.GibbsRd.Unconditional
import MarkovTriple.BGL.Theory.Extension.ClosedIdent

/-!
# Gibbs on `ℝ^d`: the converse of BGL Prop. 3.3.17 with only `Hess V ≥ ρ` — no `Core2`, no growth hypothesis (R20, Stream D1)

Statements: `Instances/Gibbs/STATEMENTS_R20_Direct.md` (D1-3).

## DIFFERENCE FROM BGL

BGL (Prop. 3.3.17, p. 161-162) proves the converse (`f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹` ⇒ `f ∈ 𝒟(L)`) through the functional `b ↦ ∫ f L(b − Lb)` on
`(1−L)𝒜₀`, Cauchy-Schwarz for `Γ₂ − ρΓ` and Riesz; identifying the representing vector silently needs that `𝒜₀` is a core for `L²`
(ERRATA R15-1; the repo's `FullTriple.mem_domain_of_Γ₂` takes `Core2` as hypothesis, and R18-R19 proved `Core2` on `ℝ^d` only under `BddHess3`/`GrowHess3`).
Here:
1. `GibbsRdData.memLp_Lr_of_Γ₂` (`DirectCore.lean`): a cut-off Caccioppoli estimate (BGL Prop. 3.2.1, p. 142, applied to `Γ₂`) gives `L f ∈ L²(μ)`;
2. `FullTriple.mem_domain_of_ESA` (BGL Prop. 3.3.6 (i): essential self-adjointness of `L`, F10, proved for every Gibbs triple) gives `[f] ∈ 𝒟(L̄)`, `L̄[f] = [Lf]`.
Hypotheses: `HessGe V ρ` only (any sign of `ρ`), plus `f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹` as in the book.  ESA of `L` replaces ESA of `L²`; `Core2` is not used,
and the `Core2Rd*` theorems stay as independent facts.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (FullTriple DiffusionTriple pderiv)

variable {d : ℕ}

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- **D1-3: the converse of BGL Prop. 3.3.17 (p. 162) for Gibbs triples on `ℝ^d`, with only `Hess V ≥ ρ`.**
`f ∈ 𝒜 ∩ L²(μ)` with `Γ(f), Γ₂(f) ∈ L¹(μ)` ⇒ `[f] ∈ 𝒟(L)` and `L[f] = [L f]`.  No `Core2`, no growth condition on `V`
(contrast `gibbsRd_mem_domain_of_Γ₂`, `gibbsRd_mem_domain_of_Γ₂_w`). -/
theorem gibbsRd_mem_domain_of_Γ₂_direct {ρ : ℝ} (hρ : HessGe G.V ρ) {f : Rd d → ℝ}
    (hf : f ∈ G.gibbsRdFull_unconditional.A) (hf2 : MemLp f 2 G.toEll.μ)
    (hG : Integrable (FullTriple.G G.gibbsRdFull_unconditional f f) G.toEll.μ)
    (hG2 : Integrable (G.gibbsRdFull_unconditional.toDiffusionTriple.Γ₂ f f) G.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ G.gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      ((G.gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 G.toEll.μ) :
        Rd d → ℝ) =ᵐ[G.toEll.μ] G.gibbsRdFull_unconditional.L f := by
  have hfS : Sm f := hf
  have hGr : FullTriple.G G.gibbsRdFull_unconditional f f = Gr f f := by
    show G.toEll.diff.ΓA f f = Gr f f
    rw [G.toEll.ΓA_eq hfS hfS, G.toEll_Γ]
  have hG' : Integrable (Gr f f) G.toEll.μ := by
    rw [hGr] at hG; exact hG
  have hG2' : Integrable (fun x => ∑ i, ∑ j, pderiv (pderiv f i) j x ^ 2 +
      ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv f i x * pderiv f j x) G.toEll.μ :=
    hG2.congr (Eventually.of_forall fun x => G.gibbsRd_Γ₂_eq hfS x)
  have hL2 : MemLp (G.gibbsRdFull_unconditional.L f) 2 G.toEll.μ := by
    have e : G.gibbsRdFull_unconditional.L f = Lr G.V f := G.gibbsRdDiff_L hfS
    rw [e]
    exact G.memLp_Lr_of_Γ₂ hρ hfS hG' hG2'
  obtain ⟨hF, hFe⟩ := FullTriple.mem_domain_of_ESA hf hf2 hL2
  refine ⟨hF, ?_⟩
  rw [hFe]
  exact hL2.coeFn_toLp

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
