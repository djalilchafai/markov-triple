import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.DirectEllCore
import MarkovTriple.BGL.Instances.Riemannian.DirectRiemTransport

/-!
# The converse of BGL Prop. 3.3.17 for `EllData d` WITHOUT `Core2` / `CoreCut` (R20, Stream D2)

Statements: `STATEMENTS_R20_DirectEll.md` (D5).

## DIFFERENCE FROM BGL

* *BGL* (Prop. 3.3.17, p. 161-162): the converse is proved through density of `(L² + Id)𝒜₀` in `L²`, i.e. `Core2` (silently used;
  ERRATA R15-1).  R17-R19 proved `Core2` only under growth hypotheses; for `EllData`/`RiemData` it was proved under `Curv ρ` + `CoreCut`
  (`EllData.ell_mem_domain_of_Γ₂`), and `CoreCut` fails for the hyperbolic plane.
* *Here*: `EllData.ell_mem_domain_of_Γ₂_direct` assumes ONLY `Curv ρ` (`ρ ∈ ℝ` of any sign); completeness is part of the data (`a_exh`).
  The proof is the cut-off (Caccioppoli) technique of BGL Prop. 3.2.1 (p. 142) applied to `Γ₂`: the identity
  `∫ χ²(Lf)² = ∫ χ²Γ₂(f) + ∫ χΓ(χ,Γf) − 2∫ χ Lf Γ(χ,f)` with the cross term controlled by `|∇χ|` through the Hessian
  Cauchy–Schwarz (Bochner), gives `Lf ∈ L²`; then ESA (F10, existing `FullTriple.mem_domain_of_ESA`) gives `f ∈ 𝒟(L)`.
  `Core2` is never used; the earlier `Core2` results are independent facts and are not claimed here.
* Same conclusion shape as `EllData.ell_mem_domain_of_Γ₂`, with the hypothesis `hC : E.CoreCut` removed.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.BGL (FullTriple pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- **D5: the converse of BGL Prop. 3.3.17 without `Core2`/`CoreCut`** for a weighted elliptic chart: `f ∈ 𝒜 ∩ L²(μ)` with
`Γ(f), Γ₂(f) ∈ L¹(μ)` implies `[f] ∈ 𝒟(L)`, `L[f] = [Lf]` a.e., under `Curv ρ` only. -/
theorem ell_mem_domain_of_Γ₂_direct {ρ : ℝ} (hρ : E.Curv ρ) {f : Rd d → ℝ}
    (hf : f ∈ E.fullU.A) (hf2 : MemLp f 2 E.μ)
    (hG : Integrable (FullTriple.G E.fullU f f) E.μ)
    (hG2 : Integrable (E.fullU.toDiffusionTriple.Γ₂ f f) E.μ) :
    ∃ hF : hf2.toLp f ∈ E.fullU.toDiffusionTriple.generator.domain,
      ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ]
        E.fullU.L f :=
  E.ell_mem_domain_of_hessCS hρ (E.hessCS_of_curv hρ) hf hf2 hG hG2

/-- non-vacuity of the hypotheses: every test function `f ∈ C_c^∞` satisfies them, so the theorem applies to all of `𝒜₀`
(with the conclusion for the explicit `L²`-class). -/
theorem ell_mem_domain_of_A₀_direct {ρ : ℝ} (hρ : E.Curv ρ) {f : Rd d → ℝ} (hf : f ∈ A₀ d) :
    ∃ hf2 : MemLp f 2 E.μ, ∃ hF : hf2.toLp f ∈ E.fullU.toDiffusionTriple.generator.domain,
      ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ]
        E.fullU.L f := by
  have hfS : Sm f := hf.1
  have hf2 : MemLp f 2 E.μ := hfS.continuous.memLp_of_hasCompactSupport hf.2
  have hG : Integrable (FullTriple.G E.fullU f f) E.μ := by
    have e : FullTriple.G E.fullU f f = E.Γ f f := E.ΓA_eq hfS hfS
    rw [e]
    exact (E.sm_Γ hfS hfS).continuous.integrable_of_hasCompactSupport (E.hcs_Γ_left hf.2)
  have hG2 : Integrable (E.fullU.toDiffusionTriple.Γ₂ f f) E.μ := by
    have e : E.fullU.toDiffusionTriple.Γ₂ f f = fun x => (E.L (E.Γ f f) x - E.Γ f (E.L f) x - E.Γ (E.L f) f x) / 2 :=
      E.Γ₂_eq_comb hfS
    rw [e]
    have hc : HasCompactSupport (fun x => (E.L (E.Γ f f) x - E.Γ f (E.L f) x - E.Γ (E.L f) f x)) :=
      ((E.hcs_L (E.hcs_Γ_left hf.2)).sub (E.hcs_Γ_left hf.2)).sub (E.hcs_Γ_left (E.hcs_L hf.2))
    have hcon : Continuous (fun x => (E.L (E.Γ f f) x - E.Γ f (E.L f) x - E.Γ (E.L f) f x) / 2) :=
      ((((E.sm_L (E.sm_Γ hfS hfS)).continuous).sub (E.sm_Γ hfS (E.sm_L hfS)).continuous).sub
        (E.sm_Γ (E.sm_L hfS) hfS).continuous).div_const 2
    exact hcon.integrable_of_hasCompactSupport (hc.comp_left (g := fun y : ℝ => y / 2) (by simp))
  exact ⟨hf2, E.ell_mem_domain_of_Γ₂_direct hρ (hfS) hf2 hG hG2⟩

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
