import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.DirectEllMain
import MarkovTriple.BGL.Instances.Riemannian.Core2RiemConf
import MarkovTriple.BGL.Instances.Riemannian.HypUnconditional

/-!
# The converse of BGL Prop. 3.3.17 for weighted Riemannian charts WITHOUT `Core2` / `CoreCut`; `hypRiem`, `confRiem` (R20, Stream D2)

Statements: `STATEMENTS_R20_DirectEll.md` (D6, D7).

## DIFFERENCE FROM BGL

* *BGL* (Prop. 3.3.17, p. 161-162) proves the converse through density of `(L² + Id)𝒜₀` (`Core2`, silently used, ERRATA R15-1).
  R19 proved `Core2` and the converse for `RiemData` under `Curv ρ` and the cut-off hypothesis `CoreCut` (bounded `Γ₂(χ_n), Lχ_n, ...`),
  which the hyperbolic plane `hypRiem` does NOT satisfy (`AUDIT_R19_CORE2ELL.md` §6, by hand).
* *Here*: `RiemData.riem_mem_domain_of_Γ₂_direct` needs only `Curv ρ` (any sign) and the completeness field `g_exh`.  The argument is the
  cut-off technique of BGL Prop. 3.2.1 (p. 142) applied to `Γ₂` (cross term controlled through Bochner's formula by `|∇χ|` alone),
  followed by the existing ESA statement `FullTriple.mem_domain_of_ESA` (BGL Prop. 3.3.6 (i)).  `Core2` and `CoreCut` are not used, and
  the earlier `Core2` theorems stay valid as independent facts (we claim nothing about `Core2` for `hypRiem`).
* New instance: `hypRiem` (`Curv 1`, `ρ > 0`, unbounded co-metric, no `CoreCut`): `hypRiem_mem_domain_of_Γ₂_direct`.  Also `confRiem` (`Curv 2`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open MarkovTriple.BGL (FullTriple pderiv)

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

/-- **D6**: the converse of BGL Prop. 3.3.17 for weighted Riemannian charts under `Curv ρ` only (no `CoreCut`). -/
theorem riem_mem_domain_of_Γ₂_direct {ρ : ℝ} (hρ : R.Curv ρ) {f : Rd d → ℝ}
    (hf : f ∈ R.riemFull_unconditional.A) (hf2 : MemLp f 2 R.toEll.μ)
    (hG : Integrable (FullTriple.G R.riemFull_unconditional f f) R.toEll.μ)
    (hG2 : Integrable (R.riemFull_unconditional.toDiffusionTriple.Γ₂ f f) R.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ R.riemFull_unconditional.toDiffusionTriple.generator.domain,
      ((R.riemFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 R.toEll.μ) :
        Rd d → ℝ) =ᵐ[R.toEll.μ] R.riemFull_unconditional.L f :=
  R.toEll.ell_mem_domain_of_Γ₂_direct hρ hf hf2 hG hG2

/-- the hypotheses are satisfied by every test function (non-vacuity of the statement) -/
theorem riem_mem_domain_of_A₀_direct {ρ : ℝ} (hρ : R.Curv ρ) {f : Rd d → ℝ} (hf : f ∈ A₀ d) :
    ∃ hf2 : MemLp f 2 R.toEll.μ,
      ∃ hF : hf2.toLp f ∈ R.riemFull_unconditional.toDiffusionTriple.generator.domain,
      ((R.riemFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 R.toEll.μ) :
        Rd d → ℝ) =ᵐ[R.toEll.μ] R.riemFull_unconditional.L f :=
  R.toEll.ell_mem_domain_of_A₀_direct hρ hf

end RiemData

/-- **The hyperbolic plane** `hypRiem` (`W = 2 cosh d`, `Curv 1`, `ρ = 1 > 0`, unbounded co-metric, NO `CoreCut`): the converse of
Prop. 3.3.17 holds, by the direct route. -/
theorem hypRiem_mem_domain_of_Γ₂_direct {f : Rd 2 → ℝ} (hf : f ∈ hypRiem.riemFull_unconditional.A)
    (hf2 : MemLp f 2 hypRiem.toEll.μ)
    (hG : Integrable (FullTriple.G hypRiem.riemFull_unconditional f f) hypRiem.toEll.μ)
    (hG2 : Integrable (hypRiem.riemFull_unconditional.toDiffusionTriple.Γ₂ f f) hypRiem.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ hypRiem.riemFull_unconditional.toDiffusionTriple.generator.domain,
      ((hypRiem.riemFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 hypRiem.toEll.μ) : Rd 2 → ℝ) =ᵐ[hypRiem.toEll.μ] hypRiem.riemFull_unconditional.L f :=
  hypRiem.riem_mem_domain_of_Γ₂_direct hypRiem.curv hf hf2 hG hG2

/-- `hypRiem`: instance on test functions, with all hypotheses discharged -/
theorem hypRiem_mem_domain_of_A₀_direct {f : Rd 2 → ℝ} (hf : f ∈ A₀ 2) :
    ∃ hf2 : MemLp f 2 hypRiem.toEll.μ,
      ∃ hF : hf2.toLp f ∈ hypRiem.riemFull_unconditional.toDiffusionTriple.generator.domain,
      ((hypRiem.riemFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 hypRiem.toEll.μ) : Rd 2 → ℝ) =ᵐ[hypRiem.toEll.μ] hypRiem.riemFull_unconditional.L f :=
  hypRiem.riem_mem_domain_of_A₀_direct hypRiem.curv hf

/-- **`confRiem`** (`Curv 2`, non-flat): the converse of Prop. 3.3.17 by the direct route (no `CoreCut`). -/
theorem confRiem_mem_domain_of_Γ₂_direct {f : Rd 2 → ℝ} (hf : f ∈ confRiem.riemFull_unconditional.A)
    (hf2 : MemLp f 2 confRiem.toEll.μ)
    (hG : Integrable (FullTriple.G confRiem.riemFull_unconditional f f) confRiem.toEll.μ)
    (hG2 : Integrable (confRiem.riemFull_unconditional.toDiffusionTriple.Γ₂ f f) confRiem.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ confRiem.riemFull_unconditional.toDiffusionTriple.generator.domain,
      ((confRiem.riemFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 confRiem.toEll.μ) : Rd 2 → ℝ) =ᵐ[confRiem.toEll.μ] confRiem.riemFull_unconditional.L f :=
  confRiem.riem_mem_domain_of_Γ₂_direct confRiem.curv hf hf2 hG hG2

/-- the Hessian Cauchy–Schwarz on the two witnesses (`ρ = 1`, `ρ = 2`) -/
theorem hypRiem_hessCS : hypRiem.toEll.HessCS 1 := hypRiem.riem_hessCS hypRiem.curv

theorem confRiem_hessCS : confRiem.toEll.HessCS 2 := confRiem.riem_hessCS confRiem.curv

end MarkovTriple.BGL.Instances.Riemannian
