import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllRegProof
import MarkovTriple.BGL.Instances.GibbsRd.Unconditional
import MarkovTriple.BGL.Instances.Riemannian.BochnerExample

/-!
# Weighted Riemannian chart: unconditional theorems (R16 glue)

`WeakHypo`, `F8` are theorems (`EllData.ellReg`).  Conditional versions unchanged.
Statements: `GibbsRd/STATEMENTS_R16_Glue.md`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.BGL.Instances.Riemannian

open MarkovTriple.BGL.Instances.GibbsRd
open MarkovTriple.BGL (DiffusionTriple FullTriple HasGradientBound)

variable {d : ℕ}

namespace RiemData
variable (R : RiemData d)

theorem weakHypo_unconditional : R.WeakHypo := R.toEll.weakHypo_unconditional
theorem f8_unconditional : R.F8 := R.toEll.f8_unconditional

theorem riem_poincare_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : R.Curv ρ) :
    R.riemDiff.PI (1 / ρ) := R.riem_poincare hρpos hρ R.weakHypo_unconditional

theorem riem_spectralGap_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : R.Curv ρ) :
    (DiffusionTriple.formData R.riemDiff).HasSpectralGap ρ :=
  R.riem_spectralGap hρpos hρ R.weakHypo_unconditional

theorem riem_expDecay_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : R.Curv ρ) :
    (DiffusionTriple.formData R.riemDiff).HasExpDecay ρ :=
  R.riem_expDecay hρpos hρ R.weakHypo_unconditional

noncomputable def riemFull_unconditional : FullTriple (Rd d) :=
  R.riemFull R.weakHypo_unconditional R.f8_unconditional

theorem riemFull_CD_unconditional {ρ : ℝ} (hρ : R.Curv ρ) : R.riemFull_unconditional.CD ρ ∞ :=
  R.riemFull_CD R.weakHypo_unconditional R.f8_unconditional hρ

theorem riemFull_logSobolev_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : R.Curv ρ) :
    R.riemFull_unconditional.toDiffusionTriple.LS (1 / ρ) 0 := by
  have : IsProbabilityMeasure R.riemFull_unconditional.μ :=
    (inferInstance : IsProbabilityMeasure R.toEll.μ)
  exact FullTriple.logSobolev_unconditional _ hρpos (R.riemFull_CD_unconditional hρ)

theorem riemFull_gradient_bound_unconditional {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : R.Curv ρ)
    (f : R.riemFull_unconditional.A₀) (t : ℝ≥0) :
    R.riemFull_unconditional.toDiffusionTriple.ΓA (R.riemFull_unconditional.Pt t f)
        (R.riemFull_unconditional.Pt t f) ≤ᵐ[R.toEll.μ] fun x =>
      Real.exp (-2 * ρ * t) * (R.riemFull_unconditional.toDiffusionTriple.semigroup t
        (R.riemFull_unconditional.toDiffusionTriple.cls
          ⟨R.riemFull_unconditional.toDiffusionTriple.ΓA f.1 f.1,
            R.riemFull_unconditional.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 R.toEll.μ) x :=
  FullTriple.gradient_bound_unconditional _ (R.riemFull_CD_unconditional hρ) hρ0 f t

theorem riemFull_hasGradientBound_unconditional {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : R.Curv ρ) :
    HasGradientBound R.riemFull_unconditional.toDiffusionTriple R.riemFull_unconditional.A ρ :=
  FullTriple.hasGradientBound_unconditional _ (R.riemFull_CD_unconditional hρ) hρ0

end RiemData

/-! ### The non-flat example `confRiem` (`Curv 2`) -/

theorem confRiem_poincare_unconditional : confRiem.riemDiff.PI (1 / 2) :=
  confRiem_poincare confRiem.weakHypo_unconditional

theorem confRiem_spectralGap_unconditional :
    (DiffusionTriple.formData confRiem.riemDiff).HasSpectralGap 2 :=
  confRiem_spectralGap confRiem.weakHypo_unconditional

theorem confRiem_expDecay_unconditional :
    (DiffusionTriple.formData confRiem.riemDiff).HasExpDecay 2 :=
  confRiem_expDecay confRiem.weakHypo_unconditional

theorem confRiem_CD_unconditional : confRiem.riemFull_unconditional.CD 2 ∞ :=
  confRiem.riemFull_CD_unconditional confRiem.curv

theorem confRiem_logSobolev_unconditional :
    confRiem.riemFull_unconditional.toDiffusionTriple.LS (1 / 2) 0 :=
  confRiem.riemFull_logSobolev_unconditional (by norm_num) confRiem.curv

theorem confRiem_hasGradientBound_unconditional :
    HasGradientBound confRiem.riemFull_unconditional.toDiffusionTriple
      confRiem.riemFull_unconditional.A 2 :=
  confRiem.riemFull_hasGradientBound_unconditional (by norm_num) confRiem.curv

end MarkovTriple.BGL.Instances.Riemannian
