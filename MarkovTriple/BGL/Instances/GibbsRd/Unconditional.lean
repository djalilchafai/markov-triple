import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllRegProof
import MarkovTriple.BGL.Instances.Gibbs.JensenMain
import MarkovTriple.BGL.Theory.Interp.EntropyApplications

/-!
# Gibbs on `ℝ^d`: unconditional theorems (R16 glue)

`WeakHypo` and `F8` are now theorems (`EllData.weakHypo_unconditional`, `f8_unconditional`, via `EllData.ellReg`).
The conditional versions in `Main.lean` are unchanged.  Statements: `STATEMENTS_R16_Glue.md`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (DiffusionTriple FullTriple HasGradientBound)

variable {d : ℕ}

namespace GibbsRdData
variable (G : GibbsRdData d)

theorem weakHypo_unconditional : G.WeakHypo := G.toEll.weakHypo_unconditional
theorem f8_unconditional : G.F8 := G.toEll.f8_unconditional

theorem gibbsRd_poincare_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : HessGe G.V ρ) :
    G.gibbsRdDiff.PI (1 / ρ) := G.gibbsRd_poincare hρpos hρ G.weakHypo_unconditional

theorem gibbsRd_spectralGap_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : HessGe G.V ρ) :
    (DiffusionTriple.formData G.gibbsRdDiff).HasSpectralGap ρ :=
  G.gibbsRd_spectralGap hρpos hρ G.weakHypo_unconditional

theorem gibbsRd_expDecay_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : HessGe G.V ρ) :
    (DiffusionTriple.formData G.gibbsRdDiff).HasExpDecay ρ :=
  G.gibbsRd_expDecay hρpos hρ G.weakHypo_unconditional

/-- The Gibbs Full Markov triple on `ℝ^d`, with no hypothesis. -/
noncomputable def gibbsRdFull_unconditional : FullTriple (Rd d) :=
  G.gibbsRdFull G.weakHypo_unconditional G.f8_unconditional

theorem gibbsRdFull_CD_unconditional {ρ : ℝ} (hρ : HessGe G.V ρ) :
    G.gibbsRdFull_unconditional.CD ρ ∞ :=
  G.gibbsRdFull_CD G.weakHypo_unconditional G.f8_unconditional hρ

theorem gibbsRdFull_poincare_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : HessGe G.V ρ) :
    G.gibbsRdFull_unconditional.toDiffusionTriple.PI (1 / ρ) :=
  G.gibbsRdFull_poincare G.weakHypo_unconditional G.f8_unconditional hρpos hρ

/-- Log-Sobolev `LS(1/ρ, 0)` for `e^{-V}dx / Z` on `ℝ^d`, `Hess V ≥ ρ > 0`, with no hypothesis. -/
theorem gibbsRdFull_logSobolev_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : HessGe G.V ρ) :
    G.gibbsRdFull_unconditional.toDiffusionTriple.LS (1 / ρ) 0 := by
  have : IsProbabilityMeasure G.gibbsRdFull_unconditional.μ :=
    (inferInstance : IsProbabilityMeasure G.toEll.μ)
  exact FullTriple.logSobolev_unconditional _ hρpos (G.gibbsRdFull_CD_unconditional hρ)

/-- Weak gradient bound `Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)` (`ρ ≥ 0`), with no hypothesis. -/
theorem gibbsRdFull_gradient_bound_noHyp {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : HessGe G.V ρ)
    (f : G.gibbsRdFull_unconditional.A₀) (t : ℝ≥0) :
    G.gibbsRdFull_unconditional.toDiffusionTriple.ΓA (G.gibbsRdFull_unconditional.Pt t f)
        (G.gibbsRdFull_unconditional.Pt t f) ≤ᵐ[G.toEll.μ] fun x =>
      Real.exp (-2 * ρ * t) * (G.gibbsRdFull_unconditional.toDiffusionTriple.semigroup t
        (G.gibbsRdFull_unconditional.toDiffusionTriple.cls
          ⟨G.gibbsRdFull_unconditional.toDiffusionTriple.ΓA f.1 f.1,
            G.gibbsRdFull_unconditional.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 G.toEll.μ) x :=
  G.gibbsRdFull_gradient_bound_unconditional G.weakHypo_unconditional G.f8_unconditional hρ0 hρ f t

theorem gibbsRdFull_hasGradientBound_unconditional {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : HessGe G.V ρ) :
    HasGradientBound G.gibbsRdFull_unconditional.toDiffusionTriple G.gibbsRdFull_unconditional.A ρ :=
  FullTriple.hasGradientBound_unconditional _ (G.gibbsRdFull_CD_unconditional hρ) hρ0

end GibbsRdData
end MarkovTriple.BGL.Instances.GibbsRd
