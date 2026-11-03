import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.RegSemigroup
import MarkovTriple.BGL.Instances.Gibbs.FunctFull
import MarkovTriple.BGL.Instances.Gibbs.FunctPI

/-!
# Unconditional Gibbs results (R15)

The hypotheses `GibbsData.WeakHypo` (BGL Def. 3.3.8) and `GibbsData.F8` (BGL Def. 3.3.1 (viii)) are now theorems
(`GibbsData.weakHypo`, `GibbsData.f8`).  This file restates the results of `FunctAlgebra`/`FunctFull`/`FunctPI` for
every `G : GibbsData` with no regularity hypothesis.  The old conditional declarations are unchanged.

Still conditional elsewhere (not touched here): `gibbsFull_logSobolev`, `gibbsFull_gradient_bound`
(named structures `EntropyInterpolation`, `GradientInterpolation`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU hiding A₀ γ φ

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- ESA (F10) for every Gibbs triple. -/
theorem gibbsDiff_esaProp_unconditional : G.gibbsDiff.ESAProp := G.gibbsDiff_esaProp G.weakHypo

/-- Ergodicity (S10) for every Gibbs triple. -/
theorem gibbsDiff_ergodic_unconditional :
    ∀ (u : Lp ℝ 2 G.gibbsDiff.μ) (hu : u ∈ G.gibbsDiff.generator.domain),
      G.gibbsDiff.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : ℝ → ℝ) =ᵐ[G.gibbsDiff.μ] fun _ => c :=
  G.gibbsDiff_ergodic G.weakHypo

/-- The Gibbs Standard Markov Triple, unconditionally. -/
noncomputable def gibbsStandard_unconditional : StandardTriple ℝ := G.gibbsStandard G.weakHypo

/-- **The Gibbs Full Markov Triple** (BGL Def. 3.3.25), unconditionally. -/
noncomputable def gibbsFull_unconditional : FullTriple ℝ := G.gibbsFull G.weakHypo G.f8

/-- `CD(ρ,∞)` for the (unconditional) Gibbs Full Markov Triple when `V'' ≥ ρ`. -/
theorem gibbsFull_CD_unconditional {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    G.gibbsFull_unconditional.CD ρ ∞ := G.gibbsFull_CD G.weakHypo G.f8 hρ

/-- Poincaré through the unconditional Full triple. -/
theorem gibbsFull_poincare_unconditional {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    G.gibbsFull_unconditional.toDiffusionTriple.PI (1 / ρ) :=
  G.gibbsFull_poincare G.weakHypo G.f8 hρpos hρ

/-- **Poincaré inequality for `e^{-V}dx`, `V'' ≥ ρ > 0`**, constant `1/ρ`, with no regularity hypothesis. -/
theorem gibbs_poincare_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    G.gibbsDiff.PI (1 / ρ) := G.gibbs_poincare hρpos hρ G.weakHypo

/-- Spectral gap `ρ`, unconditionally. -/
theorem gibbs_spectralGap_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    (DiffusionTriple.formData G.gibbsDiff).HasSpectralGap ρ :=
  G.gibbs_spectralGap hρpos hρ G.weakHypo

/-- `L²` exponential decay, unconditionally. -/
theorem gibbs_expDecay_unconditional {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    (DiffusionTriple.formData G.gibbsDiff).HasExpDecay ρ :=
  G.gibbs_expDecay hρpos hρ G.weakHypo

/-! ### Non-vacuity checks (used by `AUDIT_R15_REG_SELF.md`) -/

/-- the premise of `WeakHypo` is satisfiable by a non-zero class (the constant `1`, `λ = 0`), so the theorem
`weakHypo` is not an implication with an impossible hypothesis. -/
theorem weakHypo_premise_satisfiable :
    ∃ (l : ℝ) (f : Lp ℝ 2 G.gibbsDiff.μ), f ≠ 0 ∧
      ∀ a : G.gibbsDiff.A₀, ∫ x, (f : ℝ → ℝ) x * G.gibbsDiff.L a.1 x ∂G.gibbsDiff.μ =
        ∫ x, (l * (f : ℝ → ℝ) x) * a.1 x ∂G.gibbsDiff.μ := by
  refine ⟨0, G.gibbsDiff.one2, ?_, fun a => ?_⟩
  · intro h
    have h1 := G.gibbsDiff.coeFn_one2
    have h2 : (G.gibbsDiff.one2 : ℝ → ℝ) =ᵐ[G.gibbsDiff.μ] 0 := by
      rw [h]; exact Lp.coeFn_zero ℝ 2 _
    obtain ⟨x, hx1, hx2⟩ := (h1.and h2).exists
    simp at hx1 hx2
    rw [hx1] at hx2
    exact one_ne_zero hx2
  · have e1 : ∫ x, (G.gibbsDiff.one2 : ℝ → ℝ) x * G.gibbsDiff.L a.1 x ∂G.gibbsDiff.μ =
        ∫ x, G.gibbsDiff.L a.1 x ∂G.gibbsDiff.μ := by
      refine integral_congr_ae ?_
      filter_upwards [G.gibbsDiff.coeFn_one2] with x hx
      rw [hx, one_mul]
    rw [e1, G.gibbsDiff.integral_L a.1 a.2]
    simp

/-- representatives in `𝒜 = C^∞(ℝ)` are unique (`μ` has full support), so `F8` is a genuine statement about the
class and cannot be satisfied through a.e. freedom. -/
theorem afull_rep_unique {g₁ g₂ : ℝ → ℝ} (h₁ : g₁ ∈ Afull) (h₂ : g₂ ∈ Afull)
    (h : g₁ =ᵐ[G.μ] g₂) : g₁ = g₂ :=
  (Continuous.ae_eq_iff_eq G.μ (show Sm g₁ from h₁).continuous (show Sm g₂ from h₂).continuous).1 h

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
