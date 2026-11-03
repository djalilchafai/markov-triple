import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctPI
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Theory.LogSobolevMain
import MarkovTriple.BGL.Theory.GradientBound
import MarkovTriple.BGL.Theory.Strong.Main

/-!
# Gibbs measures: the Full Markov Triple, conditionally on exactly three analytic inputs

BGL Def. 3.3.25 (F1–F10, S10, S11) for `μ = Z⁻¹e^{-V}dx`, `𝒜₀ = C_c^∞(ℝ)`, `𝒜 = C^∞(ℝ)`.

Everything except the three semigroup-dependent items is proved here:
F1 (ideal), F2 (positivity detection), F3, F4, F5, F6, F7, F9 (connexity) are elementary calculus
(`gibbs_preFull`, `Gibbs/FunctIBP`, `Calculus`); S11 follows from ESA for the finite measure (`conservative_of_esa`).
The remaining inputs are

* `GibbsData.WeakHypo` (BGL Def. 3.3.8; with connexity and completeness it gives F10 = ESA,
  Prop. 3.3.11, and S10 = ergodicity, Prop. 3.3.10);
* `GibbsData.F8`: `P_t f ∈ 𝒜` for `f ∈ 𝒜₀` (BGL Def. 3.3.1 (viii) / F8), i.e. the Friedrichs semigroup maps
  test functions to smooth functions.

Both are quoted, not proved, by the book (Sect. 1.12).  Under these `gibbsFull : FullTriple ℝ` exists, `FullTriple.CD ρ ∞` holds when `V'' ≥ ρ`
(`gibbsFull_CD`), and the book's consequences follow, the last two still conditional on the named
regularity structures of `Theory/` (not derived for non-compact triples):
Poincaré (unconditionally in the structure, `gibbsFull_poincare`), log-Sobolev (`EntropyInterpolation`),
gradient bounds (`GradientInterpolation`, `StrongInterpolation`).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- **The Gibbs Standard Markov Triple** (S10 from Prop. 3.3.10; S11 from ESA, finite measure). -/
noncomputable def gibbsStandard (hH : G.WeakHypo) : StandardTriple ℝ where
  toDiffusionTriple := G.gibbsDiff
  ergodic := G.gibbsDiff_ergodic hH
  conservative := fun _ hu _ t =>
    DiffusionTriple.conservative_of_esa (T := G.gibbsDiff) (G.gibbsDiff_esaProp hH) hu t

/-- **The Gibbs Full Markov Triple** (BGL Def. 3.3.25), under weak hypo-ellipticity and F8. -/
noncomputable def gibbsFull (hH : G.WeakHypo) (h8 : G.F8) : FullTriple ℝ where
  toStandardTriple := G.gibbsStandard hH
  A := Afull
  A₀_le := G.gibbs_preFull.A₀_le
  A_measurable := G.gibbs_preFull.A_measurable
  ideal := G.gibbs_preFull.ideal
  pos_detect := G.gibbs_preFull.pos_detect
  A_comp := fun k ψ hψ f hf => sm_comp k ψ hψ f hf
  L_mem_A := G.gibbs_preFull.L_mem_A
  ΓA_nonneg := G.gibbs_preFull.ΓA_nonneg
  diffusion_Γ_A := G.gibbs_preFull.diffusion_Γ_A
  diffusion_L_A := fun k ψ hψ f hf => Eventually.of_forall fun x => by
    have hf' : ∀ i, Sm (f i) := fun i => hf i
    have key : ∀ i j, G.gibbsDiff.ΓA (f i) (f j) = Go (f i) (f j) :=
      fun i j => G.gibbsDiff_ΓA (hf' i) (hf' j)
    have := congrFun (diffusion_g G.V k ψ hψ f hf') x
    refine this.trans ?_
    congr 1
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      show _ = _ * G.gibbsDiff.ΓA (f i) (f j) x
      rw [key i j]
  ibp_A := G.gibbs_preFull.ibp_A
  semigroup_A := h8
  connected := G.gibbs_preFull.connected
  esa := G.gibbsDiff_esaProp hH

/-- **`CD(ρ,∞)` for the Gibbs Full Markov Triple** (`V'' ≥ ρ`). -/
theorem gibbsFull_CD (hH : G.WeakHypo) (h8 : G.F8) {ρ : ℝ}
    (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) : (G.gibbsFull hH h8).CD ρ ∞ :=
  ⟨le_top, fun f hf => Eventually.of_forall fun x => G.gibbs_CD_pointwise hρ f hf x⟩

/-- **Poincaré for Gibbs through the Full triple** (`poincare_of_CD_infty`; same statement as
`gibbs_poincare`, which does not need F8). -/
theorem gibbsFull_poincare (hH : G.WeakHypo) (h8 : G.F8)
    {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    (G.gibbsFull hH h8).toDiffusionTriple.PI (1 / ρ) :=
  haveI : IsProbabilityMeasure (G.gibbsFull hH h8).μ :=
    (inferInstance : IsProbabilityMeasure G.μ)
  FullTriple.poincare_of_CD_infty _ hρpos (G.gibbsFull_CD hH h8 hρ)

/-- **Log-Sobolev for Gibbs** (`Ent(f²) ≤ (2/ρ) ∫ f'² dμ`, BGL Prop. 5.7.1 / Thm 5.7.4 route),
conditional on the named structure `EntropyInterpolation` of the Gibbs Full triple. -/
theorem gibbsFull_logSobolev (hH : G.WeakHypo) (h8 : G.F8)
    {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x)
    (hE : (G.gibbsFull hH h8).EntropyInterpolation) :
    (G.gibbsFull hH h8).toDiffusionTriple.LS (1 / ρ) 0 :=
  haveI : IsProbabilityMeasure (G.gibbsFull hH h8).μ :=
    (inferInstance : IsProbabilityMeasure G.μ)
  FullTriple.logSobolev_of_CD_infty _ hE hρpos (G.gibbsFull_CD hH h8 hρ)

/-- **Gradient bound for Gibbs** (`Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)`, BGL Cor. 3.3.19), conditional on
`GradientInterpolation` of the Gibbs Full triple. -/
theorem gibbsFull_gradient_bound (hH : G.WeakHypo)
    (h8 : G.F8) {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x)
    (hG : (G.gibbsFull hH h8).GradientInterpolation) (f : (G.gibbsFull hH h8).A₀) (t : ℝ≥0) :
    (G.gibbsFull hH h8).toDiffusionTriple.ΓA ((G.gibbsFull hH h8).Pt t f)
        ((G.gibbsFull hH h8).Pt t f) ≤ᵐ[G.μ] fun x =>
      Real.exp (-2 * ρ * t) * ((G.gibbsFull hH h8).toDiffusionTriple.semigroup t
        ((G.gibbsFull hH h8).toDiffusionTriple.cls
          ⟨(G.gibbsFull hH h8).toDiffusionTriple.ΓA f.1 f.1,
            (G.gibbsFull hH h8).ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 G.μ) x :=
  FullTriple.gradient_bound _ (G.gibbsFull_CD hH h8 hρ) hG f t

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
