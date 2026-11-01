import Mathlib
import MarkovTriple.BGL.Frozen.PartialDeriv
import MarkovTriple.BGL.Frozen.Exhaustion

/-!
# Diffusion Markov Triples (Bakry–Gentil–Ledoux, Ch. 3, Defs 3.1.1, 3.1.3, 3.1.8; hypotheses D1–D8)
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BGL

/-- A **Diffusion Markov Triple** `(E, μ, Γ)` in the sense of Bakry–Gentil–Ledoux, *Analysis and
Geometry of Markov Diffusion Operators*, Ch. 3: Definitions 3.1.1, 3.1.3, 3.1.8, summarized as the
hypotheses D1–D9 of §3.4.1.  The labels below are the book's.

Everything analytic is a field; nothing is an axiom.  `Γ` and `L` are honest functions
`(E → ℝ) → (E → ℝ) → (E → ℝ)` and `(E → ℝ) → (E → ℝ)`, only constrained on `A₀`.  Equalities between
functions are `μ`-a.e. (the book's convention, Def. 3.1.3), except membership statements, which are
literal.

* D1: `μ` σ-finite, and a probability measure when finite (`finite_prob`).  The "good measurable
  space" requirement (countable generation up to null sets, measure decomposition theorem) is NOT
  encoded; no hypothesis below uses it.
* D2: `A₀` bounded (everywhere) measurable functions, an algebra (non-unital, a
  `NonUnitalSubalgebra`), dense in every `Lᵖ(μ)`, `1 ≤ p < ∞` (`memLp` is the implicit
  requirement `A₀ ⊂ Lᵖ` needed for the density statement to make sense), stable under every smooth
  `ψ : ℝᵏ → ℝ` with `ψ(0) = 0` (`comp_mem`).  Plus the exhaustion sequence of Def. 3.1.1.
* D3: `Γ : A₀ × A₀ → A₀`, symmetric bilinear, `Γ(f,f) ≥ 0`, diffusion property (3.1.2)/(3.4.1).
  The fundamental identity (3.1.1) is a consequence of the diffusion property (the book says so),
  hence not a field.
* D4 (continuity of `g ↦ ∫Γ(f,g)` in `L²`): a consequence of D5 and D6 (Cauchy–Schwarz), hence not a
  field (theorem `DiffusionTriple.exists_bound_D4` in `BGL/Basic.lean`).
* D5: `L` is defined by integration by parts (`ibp`); linearity of `L` on classes and the change of
  variables formula (3.1.8) for `L` are consequences (the book says so), hence not fields.
* D6: `L(A₀) ⊂ A₀`.  D8: `∫ L f dμ = 0`.
* D7, D9: the Dirichlet form, domains and the semigroup are *constructed* from this data
  (Friedrichs), see `Frozen/Semigroup.lean`. -/
structure DiffusionTriple (E : Type*) [MeasurableSpace E] where
  /-- the reference measure (D1). -/
  μ : Measure E
  /-- D1: `μ` is σ-finite. -/
  sigmaFinite : SigmaFinite μ
  /-- D1: when `μ` is finite it is assumed to be a probability measure. -/
  finite_prob : IsFiniteMeasure μ → IsProbabilityMeasure μ
  /-- the test algebra `𝒜₀` (D2), non-unital. -/
  A₀ : NonUnitalSubalgebra ℝ (E → ℝ)
  /-- D2: elements of `𝒜₀` are measurable. -/
  measurable : ∀ f ∈ A₀, Measurable f
  /-- D2: elements of `𝒜₀` are bounded (everywhere). -/
  bounded : ∀ f ∈ A₀, ∃ C : ℝ, ∀ x, |f x| ≤ C
  /-- D2 (implicit): `𝒜₀ ⊂ Lᵖ(μ)` for `1 ≤ p < ∞`. -/
  memLp : ∀ f ∈ A₀, ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ → MemLp f p μ
  /-- D2: `𝒜₀` is dense in every `Lᵖ(μ)`, `1 ≤ p < ∞`. -/
  dense : ∀ p : ℝ≥0∞, ∀ _ : Fact (1 ≤ p), p ≠ ∞ →
    Dense {u : Lp ℝ p μ | ∃ f ∈ A₀, (u : E → ℝ) =ᵐ[μ] f}
  /-- D2: stability under smooth `ψ : ℝᵏ → ℝ` with `ψ(0) = 0`. -/
  comp_mem : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → ψ 0 = 0 →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A₀) → (fun x => ψ (fun i => f i x)) ∈ A₀
  /-- Def. 3.1.1: an exhaustion sequence exists (increasing in `𝒜₀`, tending a.e. to `1`). -/
  exhaustion : ∃ u : ℕ → E → ℝ, IsExhaustion μ A₀ u
  /-- the carré du champ `Γ`. -/
  Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)
  /-- the generator `L`. -/
  L : (E → ℝ) → (E → ℝ)
  /-- D3: `Γ(f,g) ∈ 𝒜₀`. -/
  Γ_mem : ∀ f ∈ A₀, ∀ g ∈ A₀, Γ f g ∈ A₀
  /-- D6: `L(𝒜₀) ⊂ 𝒜₀`. -/
  L_mem : ∀ f ∈ A₀, L f ∈ A₀
  /-- D3: symmetry of `Γ`. -/
  Γ_symm : ∀ f ∈ A₀, ∀ g ∈ A₀, Γ f g =ᵐ[μ] Γ g f
  /-- D3: additivity of `Γ` in the first variable (second variable by symmetry). -/
  Γ_add : ∀ f ∈ A₀, ∀ f' ∈ A₀, ∀ g ∈ A₀, Γ (f + f') g =ᵐ[μ] Γ f g + Γ f' g
  /-- D3: homogeneity of `Γ` in the first variable. -/
  Γ_smul : ∀ (c : ℝ), ∀ f ∈ A₀, ∀ g ∈ A₀, Γ (c • f) g =ᵐ[μ] c • Γ f g
  /-- D3: `Γ(f,f) ≥ 0`. -/
  Γ_nonneg : ∀ f ∈ A₀, 0 ≤ᵐ[μ] Γ f f
  /-- D3: the diffusion property (3.1.2)/(3.4.1): `Γ(ψ(f₁,…,f_k), g) = Σᵢ ∂ᵢψ(f) Γ(fᵢ, g)`. -/
  diffusion : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → ψ 0 = 0 →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A₀) → ∀ g ∈ A₀,
      Γ (fun x => ψ (fun i => f i x)) g =ᵐ[μ]
        fun x => ∑ i, pderiv ψ i (fun j => f j x) * Γ (f i) g x
  /-- D5: integration by parts `∫ g Lf dμ = −∫ Γ(f,g) dμ`, defining `L` on `𝒜₀`. -/
  ibp : ∀ f ∈ A₀, ∀ g ∈ A₀, ∫ x, g x * L f x ∂μ = -∫ x, Γ f g x ∂μ
  /-- D8: `∫ L f dμ = 0`. -/
  integral_L : ∀ f ∈ A₀, ∫ x, L f x ∂μ = 0

end MarkovTriple.BGL
