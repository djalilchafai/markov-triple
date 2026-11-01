import Mathlib
import MarkovTriple.Frozen.PartialDeriv

/-!
# Markov triples (Bakry–Gentil–Ledoux, Definition 3.1.8)
-/

open MeasureTheory
open scoped ENNReal

/-- A **(standard) Markov triple** `(E, μ, Γ)` in the sense of Bakry–Gentil–Ledoux,
*Analysis and Geometry of Markov Diffusion Operators*, Definition 3.1.8 (with Definitions 3.1.1–3.1.7).

The generator `L` and the carré du champ `Γ` are both data, tied by the *pointwise* carré-du-champ
identity (BGL (3.1.1)/(1.4.1)); integration by parts (BGL (3.1.2)) is a field.
Both `Γ` and `L` live on `E → ℝ` but are only constrained on the test algebra `A₀`.
Every analytic requirement is a field; nothing is an axiom.

Deviations from BGL, discussed in `FROZEN_REVIEW.md`:
* `A₀` is a unital `Subalgebra`, so constants lie in `A₀` (this forces `μ` finite, since `1 ∈ Lᵖ`).
* The diffusion property is required only when `ψ(f₁,…,f_k) ∈ A₀` (no stability of `A₀` under all
  smooth `ψ` is demanded, so that polynomial algebras, e.g. for Ornstein–Uhlenbeck, are allowed).
* `L 1 = 0` is not a field: it is the case `k = 0`, `ψ ≡ 1` of the chain rule. -/
structure MarkovTriple (E : Type*) [MeasurableSpace E] where
  /-- the reference measure (σ-finite; in fact finite because `1 ∈ A₀ ⊆ Lᵖ`). -/
  μ : Measure E
  /-- σ-finiteness of `μ`. -/
  sigmaFinite : SigmaFinite μ
  /-- the algebra of test functions `𝒜₀` (BGL Def. 3.1.1). Contains the constants. -/
  A₀ : Subalgebra ℝ (E → ℝ)
  /-- the carré du champ `Γ`. -/
  Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)
  /-- the generator `L`. -/
  L : (E → ℝ) → (E → ℝ)
  /-- test functions are measurable. -/
  measurable : ∀ f ∈ A₀, Measurable f
  /-- `𝒜₀ ⊆ ⋂_{p<∞} Lᵖ(μ)` (BGL Def. 3.1.1). -/
  memLp : ∀ f ∈ A₀, ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ
  /-- `Γ : 𝒜₀ × 𝒜₀ → 𝒜₀`. -/
  Γ_mem : ∀ f ∈ A₀, ∀ g ∈ A₀, Γ f g ∈ A₀
  /-- `L : 𝒜₀ → 𝒜₀`. -/
  L_mem : ∀ f ∈ A₀, L f ∈ A₀
  /-- symmetry of `Γ` on `𝒜₀`. -/
  Γ_symm : ∀ f ∈ A₀, ∀ g ∈ A₀, Γ f g = Γ g f
  /-- additivity of `Γ` in the first variable (the second follows by symmetry). -/
  Γ_add : ∀ f ∈ A₀, ∀ f' ∈ A₀, ∀ g ∈ A₀, Γ (f + f') g = Γ f g + Γ f' g
  /-- homogeneity of `Γ` in the first variable. -/
  Γ_smul : ∀ (c : ℝ), ∀ f ∈ A₀, ∀ g ∈ A₀, Γ (c • f) g = c • Γ f g
  /-- positivity `Γ(f,f) ≥ 0`, pointwise. -/
  Γ_nonneg : ∀ f ∈ A₀, ∀ x, 0 ≤ Γ f f x
  /-- additivity of `L` on `𝒜₀`. -/
  L_add : ∀ f ∈ A₀, ∀ g ∈ A₀, L (f + g) = L f + L g
  /-- homogeneity of `L` on `𝒜₀`. -/
  L_smul : ∀ (c : ℝ), ∀ f ∈ A₀, L (c • f) = c • L f
  /-- the **pointwise** carré du champ identity `2Γ(f,g) = L(fg) − f Lg − g Lf` (BGL (1.4.1)). -/
  carre_du_champ : ∀ f ∈ A₀, ∀ g ∈ A₀, ∀ x,
    Γ f g x = (L (f * g) x - f x * L g x - g x * L f x) / 2
  /-- integration by parts `∫ g Lf dμ = −∫ Γ(f,g) dμ` (BGL (3.1.2)). -/
  ibp : ∀ f ∈ A₀, ∀ g ∈ A₀, ∫ x, g x * L f x ∂μ = -∫ x, Γ f g x ∂μ
  /-- `𝒜₀` is dense in `Lᵖ(μ)`, `1 ≤ p < ∞` (BGL Def. 3.1.1). -/
  dense : ∀ p : ℝ≥0∞, ∀ _ : Fact (1 ≤ p), p ≠ ∞ →
    Dense {u : Lp ℝ p μ | ∃ f ∈ A₀, (u : E → ℝ) =ᵐ[μ] f}
  /-- the **diffusion property** (BGL Def. 3.1.8 / (1.11.2)–(1.11.3)): chain rule for smooth `ψ`
  and `f₁,…,f_k ∈ 𝒜₀` whenever `ψ(f₁,…,f_k) ∈ 𝒜₀`:
  `Γ(ψ(f),g) = Σᵢ ∂ᵢψ(f) Γ(fᵢ,g)` and
  `L ψ(f) = Σᵢ ∂ᵢψ(f) L fᵢ + Σᵢⱼ ∂ᵢ∂ⱼψ(f) Γ(fᵢ,fⱼ)`. -/
  diffusion : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A₀) → (fun x => ψ (fun i => f i x)) ∈ A₀ →
      (∀ g ∈ A₀, Γ (fun x => ψ (fun i => f i x)) g =
        fun x => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j x) * Γ (f i) g x) ∧
      L (fun x => ψ (fun i => f i x)) =
        fun x => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j x) * L (f i) x +
          ∑ i, ∑ j, MarkovTriple.pderiv₂ ψ i j (fun l => f l x) * Γ (f i) (f j) x
