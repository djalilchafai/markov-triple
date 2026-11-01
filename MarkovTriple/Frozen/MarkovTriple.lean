import Mathlib
import MarkovTriple.Frozen.PartialDeriv

/-!
# Markov triples (Bakry–Gentil–Ledoux, Definition 3.1.8)
-/

open MeasureTheory
open scoped ENNReal

/-- A **(standard) Markov triple** `(E, μ, Γ)` in the sense of Bakry–Gentil–Ledoux,
*Analysis and Geometry of Markov Diffusion Operators*, §3.1 (Definitions 3.1.1–3.1.8; numbering
unverified, see `FROZEN_REVIEW.md`).

The generator `L` and the carré du champ `Γ` are both data, tied by the *pointwise* carré-du-champ
identity (BGL (3.1.1)/(1.4.1)); integration by parts (BGL (3.1.2)) is a field.
Both `Γ` and `L` live on `E → ℝ` but are only constrained on the test algebra `A₀`.
Every analytic requirement is a field; nothing is an axiom.

Design (DECISIONS items 8–11, following BGL):
* `μ` is σ-finite, **not necessarily finite** (Lebesgue measure on `ℝ` is admissible,
  see `Sanity/Lebesgue.lean`).
* `A₀` is a **non-unital** algebra (`NonUnitalSubalgebra`): it need *not* contain the constants
  (constants are not in `⋂ Lᵖ` when `μ` is infinite).  Constants belong to the extended algebra `𝒜`
  of a `FullMarkovTriple`.
* `A₀` is stable under composition with every smooth `ψ : ℝᵏ → ℝ` with `ψ(0) = 0`
  (`comp_mem`; BGL's "diffusion algebra" hypothesis).  Consequently the chain rule
  (`diffusion`) is unconditional on `A₀`, and truncations such as `√(f²+ε²) − ε` stay in `A₀`
  (this is what makes the Markov property of the form a *theorem*, `Hilbert/MarkovCriterion.lean`).
* `L 1 = 0` is no longer visible here (`1 ∉ A₀`); it is the case `k = 0` of the chain rule on `𝒜`
  in `FullMarkovTriple`. -/
structure MarkovTriple (E : Type*) [MeasurableSpace E] where
  /-- the reference measure (σ-finite, possibly infinite). -/
  μ : Measure E
  /-- σ-finiteness of `μ`. -/
  sigmaFinite : SigmaFinite μ
  /-- the algebra of test functions `𝒜₀` (BGL Def. 3.1.1): non-unital. -/
  A₀ : NonUnitalSubalgebra ℝ (E → ℝ)
  /-- the carré du champ `Γ`. -/
  Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)
  /-- the generator `L`. -/
  L : (E → ℝ) → (E → ℝ)
  /-- test functions are measurable. -/
  measurable : ∀ f ∈ A₀, Measurable f
  /-- `𝒜₀ ⊆ ⋂_{p<∞} Lᵖ(μ)` (BGL Def. 3.1.1). -/
  memLp : ∀ f ∈ A₀, ∀ p : ℝ≥0∞, p ≠ ∞ → MemLp f p μ
  /-- `𝒜₀` is stable under composition with smooth `ψ : ℝᵏ → ℝ`, `ψ(0) = 0`
  (BGL Def. 3.1.1/3.1.8; for `k = 0` this only says `0 ∈ 𝒜₀`). -/
  comp_mem : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → ψ 0 = 0 →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A₀) → (fun x => ψ (fun i => f i x)) ∈ A₀
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
  /-- the **pointwise** carré du champ identity `2Γ(f,g) = L(fg) − f Lg − g Lf` (BGL (1.4.1)),
  only for `f, g ∈ 𝒜₀` (all products are taken inside the algebra `𝒜₀`; no unit is used). -/
  carre_du_champ : ∀ f ∈ A₀, ∀ g ∈ A₀, ∀ x,
    Γ f g x = (L (f * g) x - f x * L g x - g x * L f x) / 2
  /-- integration by parts `∫ g Lf dμ = −∫ Γ(f,g) dμ` (BGL (3.1.2)); symmetric in `(f,g)` because
  `Γ` is symmetric.  Integrability of both sides follows from `memLp`, `Γ_mem`, `L_mem`. -/
  ibp : ∀ f ∈ A₀, ∀ g ∈ A₀, ∫ x, g x * L f x ∂μ = -∫ x, Γ f g x ∂μ
  /-- `𝒜₀` is dense in `Lᵖ(μ)`, `1 ≤ p < ∞` (BGL Def. 3.1.1). -/
  dense : ∀ p : ℝ≥0∞, ∀ _ : Fact (1 ≤ p), p ≠ ∞ →
    Dense {u : Lp ℝ p μ | ∃ f ∈ A₀, (u : E → ℝ) =ᵐ[μ] f}
  /-- the **diffusion property** (BGL Def. 3.1.8 / (1.11.2)–(1.11.3)): chain rule for smooth `ψ`
  with `ψ(0) = 0` and `f₁,…,f_k ∈ 𝒜₀` (`ψ(f₁,…,f_k) ∈ 𝒜₀` by `comp_mem`):
  `Γ(ψ(f),g) = Σᵢ ∂ᵢψ(f) Γ(fᵢ,g)` and
  `L ψ(f) = Σᵢ ∂ᵢψ(f) L fᵢ + Σᵢⱼ ∂ᵢ∂ⱼψ(f) Γ(fᵢ,fⱼ)`. -/
  diffusion : ∀ (k : ℕ) (ψ : (Fin k → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → ψ 0 = 0 →
    ∀ f : Fin k → (E → ℝ), (∀ i, f i ∈ A₀) →
      (∀ g ∈ A₀, Γ (fun x => ψ (fun i => f i x)) g =
        fun x => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j x) * Γ (f i) g x) ∧
      L (fun x => ψ (fun i => f i x)) =
        fun x => ∑ i, MarkovTriple.pderiv ψ i (fun j => f j x) * L (f i) x +
          ∑ i, ∑ j, MarkovTriple.pderiv₂ ψ i j (fun l => f l x) * Γ (f i) (f j) x
