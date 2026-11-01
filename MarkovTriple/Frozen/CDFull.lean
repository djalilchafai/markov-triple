import Mathlib
import MarkovTriple.Frozen.Gamma2
import MarkovTriple.Frozen.CD
import MarkovTriple.Frozen.FullMarkovTriple

/-! # Curvature-dimension on the extended algebra of a full Markov triple -/

open MeasureTheory
open scoped ENNReal

namespace FullMarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- `CD(ρ,n)` on the *extended* algebra `𝒜` of a full Markov triple (BGL §3.3–3.4; numbering to be
verified): `Γ₂(f) ≥ ρ Γ(f) + (1/n)(Lf)²` μ-a.e. for all `f ∈ 𝒜` (not only `𝒜₀`). This is the form
needed for semigroup interpolation, since `P_t f ∈ 𝒜` (`semigroup_stable`) need not lie in `𝒜₀`.
`MarkovTriple.CD` (on `𝒜₀`) is kept unchanged; `CDFull.toCD` shows the former follows. -/
def CDFull (T : FullMarkovTriple E) (ρ : ℝ) (n : ℝ≥0∞) : Prop :=
  0 < n ∧ ∀ f ∈ T.A, ∀ᵐ x ∂T.μ,
    ρ * T.Γ f f x + (n⁻¹).toReal * (T.L f x) ^ 2 ≤ T.toMarkovTriple.Γ₂ f x

theorem CDFull.toCD {T : FullMarkovTriple E} {ρ : ℝ} {n : ℝ≥0∞} (h : T.CDFull ρ n) :
    T.toMarkovTriple.CD ρ n :=
  ⟨h.1, fun f hf => h.2 f (T.A₀_le hf)⟩

end FullMarkovTriple
