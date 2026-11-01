import Mathlib
import MarkovTriple.Frozen.MarkovTriple

/-! # Ergodicity of a Markov triple

Ergodicity is deliberately *not* a field of `MarkovTriple` (many natural triples are non-ergodic).
It is a hypothesis of the theorems `CD(ρ,∞) ⇒ PI/LSI` (see ERRATA F1, `Audit/TwoPoint.lean`). -/

open MeasureTheory Filter
open scoped Topology

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- **Ergodicity, L²-closure form** (BGL §3.2 / §4.1: the kernel of the `L²`-closure `L̄` of `L|𝒜₀`
consists of the constants). Here `u ∈ L²` lies in the domain of `L̄` with `L̄ u = 0` iff there is a
sequence `fₙ ∈ 𝒜₀` with `fₙ → u` and `L fₙ → 0` in `L²(μ)` (graph-closure characterisation, so no
`LinearPMap` is needed). Ergodic means every such `u` is a.e. constant. -/
def ErgodicL2 (T : MarkovTriple E) : Prop :=
  ∀ u : Lp ℝ 2 T.μ,
    (∃ f : ℕ → E → ℝ, (∀ n, f n ∈ T.A₀) ∧
      Tendsto (fun n => eLpNorm (f n - (u : E → ℝ)) 2 T.μ) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (T.L (f n)) 2 T.μ) atTop (𝓝 0)) →
    ∃ c : ℝ, (u : E → ℝ) =ᵐ[T.μ] fun _ => c

/-- **Ergodicity, elementary (Γ) form**: `f ∈ 𝒜₀` with `Γ(f,f) = 0` a.e. is a.e. constant.
`ErgodicL2 T → ErgodicΓ T` is proved in `Sanity/Ergodic.lean`. The converse is not claimed. -/
def ErgodicΓ (T : MarkovTriple E) : Prop :=
  ∀ f ∈ T.A₀, (∀ᵐ x ∂T.μ, T.Γ f f x = 0) → ∃ c : ℝ, f =ᵐ[T.μ] fun _ => c

end MarkovTriple
