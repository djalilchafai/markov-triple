import Mathlib
import MarkovTriple.Frozen.MarkovTriple

/-! # The Markov semigroup `P_t = e^{tL}` as an abstract predicate -/

open MeasureTheory
open scoped NNReal

namespace MarkovTriple

variable {E : Type*} [MeasurableSpace E]

/-- `IsSemigroupOf T P`: `P : ℝ≥0 → L²(μ) →L[ℝ] L²(μ)` is *the* symmetric Markov semigroup `e^{tL}`
of the triple `T` (BGL §1.2, §3.2). It is characterised through the `L²`-generator:
* `P 0 = id`, `P (s+t) = P s ∘ P t`, strong continuity at `0`;
* each `P t` is self-adjoint (symmetric w.r.t. `μ`);
* Markov: positivity preserving and `P t 1 = 1`;
* the generator extends `L|𝒜₀`: for `f ∈ 𝒜₀`, `t⁻¹(P_t f − f) → L f` in `L²`.

When `L|𝒜₀` is essentially self-adjoint (see `FullMarkovTriple.esa`) such a `P` is unique, being
`e^{t L̄}`. Without essential self-adjointness the predicate may have several witnesses (one per
self-adjoint extension). Existence is not asserted here (it is a theorem for full triples:
`Hilbert.isSemigroupOf_full`).

Note on the Markov clause `P t 1 = 1`: it is only meaningful when `1 ∈ L²(μ)`, i.e. `μ` finite
(the hypothesis `u =ᵐ 1` with `u ∈ L²` is unsatisfiable for infinite `μ`, and the clause is then
vacuous). Positivity preservation is the only Markov clause with content for infinite `μ`.
The `L^∞`-contractivity (`0 ≤ u ≤ 1 ⇒ 0 ≤ P t u ≤ 1`) is NOT part of the frozen surface. -/
def IsSemigroupOf (T : MarkovTriple E) (P : ℝ≥0 → (Lp ℝ 2 T.μ →L[ℝ] Lp ℝ 2 T.μ)) : Prop :=
  P 0 = ContinuousLinearMap.id ℝ _ ∧
  (∀ s t, P (s + t) = (P s).comp (P t)) ∧
  (∀ u : Lp ℝ 2 T.μ, Filter.Tendsto (fun t => P t u) (nhds 0) (nhds u)) ∧
  (∀ t u v, inner ℝ (P t u) v = inner ℝ u (P t v)) ∧
  (∀ t (u : Lp ℝ 2 T.μ), 0 ≤ᵐ[T.μ] u → 0 ≤ᵐ[T.μ] P t u) ∧
  (∀ t (u : Lp ℝ 2 T.μ), (u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ) → (P t u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ)) ∧
  (∀ f ∈ T.A₀, ∀ u v : Lp ℝ 2 T.μ, (u : E → ℝ) =ᵐ[T.μ] f → (v : E → ℝ) =ᵐ[T.μ] T.L f →
    Filter.Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds v))

end MarkovTriple
