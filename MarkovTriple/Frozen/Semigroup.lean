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
* Markov: positivity preserving, **sub-Markov** (`u ≤ 1` a.e. implies `P t u ≤ 1` a.e., ERRATA N2),
  and `P t 1 = 1`;
* the generator extends `L|𝒜₀`: for `f ∈ 𝒜₀`, `t⁻¹(P_t f − f) → L f` in `L²`.

Uniqueness: when `L|𝒜₀` is essentially self-adjoint (see `FullMarkovTriple.esa`) one expects such a
`P` to be unique, being `e^{t L̄}` (a strongly continuous self-adjoint semigroup is determined by its
generator, and the generator extends the essentially self-adjoint `L|𝒜₀`).  This uniqueness is
**not** formalised and nothing in this repository relies on it as a theorem (ERRATA L1); what is
proved is existence (`Hilbert.isSemigroupOf_full`).  Without essential self-adjointness the
predicate may have several witnesses (one per self-adjoint extension).

Markov clauses.  The sub-Markov clause is stated on representatives of `L²`-classes: for `u ∈ L²`
with `u ≤ 1` a.e. (`u` may be negative and need not vanish at infinity; for infinite `μ` this is a
perfectly satisfiable hypothesis although `1 ∉ L²`) we ask `P t u ≤ 1` a.e.  Together with
positivity this is `L^∞`-contractivity `0 ≤ u ≤ 1 ⇒ 0 ≤ P t u ≤ 1`.  It is **proved** for the
Friedrichs semigroup of every `MarkovTriple` (`Hilbert.tripleSemigroup_subMarkov`).
The clause `P t 1 = 1` is only meaningful when `1 ∈ L²(μ)`, i.e. `μ` finite (the hypothesis
`u =ᵐ 1` with `u ∈ L²` is unsatisfiable for infinite `μ`, and the clause is then vacuous).
Conservativeness for infinite `μ` is the separate predicate `IsConservative`, which is *not* part of
`IsSemigroupOf` (it fails for some bare triples, e.g. Dirichlet semigroups, and for stochastically
incomplete full triples). -/
def IsSemigroupOf (T : MarkovTriple E) (P : ℝ≥0 → (Lp ℝ 2 T.μ →L[ℝ] Lp ℝ 2 T.μ)) : Prop :=
  P 0 = ContinuousLinearMap.id ℝ _ ∧
  (∀ s t, P (s + t) = (P s).comp (P t)) ∧
  (∀ u : Lp ℝ 2 T.μ, Filter.Tendsto (fun t => P t u) (nhds 0) (nhds u)) ∧
  (∀ t u v, inner ℝ (P t u) v = inner ℝ u (P t v)) ∧
  (∀ t (u : Lp ℝ 2 T.μ), 0 ≤ᵐ[T.μ] u → 0 ≤ᵐ[T.μ] P t u) ∧
  (∀ t (u : Lp ℝ 2 T.μ), (u : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ) → (P t u : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ)) ∧
  (∀ t (u : Lp ℝ 2 T.μ), (u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ) → (P t u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ)) ∧
  (∀ f ∈ T.A₀, ∀ u v : Lp ℝ 2 T.μ, (u : E → ℝ) =ᵐ[T.μ] f → (v : E → ℝ) =ᵐ[T.μ] T.L f →
    Filter.Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t u - u)) (nhdsWithin 0 (Set.Ioi 0)) (nhds v))

/-- `IsConservative T P`: the semigroup `P` preserves the integral, `∫ P_t g = ∫ g` for
`g ∈ L¹ ∩ L²` (with `P_t g ∈ L¹`).  A separate hypothesis (not part of `IsSemigroupOf`): it is the
infinite-measure replacement of `P_t 1 = 1` (stochastic completeness); ERRATA N2. -/
def IsConservative (T : MarkovTriple E) (P : ℝ≥0 → (Lp ℝ 2 T.μ →L[ℝ] Lp ℝ 2 T.μ)) : Prop :=
  ∀ (t : ℝ≥0) (g : Lp ℝ 2 T.μ), Integrable (g : E → ℝ) T.μ →
    Integrable (P t g : E → ℝ) T.μ ∧ ∫ x, (P t g : E → ℝ) x ∂T.μ = ∫ x, (g : E → ℝ) x ∂T.μ

end MarkovTriple
