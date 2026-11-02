import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-!
# Completeness (BGL Definition 3.3.9)
-/

open MeasureTheory Filter
open scoped Topology

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- **Completeness** of a Diffusion Markov Triple (BGL Def. 3.3.9): there is an increasing sequence
`(ζ_k)_{k ≥ 1}` of positive functions of `𝒜₀` with `ζ_k → 1` almost everywhere and `√Γ(ζ_k) ≤ 1/k`.

Encoding choices (all faithful readings of the book's conventions):
* the sequence is indexed by `k : ℕ` and the bound `√Γ(ζ_k) ≤ 1/k` becomes `Γ(ζ_k) ≤ 1/(k+1)²`
  (index shift, so that `k = 0` is not a division by zero), a.e. and stated for the field `T.Γ` on `𝒜₀`
  (`Γ(ζ_k) ∈ 𝒜₀` is a bounded function);
* "positive" is `0 ≤ ζ_k` a.e. (the book's convention for positive = nonnegative), "increasing" and
  "convergence to `1`" are a.e., exactly as for the exhaustion sequence of Def. 3.1.1
  (so a complete triple has a nonnegative exhaustion sequence with `√Γ(ζ_k) ≤ 1/(k+1)`,
  `DiffusionTriple.IsComplete.isExhaustion`).
It is a hypothesis about the triple, not a field of the structures (`DiffusionTriple` is stated before
the extended algebra; Thm 3.3.23 is the theorem that uses it). -/
def DiffusionTriple.IsComplete (T : DiffusionTriple E) : Prop :=
  ∃ ζ : ℕ → E → ℝ, (∀ k, ζ k ∈ T.A₀) ∧ (∀ k, 0 ≤ᵐ[T.μ] ζ k) ∧ (∀ k, ζ k ≤ᵐ[T.μ] ζ (k + 1)) ∧
    (∀ᵐ x ∂T.μ, Tendsto (fun k => ζ k x) atTop (𝓝 1)) ∧
    ∀ k, T.Γ (ζ k) (ζ k) ≤ᵐ[T.μ] fun _ => (1 / ((k : ℝ) + 1)) ^ 2

end MarkovTriple.BGL
