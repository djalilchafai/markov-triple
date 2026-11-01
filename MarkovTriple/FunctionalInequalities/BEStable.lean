import Mathlib
import MarkovTriple.FunctionalInequalities.BEAlg
import MarkovTriple.FunctionalInequalities.BEFlow

/-! # `BEStable`: the regularity hypothesis of the Bakry–Émery semigroup argument

`BEStable F` collects EVERY analytic requirement of the classical proof that is not a consequence
of the frozen fields of `FullMarkovTriple` (see `BE_STATUS.md`):

* `A₀_bdd`: the test functions are essentially bounded;
* `reg`: for a test function `φ`, a time `s > 0` and ANY function `g ∈ 𝒜` representing `P_s φ`, and
  any smooth `ψ : ℝ → ℝ`, the function `ψ ∘ g` satisfies `BEReg`: `ψ∘g`, `L(ψ∘g)`, `Γ(ψ∘g)` are
  essentially bounded, `L L (ψ∘g)` and `L Γ(ψ∘g)` are in `L²`.

(`ψ ∘ g` ranges over the compositions needed to form `log P_s h` and `P_s h = exp log P_s h`.)
Both clauses hold on any compact full triple with `𝒜₀ = 𝒜` (`BECircle.lean`). -/

open MeasureTheory
open scoped NNReal ENNReal

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E]

structure BEStable (F : FullMarkovTriple E) : Prop where
  A₀_bdd : ∀ f ∈ F.A₀, MemLp f ∞ F.μ
  reg : ∀ (φ : E → ℝ) (hφ : φ ∈ F.A₀) (s : ℝ≥0), 0 < s → ∀ g ∈ F.A,
    ((Hilbert.tripleSemigroup F.toMarkovTriple s (cl F hφ) : Lp ℝ 2 F.μ) : E → ℝ) =ᵐ[F.μ] g →
    ∀ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → BEReg F (fun x => ψ (g x))

/-- **`BEStable` for full triples with `𝒜 = 𝒜₀` and bounded test functions** (e.g. every compact
example: the circle, `BECircle.lean`): all the required functions lie in `𝒜₀`, hence are bounded. -/
theorem BEStable.of_A_eq_A₀ (F : FullMarkovTriple E) (hA : ∀ f ∈ F.A, f ∈ F.A₀)
    (hb : ∀ f ∈ F.A₀, MemLp f ∞ F.μ) : BEStable F := by
  refine ⟨hb, ?_⟩
  intro φ hφ s hs g hgA _ ψ hψ
  have hc : (fun x => ψ (g x)) ∈ F.A := comp_mem_A F hψ hgA
  have hL : F.L (fun x => ψ (g x)) ∈ F.A := F.L_mem_A _ hc
  have hΓ : F.Γ (fun x => ψ (g x)) (fun x => ψ (g x)) ∈ F.A := F.Γ_mem_A _ hc _ hc
  exact ⟨hb _ (hA _ hc), hb _ (hA _ hL), hb _ (hA _ hΓ),
    F.memLp _ (hA _ (F.L_mem_A _ hL)) 2 (by norm_num) (by simp),
    F.memLp _ (hA _ (F.L_mem_A _ hΓ)) 2 (by norm_num) (by simp)⟩

end MarkovTriple.BE
