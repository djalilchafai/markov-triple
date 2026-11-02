import Mathlib
import MarkovTriple.BGL.Frozen.Semigroup

/-!
# Standard Markov Triples (BGL Definition 3.1.15; hypotheses S10, S11)
-/

open MeasureTheory Filter
open scoped NNReal Topology LinearPMap

namespace MarkovTriple.BGL

/-- A **Standard Markov Triple** (BGL Def. 3.1.15, §3.4.2): a Diffusion Markov Triple whose generator
and semigroup are ergodic and conservative.

* S10 (`ergodic`, Def. 3.1.11): every `f ∈ 𝒟(L)` with `L f = 0` is (a.e.) constant (in particular `0`
  if `μ` is infinite).  The book's equivalent form (`f ∈ 𝒟(ℰ)`, `Γ(f) = 0` ⇒ constant) is not a
  field (it requires `Γ` on `𝒟(ℰ)`; theorem `StandardTriple.energy_zero_const`).  D4 (continuity of
  `g ↦ ∫ Γ(f,g)`) is likewise a theorem, `DiffusionTriple.exists_bound_D4`.
* S11 (`conservative`, Def. 3.1.12): `P_t(1) = 1`.  The book lets `P_t` act on bounded measurable
  functions, so that this makes sense for infinite `μ` (`1 ∉ L²`); `1` is the a.e. limit of the
  exhaustion sequence of Def. 3.1.1 (cf. the remark after Def. 3.1.9).  Encoding: for **every
  nonnegative** exhaustion sequence `u` (`IsExhaustion`, and `0 ≤ u_n` a.e. for all `n`),
  `P_t u_n → 1` a.e. as `n → ∞`, for every `t ≥ 0`.  When `μ` is a probability measure this is
  `P_t 1 = 1` in `L²`.  The restriction to nonnegative sequences is harmless: positivity and the
  sub-Markov property of `P_t` are theorems (`BGL/Semigroup/Markov.lean`), and then the statement
  for ONE exhaustion sequence implies it for ALL exhaustion sequences, signed or not
  (`StandardTriple.conservative_all`, `BGL/Semigroup/Conservative.lean`); nonnegative
  exhaustion sequences exist (`DiffusionTriple.exists_nonneg_exhaustion`).
Positivity preservation and sub-Markov are *theorems* about `DiffusionTriple.semigroup`. -/
structure StandardTriple (E : Type*) [MeasurableSpace E] extends DiffusionTriple E where
  /-- S10: ergodicity. -/
  ergodic : ∀ (u : Lp ℝ 2 μ) (hu : u ∈ toDiffusionTriple.generator.domain),
    toDiffusionTriple.generator ⟨u, hu⟩ = 0 → ∃ c : ℝ, (u : E → ℝ) =ᵐ[μ] fun _ => c
  /-- S11: conservativeness `P_t(1) = 1`, through exhaustion sequences. -/
  conservative : ∀ (u : ℕ → E → ℝ) (hu : IsExhaustion μ A₀ u), (∀ n, 0 ≤ᵐ[μ] u n) → ∀ (t : ℝ≥0),
    ∀ᵐ x ∂μ, Tendsto (fun n => (toDiffusionTriple.semigroup t
      (toDiffusionTriple.cls ⟨u n, hu.1 n⟩) : E → ℝ) x) atTop (𝓝 1)

end MarkovTriple.BGL
