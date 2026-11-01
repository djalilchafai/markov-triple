import Mathlib
import MarkovTriple.BGL.Frozen.Energy
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-! # Poincaré inequality (BGL Definition 4.2.1) -/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- Poincaré inequality `P(C)` (BGL Def. 4.2.1), generic in `(μ, Γ)`: `μ` is a probability measure,
`C > 0`, and `Var_μ(f) ≤ C ℰ(f)` for all `f` in the class `𝒞`.  The book states it on the Dirichlet
domain `𝒟(ℰ)` and remarks that it suffices to check it on a dense family such as `𝒜₀`; here `𝒞` is
the family (take `𝒞 = T.A₀`, or `T.A` with `ΓA` for a full triple).  Variance is Mathlib's
`ProbabilityTheory.variance` (for a probability measure `∫ (f − ∫ f)² dμ`). -/
def PoincareIneq (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (𝒞 : Set (E → ℝ))
    (C : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ 0 < C ∧ ∀ f ∈ 𝒞, ProbabilityTheory.variance f μ ≤ C * energy μ Γ f

/-- **Triple-bound Poincaré inequality** `P(C)` of a diffusion triple (BGL Def. 4.2.1): the generic
`PoincareIneq` for the triple's own `μ`, `Γ`, on the test class `𝒜₀` (bounded functions: no Bochner
junk).  Not vacuous (`𝒜₀` is the triple's test algebra, dense in `L²`), and equivalent to the
book's statement on `𝒟(ℰ)`: `𝒜₀` is dense in the form domain
(`DiffusionTriple.formDomain_approx`) and the inequality extends (`DiffusionTriple.PI.extend`). -/
def DiffusionTriple.PI (T : DiffusionTriple E) (C : ℝ) : Prop :=
  PoincareIneq T.μ T.Γ (T.A₀ : Set (E → ℝ)) C

end MarkovTriple.BGL
