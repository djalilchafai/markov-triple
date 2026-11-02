import Mathlib
import MarkovTriple.BGL.Frozen.Energy
import MarkovTriple.BGL.Frozen.Ent
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-! # Logarithmic Sobolev inequality (BGL Definition 5.1.1) -/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- Logarithmic Sobolev inequality `LS(C, D)` (BGL Def. 5.1.1), generic in `(μ, Γ)`: `μ` is a
probability measure, `C > 0`, `D ≥ 0`, and `Ent_μ(f²) ≤ 2 C ℰ(f) + D ∫ f² dμ` for all `f` in the class
`𝒞` (the book: all `f ∈ 𝒟(ℰ)`, enough on a dense family).
**Hazards (audit R2/L1):** true for `𝒞 = ∅` for every probability `μ` and every `Γ`; `Ent` has junk values
off its guard `IsEntAdmissible` (`BGL/Guards.lean`), which holds for `f²` with `f` bounded in `L²`.
Use it only through `DiffusionTriple.LS` (class `T.A₀`, `DiffusionTriple.LS.extend`).  The tight inequality `LS(C)` is
`D = 0`; for the standard Gaussian it holds with `C = 1`. -/
def LogSobolevIneq (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (𝒞 : Set (E → ℝ))
    (C D : ℝ) : Prop :=
  IsProbabilityMeasure μ ∧ 0 < C ∧ 0 ≤ D ∧
    ∀ f ∈ 𝒞, Ent μ (fun x => f x ^ 2) ≤ 2 * C * energy μ Γ f + D * ∫ x, f x ^ 2 ∂μ

/-- **Triple-bound logarithmic Sobolev inequality** `LS(C, D)` of a diffusion triple (BGL Def. 5.1.1):
the generic `LogSobolevIneq` for the triple's own `μ`, `Γ`, on the test class `𝒜₀` (bounded functions,
so `f² log f²` is integrable and `Ent` is a genuine entropy: `DiffusionTriple.integrable_sq_mul_log_sq`). -/
def DiffusionTriple.LS (T : DiffusionTriple E) (C D : ℝ) : Prop :=
  LogSobolevIneq T.μ T.Γ (T.A₀ : Set (E → ℝ)) C D

end MarkovTriple.BGL
