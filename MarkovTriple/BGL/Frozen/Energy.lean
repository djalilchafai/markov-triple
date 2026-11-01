import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-!
# Dirichlet form and energy, generic in `(μ, Γ)` (BGL (3.1.10), Def. 3.1.8)
-/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- The Dirichlet form `ℰ(f, g) = ∫ Γ(f,g) dμ` (BGL (3.1.10)), for a measure `μ` and a bilinear
operator `Γ`; for a diffusion triple it is meant for `f, g ∈ 𝒜₀` (its closure, with domain `𝒟(ℰ)`,
is `FormData.E` of the Friedrichs construction, see `Frozen/Semigroup.lean`). -/
noncomputable def dirichletForm (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ))
    (f g : E → ℝ) : ℝ :=
  ∫ x, Γ f g x ∂μ

/-- The energy `ℰ(f) = ℰ(f,f)`. -/
noncomputable def energy (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (f : E → ℝ) : ℝ :=
  dirichletForm μ Γ f f

/-- **Triple-bound Dirichlet form on the test class** `𝒜₀` (BGL (3.1.10)): `ℰ(f,g) = ∫ Γ(f,g) dμ` for
`f, g ∈ 𝒜₀`, with the triple's own `μ` and `Γ`.  Restricted to the subtype `𝒜₀`: there is no junk value
(`Γ(f,g) ∈ 𝒜₀ ⊂ L¹`, `DiffusionTriple.integrable_of_mem`).  Its closure is
`DiffusionTriple.closedForm` (`closedForm_cls`). -/
noncomputable def DiffusionTriple.ℰ (T : DiffusionTriple E) (f g : T.A₀) : ℝ :=
  dirichletForm T.μ T.Γ f.1 g.1

end MarkovTriple.BGL
