import Mathlib
import MarkovTriple.BGL.Frozen.Semigroup

/-!
# The Dirichlet domain `𝒟(ℰ)` and the closed Dirichlet form (BGL D4, D7)
-/

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- The Dirichlet domain `𝒟(ℰ) ⊂ L²(μ)`: the completion of `𝒜₀` for the norm
`(‖f‖₂² + ℰ(f))^{1/2}`, realised as the range of the canonical (injective, by closability) map of the
completion to `L²(μ)` (the form domain of the Friedrichs extension). -/
noncomputable def DiffusionTriple.formDomain (T : DiffusionTriple E) :
    Submodule ℝ (MeasureTheory.Lp ℝ 2 T.μ) :=
  (DiffusionTriple.formData T).Q

/-- The closed Dirichlet form `ℰ(u,v)` on `𝒟(ℰ)` (extension by continuity of
`ℰ(f,g) = ∫ Γ(f,g) dμ`, `f,g ∈ 𝒜₀`; BGL D4). -/
noncomputable def DiffusionTriple.closedForm (T : DiffusionTriple E)
    (u v : T.formDomain) : ℝ :=
  (DiffusionTriple.formData T).E u v

end MarkovTriple.BGL
