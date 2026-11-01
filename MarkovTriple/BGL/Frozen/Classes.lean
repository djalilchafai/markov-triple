import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple

/-!
# Test functions and their images under `L` as classes in `L²(μ)`

Helper definitions for the statements of S11, F8, F10 (which speak about `L²`-classes) and for the
Friedrichs construction of D7/D9.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- A test function `f ∈ 𝒜₀` as an element of `L²(μ)`. -/
noncomputable def DiffusionTriple.cls (T : DiffusionTriple E) (f : T.A₀) : Lp ℝ 2 T.μ :=
  (T.memLp f.1 f.2 2 (by norm_num) (by simp)).toLp f.1

/-- `L f` (`f ∈ 𝒜₀`, so `L f ∈ 𝒜₀ ⊂ L²`) as an element of `L²(μ)`. -/
noncomputable def DiffusionTriple.Lcls (T : DiffusionTriple E) (f : T.A₀) : Lp ℝ 2 T.μ :=
  (T.memLp (T.L f.1) (T.L_mem f.1 f.2) 2 (by norm_num) (by simp)).toLp (T.L f.1)

end MarkovTriple.BGL
