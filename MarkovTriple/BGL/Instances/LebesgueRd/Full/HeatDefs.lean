import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.FullEasy

/-!
# Gaussian smoothing (heat flow) on `ℝ^d`: definitions (Round 24, stream A)

`heatRd a φ (x) = E φ(x - a Z)` with `Z ~ N(0, I_d)` (`gam d`); the heat semigroup `e^{tΔ}` is `heatRd (√(2t))`.
Definitions only (no lemmas); the analysis is in `HeatAPI.lean` / `HeatDeriv.lean`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

/-- the standard Gaussian measure `N(0, I_d)` on `ℝ^d = Fin d → ℝ` (product of `d` copies of `N(0,1)`). -/
noncomputable def gam (d : ℕ) : Measure (Fin d → ℝ) := Measure.pi fun _ => gaussianReal 0 1

instance : IsProbabilityMeasure (gam d) := by unfold gam; infer_instance

/-- Gaussian smoothing `x ↦ E φ(x - a Z)`. -/
noncomputable def heatRd (a : ℝ) (φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∫ z, φ (x - a • z) ∂(gam d)

open scoped Classical in
/-- the `L²(ℝ^d)` class of `heatRd a φ` (junk value `0` if it is not in `L²`; it is in `L²` for `φ ∈ 𝒜₀`,
`memLp_heatRd`). -/
noncomputable def heatL2 (φ : (Fin d → ℝ) → ℝ) (a : ℝ) : Lp ℝ 2 (volume : Measure (Fin d → ℝ)) :=
  if h : MemLp (heatRd a φ) 2 volume then h.toLp (heatRd a φ) else 0

end MarkovTriple.BGL.LebesgueRd
