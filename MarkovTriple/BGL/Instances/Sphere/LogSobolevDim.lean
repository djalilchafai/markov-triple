import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Consequences
import MarkovTriple.BGL.Theory.LogSobolevDim

/-!
# Log-Sobolev inequality on the zonal `S³` with the finite-dimensional constant (BGL Thm 5.7.4, `n = 3`)

The zonal sphere `S³ ⊂ ℝ⁴` (`sCompact`) satisfies `CD(2,3)` (`sphere_CD_two_three`, the equality case
`CD(n-1,n)` of the book, p. 272: "Theorem 5.7.4 applies to the sphere `Sⁿ`").  With `ρ = 2`, `n = 3`
Thm 5.7.4 gives `C = (n-1)/(ρ n) = (3-1)/(2·3) = 1/3`, strictly better than the `n`-independent
`1/ρ = 1/2` of Prop. 5.7.1 (`sphere_LS`), and equal to the (sharp) Poincaré constant `1/λ₁ = 1/3`
(`sphere_PI'`; the book: "the lower bound `ρn/(n-1)` of the log-Sobolev constant being optimal").
Unconditional: `CompactTriple.compact_logSobolev_dim`.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.Sphere

/-- **BGL Thm 5.7.4 on the zonal `S³`**: `LS(1/3, 0)`, i.e. `Ent(f²) ≤ (2/3) ∫ Γ(f)` for `f ∈ 𝒜₀`
(`CD(2,3)`, constant `(n-1)/(ρ n) = 1/3`).  Unconditional. -/
theorem sphere_LS_dim : sCompact.toDiffusionTriple.LS (1 / 3) 0 := by
  have h := sCompact.compact_logSobolev_dim (n := 3) (ρ := 2) (by norm_num) (by norm_num)
    (by simp) sphere_CD_two_three
  have e : MarkovTriple.BGL.dimLSConst 2 3 = 1 / 3 := by
    unfold MarkovTriple.BGL.dimLSConst
    rw [ENNReal.toReal_inv]
    norm_num
  rwa [e] at h

/-- non-vacuity of the named input of Thm 5.7.4 (`n < ∞`): on the zonal `S³` the structure
`FiniteDimInterpolation (ρ n/(n-1))`, `ρ = 2`, `n = 3` (`κ = 3`) is a theorem, not a hypothesis. -/
theorem sphere_finiteDimInterpolation :
    sCompact.toFullTriple.FiniteDimInterpolation (2 * ((3 : ℝ≥0∞).toReal / ((3 : ℝ≥0∞).toReal - 1))) :=
  sCompact.finiteDimInterpolation sphere_CD_two_three (by norm_num) (by simp)

/-- the improvement over the `n`-independent constant `1/2` of `sphere_LS`. -/
theorem sphere_LS_dim_lt : (1 / 3 : ℝ) < 1 / 2 := by norm_num

end MarkovTriple.BGL.Instances.Sphere

#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_finiteDimInterpolation
#print axioms MarkovTriple.BGL.Instances.Sphere.sphere_LS_dim
