import Mathlib
import MarkovTriple.BGL.Theory.Strong.CompactMain
import MarkovTriple.BGL.Instances.OUCompact.Consequences
import MarkovTriple.BGL.Instances.Circle.Triple
import MarkovTriple.BGL.Instances.Sphere.Consequences

/-!
# Strong gradient bounds (BGL Thm 3.3.18) for the concrete compact triples

`√Γ(P_t f) ≤ e^{-ρt} P_t(√Γ f)` for the circle (`ρ = 0`), the compact-type Ornstein–Uhlenbeck triple
(`ρ = 1`) and the round sphere (`ρ = 2`, the constant proved for the sphere triple), unconditionally.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

theorem circle_strong_gradient_bound (f : Circle.circleCompact.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂Circle.circleCompact.μ, Real.sqrt
      (Circle.circleCompact.toFullTriple.toDiffusionTriple.ΓA (Circle.circleCompact.Pt t f)
        (Circle.circleCompact.Pt t f) x) ≤ Real.exp (-0 * t) *
      (Circle.circleCompact.toDiffusionTriple.semigroup t
        (Circle.circleCompact.toFullTriple.sqrtΓcls f) : Lp ℝ 2 Circle.circleCompact.μ) x :=
  compact_strong_gradient_bound _ Circle.circle_CD_zero_top le_rfl f t

theorem ouBCompact_strong_gradient_bound (f : Instances.OUCompact.ouBCompact.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂Instances.OUCompact.ouBCompact.μ, Real.sqrt
      (Instances.OUCompact.ouBCompact.toFullTriple.toDiffusionTriple.ΓA
        (Instances.OUCompact.ouBCompact.Pt t f) (Instances.OUCompact.ouBCompact.Pt t f) x) ≤
      Real.exp (-1 * t) * (Instances.OUCompact.ouBCompact.toDiffusionTriple.semigroup t
        (Instances.OUCompact.ouBCompact.toFullTriple.sqrtΓcls f) :
          Lp ℝ 2 Instances.OUCompact.ouBCompact.μ) x :=
  compact_strong_gradient_bound _ Instances.OUCompact.ouBCompact_CD zero_le_one f t

theorem sphere_strong_gradient_bound (f : Instances.Sphere.sCompact.A₀) (t : ℝ≥0) :
    ∀ᵐ x ∂Instances.Sphere.sCompact.μ, Real.sqrt
      (Instances.Sphere.sCompact.toFullTriple.toDiffusionTriple.ΓA
        (Instances.Sphere.sCompact.Pt t f) (Instances.Sphere.sCompact.Pt t f) x) ≤
      Real.exp (-2 * t) * (Instances.Sphere.sCompact.toDiffusionTriple.semigroup t
        (Instances.Sphere.sCompact.toFullTriple.sqrtΓcls f) :
          Lp ℝ 2 Instances.Sphere.sCompact.μ) x :=
  compact_strong_gradient_bound _ Instances.Sphere.sphere_CD_two_three (by norm_num) f t

end MarkovTriple.BGL

#print axioms MarkovTriple.BGL.compact_strong_gradient_bound
#print axioms MarkovTriple.BGL.circle_strong_gradient_bound
#print axioms MarkovTriple.BGL.ouBCompact_strong_gradient_bound
#print axioms MarkovTriple.BGL.sphere_strong_gradient_bound
