import Mathlib
import MarkovTriple.BGL.Instances.Circle.Poincare
import MarkovTriple.BGL.Theory.LogSobolevDimOne

/-!
# The circle: Poincaré and tight log-Sobolev inequality with the optimal constant `1/(4π²)` (BGL p. 272-273, `n = 1`)

Source: BGL p. 272-273, the case `n = 1` "corresponding to the one-dimensional torus, for which `ρ = 0`":
`P(1)` holds (Prop. 4.5.5), `CD(0,1)` holds, hence the log-Sobolev inequality with constant 1 (equal to the Poincaré constant)
and "the constant is optimal since it is already optimal for the Poincaré inequality".  The library's circle `𝕋 = ℝ/ℤ` has
period `1` (the book's torus `2π`), so the constant is `1/(2π)² = 1/(4π²)`.

* `circle_PI`: `P(1/(4π²))` (`circle_var_le`, Parseval/Wirtinger, `Instances/Circle/Poincare.lean`);
* `circle_LS`: `LS(1/(4π²), 0)` = `CompactTriple.compact_logSobolev_one` with `circle_CD_zero_one`;
* `circle_not_PI_lt`, `circle_not_LS_lt`: both constants are optimal (eigenfunction `cos 2π·`, `λ₁ = (2π)²`; BGL Prop. 5.1.3).
-/

open MeasureTheory
open scoped Real

namespace MarkovTriple.BGL.Circle

open MarkovTriple.Sanity.Circle

/-- **Poincaré inequality on the circle** `ℝ/ℤ`: `Var f ≤ (1/(4π²)) ∫ f'²` (the book's `P(1)` for the `2π`-torus). -/
theorem circle_PI : circleCompact.toDiffusionTriple.PI (1 / (4 * π ^ 2)) := by
  refine ⟨inferInstanceAs (IsProbabilityMeasure μ₀), by positivity, fun f hf => ?_⟩
  exact circle_var_le (f := f) hf

/-- **Log-Sobolev inequality on the circle** `ℝ/ℤ`, constant `1/(4π²)` (BGL p. 273: case `n = 1`, `CD(0,1)`, `P(c) ⟹ LS(c)`). -/
theorem circle_LS : circleCompact.toDiffusionTriple.LS (1 / (4 * π ^ 2)) 0 :=
  circleCompact.compact_logSobolev_one circle_CD_zero_one circle_PI

/-- `∫ (cos 2π x)² dx > 0`. -/
lemma integral_mc_sq_pos : 0 < ∫ x, mc 1 x ^ 2 ∂μ₀ := by
  have hc : Continuous (fun x => mc 1 x ^ 2) := (continuous_of_A₀ (mc_mem 1)).pow 2
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hc
    (HasCompactSupport.of_compactSpace _) (fun x => sq_nonneg _) (x := 0) ?_
  simp [mc]

/-- **The Poincaré constant `1/(4π²)` of the circle is sharp**: `P(c)` fails for `c < 1/(4π²)`
(eigenfunction `cos 2π·`, `L f = -(2π)² f`). -/
theorem circle_not_PI_lt {c : ℝ} (hc : c < 1 / (4 * π ^ 2)) : ¬ circleCompact.toDiffusionTriple.PI c := by
  have hlam : (0 : ℝ) < 4 * π ^ 2 := by positivity
  refine DiffusionTriple.not_PI_of_eigen_pos circleCompact.toDiffusionTriple (f := mc 1) (mc_mem 1)
    (lam := 4 * π ^ 2) hlam ?_ integral_mc_sq_pos hc
  refine Filter.Eventually.of_forall fun x => ?_
  show Lc (mc 1) x = _
  rw [Lc_mc]
  show -(lam 1) * mc 1 x = _
  unfold lam
  push_cast
  ring

/-- **The log-Sobolev constant `1/(4π²)` of the circle is sharp** (BGL p. 273: "The constant is optimal since it is already
optimal for the Poincaré inequality"). -/
theorem circle_not_LS_lt {c : ℝ} (hc : c < 1 / (4 * π ^ 2)) : ¬ circleCompact.toDiffusionTriple.LS c 0 :=
  fun h => circle_not_PI_lt hc (circleCompact.PI_of_LS h)

/-- `LS(1/(4π²), 0)` holds and no smaller constant does. -/
theorem circle_LS_optimal :
    circleCompact.toDiffusionTriple.LS (1 / (4 * π ^ 2)) 0 ∧
      ∀ c : ℝ, c < 1 / (4 * π ^ 2) → ¬ circleCompact.toDiffusionTriple.LS c 0 :=
  ⟨circle_LS, fun _ hc => circle_not_LS_lt hc⟩

end MarkovTriple.BGL.Circle

#print axioms MarkovTriple.BGL.Circle.circle_var_le
#print axioms MarkovTriple.BGL.Circle.circle_PI
#print axioms MarkovTriple.BGL.Circle.circle_LS
#print axioms MarkovTriple.BGL.Circle.circle_LS_optimal
#print axioms MarkovTriple.BGL.Circle.circle_not_PI_lt
#print axioms MarkovTriple.BGL.Circle.circle_not_LS_lt
