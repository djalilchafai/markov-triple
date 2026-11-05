import Mathlib

/-!
# Round 29 (P), part 2: the 1-D boundary identity behind the `n = ∞` converse question

Statements `P5`, `P6` of `STATEMENTS_R29_P.md`.  Pure real analysis: with `u = f' √w`, `w = e^{-V}`, `V1 = V'`, `V2 = V''`,
`∫ (Lf)² w = ∫ (u' - V1 u/2)²` and `∫ (f'')² w = ∫ (u' + V1 u/2)²`.  The two differ by a boundary term and `∫ V2 u²`.
This is NOT connected to a `FullTriple`; it records the mechanism, by which, on an end where `V1 ≤ 0`, `Lf ∈ L²` follows from `f'' ∈ L²` and `∫ V2 u² < ∞`.
-/

open MeasureTheory intervalIntegral Set

namespace MarkovTriple.Stochastic.R29P

variable {u u' V1 V2 : ℝ → ℝ} {a b : ℝ}

/-- **P5.** -/
theorem oneD_boundary_identity (hab : a ≤ b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x) (hV : ∀ x ∈ Icc a b, HasDerivAt V1 (V2 x) x)
    (hu' : ContinuousOn u' (Icc a b)) (hV2 : ContinuousOn V2 (Icc a b)) :
    ∫ x in a..b, (u' x - V1 x * u x / 2) ^ 2 =
      (∫ x in a..b, (u' x + V1 x * u x / 2) ^ 2) - (V1 b * u b ^ 2 - V1 a * u a ^ 2)
        + ∫ x in a..b, V2 x * u x ^ 2 := by
  have hcu : ContinuousOn u (Icc a b) := fun x hx => (hu x hx).continuousAt.continuousWithinAt
  have hcV : ContinuousOn V1 (Icc a b) := fun x hx => (hV x hx).continuousAt.continuousWithinAt
  have hI : ∀ {g : ℝ → ℝ}, ContinuousOn g (Icc a b) → IntervalIntegrable g volume a b := fun hg =>
    hg.intervalIntegrable_of_Icc hab
  have hG : ∀ x ∈ uIcc a b, HasDerivAt (fun x => V1 x * u x ^ 2)
      (V2 x * u x ^ 2 + V1 x * (2 * u x * u' x)) x := by
    intro x hx
    rw [uIcc_of_le hab] at hx
    have := (hV x hx).mul ((hu x hx).pow 2)
    convert this using 1
    simp
  have hFTC := integral_eq_sub_of_hasDerivAt hG
    (hI ((hV2.mul (hcu.pow 2)).add (hcV.mul ((continuousOn_const.mul hcu).mul hu'))))
  have h1 : ∫ x in a..b, (u' x - V1 x * u x / 2) ^ 2 =
      ∫ x in a..b, ((u' x + V1 x * u x / 2) ^ 2 - 2 * (V1 x * u x * u' x)) := by
    congr 1; ext x; ring
  have hA : IntervalIntegrable (fun x => (u' x + V1 x * u x / 2) ^ 2) volume a b :=
    hI ((hu'.add ((hcV.mul hcu).div_const 2)).pow 2)
  have hB : IntervalIntegrable (fun x => 2 * (V1 x * u x * u' x)) volume a b :=
    hI (continuousOn_const.mul ((hcV.mul hcu).mul hu'))
  have hC : IntervalIntegrable (fun x => V2 x * u x ^ 2) volume a b := hI (hV2.mul (hcu.pow 2))
  have hD : IntervalIntegrable (fun x => V1 x * (2 * u x * u' x)) volume a b :=
    hI (hcV.mul ((continuousOn_const.mul hcu).mul hu'))
  rw [h1, integral_sub hA hB]
  rw [integral_add hC hD] at hFTC
  have hB' : ∫ x in a..b, 2 * (V1 x * u x * u' x) = ∫ x in a..b, V1 x * (2 * u x * u' x) := by
    congr 1; ext x; ring
  rw [hB']
  linarith

/-- **P6.** On an end with `V1 a ≤ 0` (the sign forced by `V'' ≥ ρ` when `V' → -∞`). -/
theorem oneD_boundary_bound (hab : a ≤ b)
    (hu : ∀ x ∈ Icc a b, HasDerivAt u (u' x) x) (hV : ∀ x ∈ Icc a b, HasDerivAt V1 (V2 x) x)
    (hu' : ContinuousOn u' (Icc a b)) (hV2 : ContinuousOn V2 (Icc a b)) (ha : V1 a ≤ 0) :
    ∫ x in a..b, (u' x - V1 x * u x / 2) ^ 2 ≤
      (∫ x in a..b, (u' x + V1 x * u x / 2) ^ 2) + (∫ x in a..b, V2 x * u x ^ 2) - V1 b * u b ^ 2 := by
  rw [oneD_boundary_identity hab hu hV hu' hV2]
  nlinarith [sq_nonneg (u a), mul_nonneg (neg_nonneg.2 ha) (sq_nonneg (u a))]

end MarkovTriple.Stochastic.R29P
