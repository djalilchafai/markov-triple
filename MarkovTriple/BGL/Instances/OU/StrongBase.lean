import Mathlib
import MarkovTriple.BGL.Instances.OU.LSIMain
import MarkovTriple.BGL.Theory.Strong.Main

/-!
# OU strong gradient bound (Part 1): Gaussian integration by parts for the interpolation
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

/-- Symmetry of `L = ∂² − x∂` on `γ` for bounded smooth functions:
`∫ (a₂ − x a₁) G = ∫ a₀ (G₂ − x G₁)` where `a₀' = a₁`, `a₁' = a₂`, `G' = G₁`, `G₁' = G₂`. -/
theorem ibp_L {a0 a1 a2 G G1 G2 : ℝ → ℝ}
    (ha0 : ∀ x, HasDerivAt a0 (a1 x) x) (ha1 : ∀ x, HasDerivAt a1 (a2 x) x)
    (hG : ∀ x, HasDerivAt G (G1 x) x) (hG1 : ∀ x, HasDerivAt G1 (G2 x) x)
    (b0 : ∃ C, ∀ x, |a0 x| ≤ C) (b1 : ∃ C, ∀ x, |a1 x| ≤ C) (b2 : ∃ C, ∀ x, |a2 x| ≤ C)
    (bG : ∃ C, ∀ x, |G x| ≤ C) (bG1 : ∃ C, ∀ x, |G1 x| ≤ C) (bG2 : ∃ C, ∀ x, |G2 x| ≤ C) :
    Integrable (fun x => (a2 x - x * a1 x) * G x) γ ∧
    Integrable (fun x => a0 x * (G2 x - x * G1 x)) γ ∧
    ∫ x, (a2 x - x * a1 x) * G x ∂γ = ∫ x, a0 x * (G2 x - x * G1 x) ∂γ := by
  have mul_bd : ∀ {u v : ℝ → ℝ}, (∃ C, ∀ x, |u x| ≤ C) → (∃ C, ∀ x, |v x| ≤ C) →
      ∃ C, ∀ x, |u x * v x| ≤ C := by
    rintro u v ⟨C, hC⟩ ⟨D, hD⟩
    refine ⟨C * D, fun x => ?_⟩
    rw [abs_mul]
    exact mul_le_mul (hC x) (hD x) (abs_nonneg _) ((abs_nonneg _).trans (hC x))
  have add_bd : ∀ {u v : ℝ → ℝ}, (∃ C, ∀ x, |u x| ≤ C) → (∃ C, ∀ x, |v x| ≤ C) →
      ∃ C, ∀ x, |u x + v x| ≤ C := by
    rintro u v ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun x => (abs_add_le _ _).trans (add_le_add (hC x) (hD x))⟩
  have cont : ∀ {F F' : ℝ → ℝ}, (∀ x, HasDerivAt F (F' x) x) → Continuous F := fun h =>
    continuous_iff_continuousAt.2 fun x => (h x).continuousAt
  -- J1 = a1 G, J2 = a0 G1
  have hd1 : ∀ x, HasDerivAt (fun x => a1 x * G x) (a2 x * G x + a1 x * G1 x) x :=
    fun x => (ha1 x).mul (hG x)
  have hd2 : ∀ x, HasDerivAt (fun x => a0 x * G1 x) (a1 x * G1 x + a0 x * G2 x) x :=
    fun x => (ha0 x).mul (hG1 x)
  obtain ⟨i1, z1⟩ := ibpγ hd1 (mul_bd b1 bG) (add_bd (mul_bd b2 bG) (mul_bd b1 bG1))
  obtain ⟨i2, z2⟩ := ibpγ hd2 (mul_bd b0 bG1) (add_bd (mul_bd b1 bG1) (mul_bd b0 bG2))
  have c1 : Continuous a1 := cont ha1
  have cG1 : Continuous G1 := cont hG1
  have cG : Continuous G := cont hG
  have iA : Integrable (fun x => a1 x * G1 x) γ :=
    integrable_of_bd (c1.mul cG1) (mul_bd b1 bG1)
  have j1 : Integrable (fun x => (a2 x - x * a1 x) * G x) γ := by
    refine (i1.sub iA).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  have j2 : Integrable (fun x => a0 x * (G2 x - x * G1 x)) γ := by
    refine (i2.sub iA).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  refine ⟨j1, j2, ?_⟩
  have e1 : ∫ x, (a2 x - x * a1 x) * G x ∂γ = -∫ x, a1 x * G1 x ∂γ := by
    have : (fun x => (a2 x * G x + a1 x * G1 x) - x * (a1 x * G x)) =
        fun x => (a2 x - x * a1 x) * G x + a1 x * G1 x := by funext x; ring
    rw [this, integral_add j1 iA] at z1
    linarith
  have e2 : ∫ x, a0 x * (G2 x - x * G1 x) ∂γ = -∫ x, a1 x * G1 x ∂γ := by
    have : (fun x => (a1 x * G1 x + a0 x * G2 x) - x * (a0 x * G1 x)) =
        fun x => a1 x * G1 x + a0 x * (G2 x - x * G1 x) := by funext x; ring
    rw [this, integral_add iA j2] at z2
    linarith
  rw [e1, e2]

end MarkovTriple.BGL.Instances.OU
