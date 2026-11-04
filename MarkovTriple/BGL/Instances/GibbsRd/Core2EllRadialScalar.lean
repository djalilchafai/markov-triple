import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllRadialCut

/-!
# Scale-invariant scalar estimates for the radial cut-off quantities (R19, Stream A6, target T6)

With `φ_k = r^k σ_k` (`r = 1/R`), `α, α', α'', β, β', β''` at a point, and the normalised quantities
`x₁ = r α`, `x₂ = r² β`, `x₃ = α'`, `x₄ = r β'`, `x₅ = R α''`, `x₆ = β''` (all `≤ B`), every quantity
`Γχ, Lχ, LLχ, Γ(Lχ), Γ₂(χ)` of the radial cut-off is a polynomial in the `σ_k, x_i` (no `R`): `radial_bounds`.
-/

namespace MarkovTriple.BGL.Instances.GibbsRd

lemma abs_mul_le'' {a b α β : ℝ} (ha : |a| ≤ α) (hb : |b| ≤ β) : |a * b| ≤ α * β := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

/-- the normalised polynomial bounds. -/
lemma norm_bounds {B σ1 σ2 σ3 σ4 x1 x2 x3 x4 x5 x6 : ℝ} (hB : 1 ≤ B)
    (s1 : |σ1| ≤ B) (s2 : |σ2| ≤ B) (s3 : |σ3| ≤ B) (s4 : |σ4| ≤ B)
    (h1 : |x1| ≤ B) (h2 : |x2| ≤ B) (h3 : |x3| ≤ B) (h4 : |x4| ≤ B) (h5 : |x5| ≤ B) (h6 : |x6| ≤ B) :
    |σ1 ^ 2 * x2| ≤ 16 * B ^ 5 ∧ |σ1 * x1 + σ2 * x2| ≤ 16 * B ^ 5 ∧
    |x1 * (σ2 * x1 + σ1 * x3 + σ3 * x2 + σ2 * x4) +
      x2 * (σ3 * x1 + 2 * σ2 * x3 + σ1 * x5 + σ4 * x2 + 2 * σ3 * x4 + σ2 * x6)| ≤ 16 * B ^ 5 ∧
    |x2 * (σ2 * x1 + σ1 * x3 + σ3 * x2 + σ2 * x4) ^ 2| ≤ 16 * B ^ 5 ∧
    |σ1 ^ 2 * (x1 * x4 / 2 + x2 * x6 / 2 - x2 * x3) + σ1 * σ2 * x2 * x4 + σ2 ^ 2 * x2 ^ 2| ≤
      16 * B ^ 5 := by
  have hB0 : 0 ≤ B := by linarith
  have p2 : ∀ {u v : ℝ}, |u| ≤ B → |v| ≤ B → |u * v| ≤ B * B := fun hu hv => abs_mul_le'' hu hv
  have p3 : ∀ {u v w : ℝ}, |u| ≤ B → |v| ≤ B → |w| ≤ B → |u * v * w| ≤ B * B * B :=
    fun hu hv hw => abs_mul_le'' (abs_mul_le'' hu hv) hw
  have e2 : B * B ≤ B ^ 5 := by nlinarith [pow_le_pow_right₀ hB (show 2 ≤ 5 by norm_num)]
  have B2 : 1 ≤ B * B := by nlinarith
  have B3 : B * B * B ≤ B ^ 5 := by nlinarith [mul_nonneg hB0 hB0]
  have B4 : B * B * B * B ≤ B ^ 5 := by nlinarith [mul_nonneg hB0 hB0]
  have B5 : B ^ 5 = B * B * B * B * B := by ring
  -- T1, T2
  have T1 : |σ2 * x1 + σ1 * x3 + σ3 * x2 + σ2 * x4| ≤ 4 * (B * B) := by
    have := abs_add_le (σ2 * x1 + σ1 * x3 + σ3 * x2) (σ2 * x4)
    have := abs_add_le (σ2 * x1 + σ1 * x3) (σ3 * x2)
    have := abs_add_le (σ2 * x1) (σ1 * x3)
    have := p2 s2 h1; have := p2 s1 h3; have := p2 s3 h2; have := p2 s2 h4
    linarith
  have T2 : |σ3 * x1 + 2 * σ2 * x3 + σ1 * x5 + σ4 * x2 + 2 * σ3 * x4 + σ2 * x6| ≤ 8 * (B * B) := by
    have a1 := abs_add_le (σ3 * x1 + 2 * σ2 * x3 + σ1 * x5 + σ4 * x2 + 2 * σ3 * x4) (σ2 * x6)
    have a2 := abs_add_le (σ3 * x1 + 2 * σ2 * x3 + σ1 * x5 + σ4 * x2) (2 * σ3 * x4)
    have a3 := abs_add_le (σ3 * x1 + 2 * σ2 * x3 + σ1 * x5) (σ4 * x2)
    have a4 := abs_add_le (σ3 * x1 + 2 * σ2 * x3) (σ1 * x5)
    have a5 := abs_add_le (σ3 * x1) (2 * σ2 * x3)
    have b1 := p2 s3 h1; have b2 := p2 s1 h5; have b3 := p2 s4 h2; have b4 := p2 s2 h6
    have c1 : |2 * σ2 * x3| ≤ 2 * (B * B) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := p2 s2 h3; linarith
    have c2 : |2 * σ3 * x4| ≤ 2 * (B * B) := by
      rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have := p2 s3 h4; linarith
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := p3 (u := σ1) (v := σ1) (w := x2) s1 s1 h2
    have e : σ1 ^ 2 * x2 = σ1 * σ1 * x2 := by ring
    rw [e]; linarith
  · have a := abs_add_le (σ1 * x1) (σ2 * x2)
    have := p2 s1 h1; have := p2 s2 h2; linarith
  · have a := abs_add_le (x1 * (σ2 * x1 + σ1 * x3 + σ3 * x2 + σ2 * x4))
      (x2 * (σ3 * x1 + 2 * σ2 * x3 + σ1 * x5 + σ4 * x2 + 2 * σ3 * x4 + σ2 * x6))
    have m1 := abs_mul_le'' h1 T1
    have m2 := abs_mul_le'' h2 T2
    nlinarith [mul_nonneg hB0 hB0]
  · have m := abs_mul_le'' h2 (abs_mul_le'' T1 T1)
    have e : x2 * (σ2 * x1 + σ1 * x3 + σ3 * x2 + σ2 * x4) ^ 2 =
        x2 * ((σ2 * x1 + σ1 * x3 + σ3 * x2 + σ2 * x4) * (σ2 * x1 + σ1 * x3 + σ3 * x2 + σ2 * x4)) := by ring
    rw [e]
    nlinarith [mul_nonneg hB0 hB0, mul_nonneg (mul_nonneg hB0 hB0) hB0]
  · have a1 := abs_add_le (σ1 ^ 2 * (x1 * x4 / 2 + x2 * x6 / 2 - x2 * x3) + σ1 * σ2 * x2 * x4) (σ2 ^ 2 * x2 ^ 2)
    have a2 := abs_add_le (σ1 ^ 2 * (x1 * x4 / 2 + x2 * x6 / 2 - x2 * x3)) (σ1 * σ2 * x2 * x4)
    have q : |x1 * x4 / 2 + x2 * x6 / 2 - x2 * x3| ≤ 2 * (B * B) := by
      have a := abs_sub (x1 * x4 / 2 + x2 * x6 / 2) (x2 * x3)
      have b := abs_add_le (x1 * x4 / 2) (x2 * x6 / 2)
      have c1 : |x1 * x4 / 2| ≤ B * B / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := p2 h1 h4; linarith
      have c2 : |x2 * x6 / 2| ≤ B * B / 2 := by
        rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := p2 h2 h6; linarith
      have c3 := p2 h2 h3
      linarith
    have m1 : |σ1 ^ 2 * (x1 * x4 / 2 + x2 * x6 / 2 - x2 * x3)| ≤ B * B * (2 * (B * B)) := by
      have := abs_mul_le'' (abs_mul_le'' s1 s1) q
      have e : σ1 ^ 2 = σ1 * σ1 := by ring
      rw [e]; exact this
    have m2 : |σ1 * σ2 * x2 * x4| ≤ B * B * B * B := by
      have := abs_mul_le'' (p3 s1 s2 h2) h4
      exact this
    have m3 : |σ2 ^ 2 * x2 ^ 2| ≤ B * B * (B * B) := by
      have := abs_mul_le'' (abs_mul_le'' s2 s2) (abs_mul_le'' h2 h2)
      have e : σ2 ^ 2 * x2 ^ 2 = σ2 * σ2 * (x2 * x2) := by ring
      rw [e]; exact this
    nlinarith [mul_nonneg hB0 hB0, mul_nonneg (mul_nonneg hB0 hB0) hB0,
      mul_nonneg (mul_nonneg hB0 hB0) (mul_nonneg hB0 hB0)]

end MarkovTriple.BGL.Instances.GibbsRd
