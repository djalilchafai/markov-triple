import Mathlib
import MarkovTriple.BGL.Instances.Circle.Triple

/-!
# The Poincaré inequality on the circle `𝕋 = ℝ/ℤ`: `Var f ≤ (1/(4π²)) ∫ (f')²` (Wirtinger, via Parseval)

Source: the book's torus case (BGL p. 272-273: "by Proposition 4.5.5, p. 199, the Poincaré inequality `P(1)` holds in this
case"; the book's torus has period `2π`, here the period is `1`, so the constant is `1/(2π)²`).  Proof: Parseval
(`AddCircle.hasSum_sq_fourierCoeff`) for `f` and `f'`, and `ĉ_n(f') = 2πi n ĉ_n(f)` (Mathlib's
`fourierCoeffOn_of_hasDerivAt` on `[0,1]`, `f` being periodic), `n² ≥ 1` for `n ≠ 0`.  The sharpness `λ₁ = (2π)²` is
`circle_not_PI_lt` (eigenfunction `cos 2π·`, in `Instances/Circle/LSOne.lean`).
-/

namespace MarkovTriple.BGL.Circle
open MeasureTheory AddCircle Filter Topology
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.Circle
local notation "𝒜c" => MarkovTriple.Sanity.Circle.A₀

/-- the complexified function. -/
noncomputable def cx (g : 𝕋 → ℝ) : 𝕋 → ℂ := fun x => (g x : ℂ)

lemma cx_memLp {g : 𝕋 → ℝ} (hg : Continuous g) : MemLp (cx g) 2 haarAddCircle :=
  ((Complex.continuous_ofReal.comp hg : Continuous (cx g))).memLp_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Parseval for a continuous real function on the circle. -/
lemma hasSum_sq_cx {g : 𝕋 → ℝ} (hg : Continuous g) :
    HasSum (fun n : ℤ => ‖fourierCoeff (cx g) n‖ ^ 2) (∫ x, g x ^ 2 ∂μ₀) := by
  have h := cx_memLp hg
  have := hasSum_sq_fourierCoeff h.toLp
  have e1 : ∀ n : ℤ, fourierCoeff (h.toLp : 𝕋 → ℂ) n = fourierCoeff (cx g) n :=
    fun n => congrFun (fourierCoeff_congr_ae h.coeFn_toLp) n
  simp only [e1] at this
  convert this using 1
  refine integral_congr_ae ?_
  filter_upwards [h.coeFn_toLp] with x hx
  rw [hx]
  simp [cx, sq]

/-- the zeroth coefficient is the mean. -/
lemma fourierCoeff_zero_cx (g : 𝕋 → ℝ) :
    fourierCoeff (cx g) 0 = ((∫ x, g x ∂μ₀ : ℝ) : ℂ) := by
  unfold fourierCoeff
  simp only [neg_zero, fourier_zero, one_smul, cx]
  exact integral_ofReal

/-- the coefficients of `g` on the circle are the coefficients on `[0,1]` of `t ↦ g(t)`. -/
lemma fourierCoeff_cx_eq (g : 𝕋 → ℝ) (n : ℤ) :
    fourierCoeff (cx g) n = fourierCoeffOn (show (0 : ℝ) < 0 + 1 by norm_num)
      (fun t : ℝ => (g (t : 𝕋) : ℂ)) n := by
  rw [← fourierCoeff_liftIoc_eq (T := 1)]
  congr 1
  funext x
  simp [AddCircle.liftIoc, cx, AddCircle.coe_equivIoc]

/-- `ĉ_n(f') = 2πi n ĉ_n(f)` for `f ∈ 𝒜₀` (`f' = D f`): integration by parts on `[0,1]`, `f` periodic. -/
lemma fourierCoeff_cx_D {f : 𝕋 → ℝ} (hf : f ∈ 𝒜c) (n : ℤ) :
    fourierCoeff (cx (D f)) n = (2 * π * Complex.I * n) * fourierCoeff (cx f) n := by
  by_cases hn : n = 0
  · subst hn
    rw [fourierCoeff_zero_cx, integral_D hf]
    simp
  · have hab : (0 : ℝ) < 0 + 1 := by norm_num
    rw [fourierCoeff_cx_eq, fourierCoeff_cx_eq]
    have hder : ∀ x ∈ Set.uIcc (0 : ℝ) (0 + 1),
        HasDerivAt (fun t : ℝ => (f (t : 𝕋) : ℂ)) ((D f (x : 𝕋) : ℝ) : ℂ) x := by
      intro x _
      have h := (Sm_of_contDiff hf).hasDerivAt 0 x
      simp only [zero_add] at h
      exact h.ofReal_comp
    have hint : IntervalIntegrable (fun t : ℝ => ((D f (t : 𝕋) : ℝ) : ℂ)) MeasureTheory.volume 0 (0 + 1) :=
      (Complex.continuous_ofReal.comp (mem_A₀.1 (D_mem_A₀ hf)).continuous).intervalIntegrable _ _
    have key := fourierCoeffOn_of_hasDerivAt hab hn hder hint
    have hper : (((0 : ℝ) + 1 : ℝ) : 𝕋) = ((0 : ℝ) : 𝕋) := by
      simp
    rw [hper, sub_self, mul_zero, zero_sub] at key
    have h2 : (-(2 * π * Complex.I * n) : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have h3 : (-2 * (π : ℂ) * Complex.I * n : ℂ) ≠ 0 := by
      have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    set A := fourierCoeffOn hab (fun t : ℝ => (f (t : 𝕋) : ℂ)) n
    set B := fourierCoeffOn hab (fun t : ℝ => ((D f (t : 𝕋) : ℝ) : ℂ)) n
    have e : ((((0 : ℝ) + 1 : ℝ) : ℂ) - ((0 : ℝ) : ℂ)) = 1 := by simp
    rw [e] at key
    field_simp at key
    linear_combination (-1 : ℂ) * key

/-- **Wirtinger**: `Var f ≤ (1/(4π²)) ∫ (f')²` for `f ∈ 𝒜₀ = C^∞(𝕋)`, `𝕋 = ℝ/ℤ`. -/
lemma circle_var_le {f : 𝕋 → ℝ} (hf : f ∈ 𝒜c) :
    ProbabilityTheory.variance f μ₀ ≤ 1 / (4 * π ^ 2) * ∫ x, D f x * D f x ∂μ₀ := by
  have hc := continuous_of_A₀ hf
  have hcD := continuous_of_A₀ (D_mem_A₀ hf)
  have S1 := hasSum_sq_cx hc
  have S2 := hasSum_sq_cx hcD
  have S3 : HasSum (fun n : ℤ => if n = 0 then ‖fourierCoeff (cx f) 0‖ ^ 2 else 0)
      (‖fourierCoeff (cx f) 0‖ ^ 2) := hasSum_ite_eq 0 _
  have S4 := S1.sub S3
  have S5 := S2.mul_left (1 / (4 * π ^ 2))
  have hle : ∀ n : ℤ, ‖fourierCoeff (cx f) n‖ ^ 2 - (if n = 0 then ‖fourierCoeff (cx f) 0‖ ^ 2 else 0) ≤
      1 / (4 * π ^ 2) * ‖fourierCoeff (cx (D f)) n‖ ^ 2 := by
    intro n
    by_cases hn : n = 0
    · subst hn
      simp only [ite_true, sub_self]
      positivity
    · simp only [hn, ↓reduceIte, sub_zero]
      rw [fourierCoeff_cx_D hf n]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by
        have h : (1 : ℤ) ≤ n ^ 2 := by nlinarith [sq_pos_of_ne_zero hn]
        exact_mod_cast h
      have hnorm : ‖(2 * (π : ℂ) * Complex.I * n) * fourierCoeff (cx f) n‖ ^ 2 =
          4 * π ^ 2 * (n : ℝ) ^ 2 * ‖fourierCoeff (cx f) n‖ ^ 2 := by
        rw [norm_mul, mul_pow]
        have : ‖(2 * (π : ℂ) * Complex.I * n)‖ ^ 2 = 4 * π ^ 2 * (n : ℝ) ^ 2 := by
          rw [norm_mul, norm_mul, norm_mul, mul_pow, mul_pow, mul_pow]
          simp [Complex.norm_real, abs_of_pos Real.pi_pos]
          ring_nf
          simp
        rw [this]
      rw [hnorm]
      have hpi : 0 < π ^ 2 := by positivity
      have : 1 / (4 * π ^ 2) * (4 * π ^ 2 * (n : ℝ) ^ 2 * ‖fourierCoeff (cx f) n‖ ^ 2) =
          (n : ℝ) ^ 2 * ‖fourierCoeff (cx f) n‖ ^ 2 := by field_simp
      rw [this]
      nlinarith [sq_nonneg ‖fourierCoeff (cx f) n‖]
  have hmain := hasSum_le hle S4 S5
  have hm0 : ‖fourierCoeff (cx f) 0‖ ^ 2 = (∫ x, f x ∂μ₀) ^ 2 := by
    rw [fourierCoeff_zero_cx, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hvar : ProbabilityTheory.variance f μ₀ = (∫ x, f x ^ 2 ∂μ₀) - (∫ x, f x ∂μ₀) ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub (memLp_of_mem hf 2)]
    simp [Pi.pow_apply]
  rw [hvar, ← hm0]
  have e : ∫ x, D f x * D f x ∂μ₀ = ∫ x, D f x ^ 2 ∂μ₀ := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
  rw [e]
  exact hmain

end MarkovTriple.BGL.Circle
