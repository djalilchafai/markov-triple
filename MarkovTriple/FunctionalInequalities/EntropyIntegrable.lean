import Mathlib
import MarkovTriple.Frozen.Ent
import MarkovTriple.Frozen.MarkovTriple
import MarkovTriple.Frozen.FullMarkovTriple
import MarkovTriple.Hilbert.TripleForm

/-!
# Integrability for entropy: no Bochner junk

`Ent μ f = ∫ f log f − (∫ f) log (∫ f)` (Frozen/Ent.lean) has the junk value `0` for the integrals
when `f log f` is not integrable.  Here we prove the integrability needed to avoid this, for
finite `μ`:

* `abs_mul_log_le`            : `|x log x| ≤ 1 + x²`;
* `integrable_mul_log_of_memLp_two` : `h ∈ L²(μ)` ⇒ `h log h ∈ L¹(μ)`;
* `integrable_sq_mul_log_sq`  : `f ∈ L³(μ)` ⇒ `f² log f² ∈ L¹(μ)` (`x² |log x²| ≤ 1 + 2|x|³`);
* the consequences for `f ∈ 𝒜₀` (`memLp 3`) and for `g ∈ 𝒜` with `g ∈ L^∞` (finite `μ`);
* `Ent_sq_eq` : for such `f`, `Ent μ (f²)` is the honest difference of integrals.
-/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple

/-- `|x log x| ≤ 1 + x²`. -/
lemma abs_mul_log_le (x : ℝ) : |x * Real.log x| ≤ 1 + x ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hax : 0 < |x| := abs_pos.2 hx
  have hl : Real.log x = Real.log |x| := (Real.log_abs x).symm
  rw [abs_mul, hl]
  by_cases h1 : 1 ≤ |x|
  · have h0 : 0 ≤ Real.log |x| := Real.log_nonneg h1
    rw [abs_of_nonneg h0]
    have := Real.log_le_sub_one_of_pos hax
    have hsq : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
    nlinarith [sq_nonneg |x|]
  · push Not at h1
    have h0 : Real.log |x| ≤ 0 := Real.log_nonpos hax.le h1.le
    rw [abs_of_nonpos h0]
    have h2 : Real.log (|x|⁻¹) ≤ |x|⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hax)
    rw [Real.log_inv] at h2
    have h3 : |x| * -Real.log |x| ≤ |x| * (|x|⁻¹ - 1) := mul_le_mul_of_nonneg_left h2 hax.le
    have h4 : |x| * (|x|⁻¹ - 1) = 1 - |x| := by field_simp
    nlinarith [sq_nonneg x, abs_nonneg x]

/-- `x² |log x²| ≤ 1 + 2 |x|³`. -/
lemma sq_mul_log_sq_le (x : ℝ) : |x ^ 2 * Real.log (x ^ 2)| ≤ 1 + 2 * |x| ^ 3 := by
  set y : ℝ := x ^ 2 with hy
  have hy0 : 0 ≤ y := sq_nonneg x
  rcases hy0.eq_or_lt with h0 | hpos
  · rw [← h0]; simp; positivity
  have hs : Real.sqrt y = |x| := by rw [hy, Real.sqrt_sq_eq_abs]
  have hsp : 0 < Real.sqrt y := Real.sqrt_pos.2 hpos
  have hss : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt hy0
  by_cases h1 : 1 ≤ y
  · have h0' : 0 ≤ Real.log y := Real.log_nonneg h1
    rw [abs_of_nonneg (mul_nonneg hy0 h0')]
    have hl : Real.log y = 2 * Real.log (Real.sqrt y) := by
      rw [Real.log_sqrt hy0]; ring
    have := Real.log_le_sub_one_of_pos hsp
    have e : y * Real.log y ≤ 2 * (y * Real.sqrt y) := by
      rw [hl]; nlinarith [mul_nonneg hy0 hsp.le]
    have e2 : y * Real.sqrt y = |x| ^ 3 := by rw [hs, hy]; have := sq_abs x; nlinarith [abs_nonneg x]
    linarith [e2]
  · push Not at h1
    have h0' : Real.log y ≤ 0 := Real.log_nonpos hy0 h1.le
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hy0 h0')]
    have h2 : Real.log (y⁻¹) ≤ y⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at h2
    have h3 : y * -Real.log y ≤ y * (y⁻¹ - 1) := mul_le_mul_of_nonneg_left h2 hy0
    have h4 : y * (y⁻¹ - 1) = 1 - y := by field_simp
    nlinarith [pow_nonneg (abs_nonneg x) 3]

variable {E : Type*} [MeasurableSpace E]

/-- `h ∈ L²(μ)` (finite `μ`) ⇒ `h log h ∈ L¹(μ)`. -/
theorem integrable_mul_log_of_memLp_two {μ : Measure E} [IsFiniteMeasure μ] {h : E → ℝ}
    (hh : MemLp h 2 μ) : Integrable (fun x => h x * Real.log (h x)) μ := by
  have hm : AEStronglyMeasurable (fun x => h x * Real.log (h x)) μ :=
    (Real.continuous_mul_log.comp_aestronglyMeasurable hh.aestronglyMeasurable)
  have hb : Integrable (fun x => 1 + h x ^ 2) μ :=
    (integrable_const (1 : ℝ)).add (hh.integrable_sq)
  refine hb.mono' hm (Filter.Eventually.of_forall fun x => ?_)
  simpa using abs_mul_log_le (h x)

/-- `f ∈ L³(μ)` (finite `μ`) ⇒ `f² log f² ∈ L¹(μ)`. -/
theorem integrable_sq_mul_log_sq {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ}
    (hf : MemLp f 3 μ) : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ := by
  have hm : AEStronglyMeasurable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ :=
    (Real.continuous_mul_log.comp_aestronglyMeasurable
      ((continuous_pow 2).comp_aestronglyMeasurable hf.aestronglyMeasurable))
  have h3 : Integrable (fun x => ‖f x‖ ^ 3) μ := by
    have := hf.integrable_norm_pow (p := 3) (by norm_num)
    simpa using this
  have hb : Integrable (fun x => 1 + 2 * ‖f x‖ ^ 3) μ :=
    (integrable_const (1 : ℝ)).add (h3.const_mul 2)
  refine hb.mono' hm (Filter.Eventually.of_forall fun x => ?_)
  simpa using sq_mul_log_sq_le (f x)

/-- Honest entropy of a square: both integrals are genuine Bochner integrals of integrable
functions (`f ∈ L³`, finite `μ`). -/
theorem Ent_sq_integrable {μ : Measure E} [IsFiniteMeasure μ] {f : E → ℝ} (hf : MemLp f 3 μ) :
    Integrable (fun x => (f ^ 2) x * Real.log ((f ^ 2) x)) μ ∧ Integrable (f ^ 2) μ :=
  ⟨integrable_sq_mul_log_sq hf, (hf.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ 3)).integrable_sq⟩

/-- Unfolded form of `Ent μ (f²)`. -/
theorem Ent_sq_eq {μ : Measure E} (f : E → ℝ) :
    Ent μ (f ^ 2) = (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) -
      (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) := rfl

/-- `f ∈ 𝒜₀` : `f² log f²` and `f²` are integrable (`memLp 3`), finite `μ`. -/
theorem integrable_sq_log_sq_of_A₀ (T : MarkovTriple E) [IsFiniteMeasure T.μ] {f : E → ℝ}
    (hf : f ∈ T.A₀) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) T.μ ∧ Integrable (fun x => f x ^ 2) T.μ :=
  Ent_sq_integrable (T.memLp f hf 3 (by norm_num) (by simp))

/-- `g ∈ 𝒜` essentially bounded (finite `μ`) : same conclusion. -/
theorem integrable_sq_log_sq_of_A_bdd (F : FullMarkovTriple E) [IsFiniteMeasure F.μ] {g : E → ℝ}
    (_hg : g ∈ F.A) (hb : MemLp g ∞ F.μ) :
    Integrable (fun x => g x ^ 2 * Real.log (g x ^ 2)) F.μ ∧ Integrable (fun x => g x ^ 2) F.μ :=
  Ent_sq_integrable (hb.mono_exponent (by norm_num : (3 : ℝ≥0∞) ≤ ∞))

/-- `Ent` of a constant is zero for a probability measure. -/
theorem Ent_const (μ : Measure E) [IsProbabilityMeasure μ] (c : ℝ) : Ent μ (fun _ => c) = 0 := by
  simp [Ent]

end MarkovTriple
