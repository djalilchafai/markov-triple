import Mathlib

/-! # Bakry–Émery (Phase 4b): boundedness helpers (finite measures) -/

open MeasureTheory
open scoped ENNReal

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

/-- `MemLp f ∞` gives an a.e. bound. -/
lemma bd_of_memLp_top {f : E → ℝ} (h : MemLp f ∞ μ) : ∃ C : ℝ, ∀ᵐ x ∂μ, |f x| ≤ C := by
  have hfin : eLpNormEssSup f μ < ∞ := by
    rw [← eLpNorm_exponent_top h.aestronglyMeasurable]; exact h.eLpNorm_lt_top
  refine ⟨(eLpNormEssSup f μ).toReal, ?_⟩
  filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
  have := ENNReal.toReal_mono hfin.ne hx
  simpa using this

/-- an a.e. bound and measurability give `MemLp f ∞`. -/
lemma memLp_top_of_bd {f : E → ℝ} (hm : AEStronglyMeasurable f μ) {C : ℝ}
    (h : ∀ᵐ x ∂μ, |f x| ≤ C) : MemLp f ∞ μ :=
  memLp_top_of_bound hm C (h.mono fun x hx => by simpa using hx)

/-- bounded functions are in every `Lᵖ` of a finite measure. -/
lemma memLp_of_memLp_top [IsFiniteMeasure μ] {f : E → ℝ} (h : MemLp f ∞ μ) (p : ℝ≥0∞) :
    MemLp f p μ := by
  obtain ⟨C, hC⟩ := bd_of_memLp_top h
  exact MemLp.of_bound h.aestronglyMeasurable C (hC.mono fun x hx => by simpa using hx)

lemma memLp_top_mul {f g : E → ℝ} (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    MemLp (fun x => f x * g x) ∞ μ := by
  obtain ⟨C, hC⟩ := bd_of_memLp_top hf
  obtain ⟨D, hD⟩ := bd_of_memLp_top hg
  refine memLp_top_of_bd (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) (C := C * D) ?_
  filter_upwards [hC, hD] with x h1 h2
  rw [abs_mul]
  exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)

lemma memLp_top_add {f g : E → ℝ} (hf : MemLp f ∞ μ) (hg : MemLp g ∞ μ) :
    MemLp (fun x => f x + g x) ∞ μ := hf.add hg

lemma memLp_top_const_mul {f : E → ℝ} (c : ℝ) (hf : MemLp f ∞ μ) :
    MemLp (fun x => c * f x) ∞ μ := hf.const_mul c

/-- a bounded function times a function in `L²` is in `L²`. -/
lemma memLp_two_mul_top {f g : E → ℝ} (hf : MemLp f ∞ μ) (hg : MemLp g 2 μ) :
    MemLp (fun x => f x * g x) 2 μ := by
  obtain ⟨C, hC⟩ := bd_of_memLp_top hf
  refine (hg.const_mul C).of_le (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable) ?_
  filter_upwards [hC] with x hx
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right (hx.trans (le_abs_self C)) (abs_nonneg _)

/-- bounded times `L²` is integrable against `L²`... product of two `L²` functions is integrable. -/
lemma integrable_mul_of_two {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * g x) μ :=
  hf.integrable_mul hg

lemma integrable_top_mul_two {f g : E → ℝ} (hf : MemLp f ∞ μ) (hg : MemLp g 2 μ)
    [IsFiniteMeasure μ] : Integrable (fun x => f x * g x) μ :=
  (memLp_of_memLp_top hf 2).integrable_mul hg

end MarkovTriple.BE
