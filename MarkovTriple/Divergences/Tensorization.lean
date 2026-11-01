import Mathlib
import MarkovTriple.Divergences.Entropy

/-!
# Entropy tensorization

Ported from ginibre-poincare (`Analysis/FiniteEntropyTensorization.lean`,
`EntropyProductDecomposition.lean`, `IntegralEntropyTensorization.lean`).  The source stated the
integral results for `squareEntropy`; here they are stated for the unified `Ent` (nonnegative
functions `h`) and the `squareEntropy` versions are corollaries (`h = f ^ 2`).
-/

open MeasureTheory Filter
open scoped BigOperators

namespace MarkovTriple

noncomputable section

/-- The scalar Gibbs inequality, including a zero numerator. -/
theorem mul_log_sub_mul_log_ge_sub {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) :
    a - b ≤ a * Real.log a - a * Real.log b := by
  by_cases hz : a = 0
  · simp [hz, hb.le]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm hz)
    have h := mul_le_mul_of_nonneg_left
      (Real.log_le_sub_one_of_pos (div_pos hb hap)) ha
    rw [Real.log_div hb.ne' hz] at h
    have he : a * (b / a - 1) = b - a := by field_simp
    rw [he] at h
    nlinarith

/-- A mixed logarithmic marginal moment is integrable whenever the marginal's
own logarithmic moment is. Zeros of the marginal cause no integrability gap. -/
theorem integrable_mul_log_fiberMoment
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hi : Integrable h (μ.prod ν))
    (hn : ∀ p, 0 ≤ h p)
    (hl : Integrable (fun x => (∫ y, h (x, y) ∂ν) *
      Real.log (∫ y, h (x, y) ∂ν)) μ) :
    Integrable (fun p => h p * Real.log (∫ y, h (p.1, y) ∂ν)) (μ.prod ν) := by
  have hA := hm.stronglyMeasurable.integral_prod_right' (ν := ν)
  apply (integrable_prod_iff (f := fun p => h p * Real.log (∫ y, h (p.1, y) ∂ν))
    (hm.mul (hA.measurable.log.comp measurable_fst)).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hi.prod_right_ae] with x hx
    exact hx.mul_const _
  · have he (x : α) : (∫ y, ‖h (x, y) * Real.log (∫ y, h (x, y) ∂ν)‖ ∂ν) =
        ‖(∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν)‖ := by
      simp_rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hn (x, _))]
      rw [integral_mul_const, abs_of_nonneg (integral_nonneg (fun y => hn (x, y)))]
    simpa only [he] using hl.norm

/-- Nonnegative densities vanish almost everywhere on zero-mass fibers. -/
theorem ae_zero_or_pos_fiberMoment
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hi : Integrable h (μ.prod ν))
    (hn : ∀ p, 0 ≤ h p) :
    ∀ᵐ p ∂μ.prod ν, h p = 0 ∨ 0 < ∫ y, h (p.1, y) ∂ν := by
  have hA := hm.stronglyMeasurable.integral_prod_right' (ν := ν)
  apply (Measure.ae_prod_iff_ae_ae (by
    exact (measurableSet_eq_fun hm measurable_const).union
      (measurableSet_lt measurable_const (hA.measurable.comp measurable_fst)))).mpr
  filter_upwards [hi.prod_right_ae] with x hx
  by_cases hp : 0 < ∫ y, h (x, y) ∂ν
  · exact Eventually.of_forall (fun y => Or.inr hp)
  · have hz : (∫ y, h (x, y) ∂ν) = 0 :=
      le_antisymm (not_lt.mp hp) (integral_nonneg (fun y => hn (x, y)))
    exact ((integral_eq_zero_iff_of_nonneg (fun y => hn (x, y)) hx).mp hz).mono
      (fun y hy => Or.inl hy)

/-- Continuous-measure entropy tensorization in its unnormalized matrix form.
Only the actual logarithmic moments must be integrable; no entropy inequality
or Gaussian LSI is assumed. -/
theorem integral_entropy_matrix_tensorization
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hi : Integrable h (μ.prod ν))
    (hn : ∀ p, 0 ≤ h p)
    (hl : Integrable (fun p => h p * Real.log (h p)) (μ.prod ν))
    (hAlog : Integrable (fun x => (∫ y, h (x, y) ∂ν) *
      Real.log (∫ y, h (x, y) ∂ν)) μ)
    (hBlog : Integrable (fun y => (∫ x, h (x, y) ∂μ) *
      Real.log (∫ x, h (x, y) ∂μ)) ν)
    (hT : 0 < ∫ p, h p ∂μ.prod ν) :
    (∫ x, (∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν) ∂μ) +
      (∫ y, (∫ x, h (x, y) ∂μ) * Real.log (∫ x, h (x, y) ∂μ) ∂ν) ≤
        (∫ p, h p * Real.log (h p) ∂μ.prod ν) +
          (∫ p, h p ∂μ.prod ν) * Real.log (∫ p, h p ∂μ.prod ν) := by
  let A : α → ℝ := fun x => ∫ y, h (x, y) ∂ν
  let B : β → ℝ := fun y => ∫ x, h (x, y) ∂μ
  let T := ∫ p, h p ∂μ.prod ν
  have hAi : Integrable A μ := hi.integral_prod_left
  have hBi : Integrable B ν := hi.integral_prod_right
  have hAm : Measurable A := hm.stronglyMeasurable.integral_prod_right'.measurable
  have hBm : Measurable B := hm.stronglyMeasurable.integral_prod_left'.measurable
  have hAp := ae_zero_or_pos_fiberMoment μ ν h hm hi hn
  have hBp' := ae_zero_or_pos_fiberMoment ν μ (h ∘ Prod.swap)
    (hm.comp measurable_swap) hi.swap (fun p => hn p.swap)
  have hBp : ∀ᵐ p ∂μ.prod ν, h p = 0 ∨ 0 < B p.2 := by
    simpa [B, Function.comp_def] using Measure.measurePreserving_swap.quasiMeasurePreserving.ae hBp'
  have hmA : Integrable (fun p => h p * Real.log (A p.1)) (μ.prod ν) :=
    integrable_mul_log_fiberMoment μ ν h hm hi hn hAlog
  have hmB : Integrable (fun p => h p * Real.log (B p.2)) (μ.prod ν) := by
    have hs := integrable_mul_log_fiberMoment ν μ (h ∘ Prod.swap)
      (hm.comp measurable_swap) hi.swap (fun p => hn p.swap) hBlog
    simpa [B, Function.comp_def] using hs.swap
  have heA : (∫ p, h p * Real.log (A p.1) ∂μ.prod ν) = ∫ x, A x * Real.log (A x) ∂μ := by
    rw [integral_prod _ hmA]
    simp only [integral_mul_const, A]
  have heB : (∫ p, h p * Real.log (B p.2) ∂μ.prod ν) = ∫ y, B y * Real.log (B y) ∂ν := by
    rw [integral_prod_symm _ hmB]
    simp only [integral_mul_const, B]
  have htA : (∫ x, A x ∂μ) = T := (integral_prod _ hi).symm
  have htB : (∫ y, B y ∂ν) = T := (integral_prod_symm _ hi).symm
  have hv : Integrable (fun p => A p.1 * B p.2 / T) (μ.prod ν) :=
    (hAi.mul_prod hBi).div_const T
  have hvint : (∫ p, A p.1 * B p.2 / T ∂μ.prod ν) = T := by
    rw [integral_div, integral_prod_mul, htA, htB]
    field_simp [show T ≠ 0 from hT.ne']
  have hineq : ∀ᵐ p ∂μ.prod ν,
      h p - A p.1 * B p.2 / T ≤
        h p * Real.log (h p) - h p * Real.log (A p.1) -
          h p * Real.log (B p.2) + h p * Real.log T := by
    filter_upwards [hAp, hBp] with p hpA hpB
    by_cases hz : h p = 0
    · have hvn : 0 ≤ A p.1 * B p.2 / T :=
        div_nonneg (mul_nonneg (integral_nonneg (fun y => hn (p.1, y)))
          (integral_nonneg (fun x => hn (x, p.2)))) hT.le
      simp only [hz, zero_mul, zero_sub, sub_self, add_zero]
      linarith
    · have hpa : 0 < A p.1 := hpA.resolve_left hz
      have hpb : 0 < B p.2 := hpB.resolve_left hz
      have hg := mul_log_sub_mul_log_ge_sub (hn p) (div_pos (mul_pos hpa hpb) hT)
      rw [Real.log_div (mul_pos hpa hpb).ne' hT.ne', Real.log_mul hpa.ne' hpb.ne'] at hg
      dsimp only [A, B] at hg ⊢
      nlinarith
  have hg := integral_mono_ae (hi.sub hv)
    (((hl.sub hmA).sub hmB).add (hi.mul_const (Real.log T))) hineq
  simp only [Pi.sub_apply, Pi.add_apply] at hg
  rw [integral_sub hi hv, hvint,
    integral_add (f := fun p => h p * Real.log (h p) - h p * Real.log (A p.1) - h p * Real.log (B p.2)) ((hl.sub hmA).sub hmB) (hi.mul_const (Real.log T)),
    integral_sub (f := fun p => h p * Real.log (h p) - h p * Real.log (A p.1)) (hl.sub hmA) hmB, integral_sub hl hmA,
    heA, heB, integral_mul_const] at hg
  change T - T ≤ _ at hg
  change _ ≤ _ + T * Real.log T
  dsimp only [A, B] at hg
  linarith

/-- Integral entropy tensorization, including zero total mass. -/
theorem integral_entropy_matrix_tensorization_nonneg
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hi : Integrable h (μ.prod ν))
    (hn : ∀ p, 0 ≤ h p)
    (hl : Integrable (fun p => h p * Real.log (h p)) (μ.prod ν))
    (hAlog : Integrable (fun x => (∫ y, h (x, y) ∂ν) *
      Real.log (∫ y, h (x, y) ∂ν)) μ)
    (hBlog : Integrable (fun y => (∫ x, h (x, y) ∂μ) *
      Real.log (∫ x, h (x, y) ∂μ)) ν) :
    (∫ x, (∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν) ∂μ) +
      (∫ y, (∫ x, h (x, y) ∂μ) * Real.log (∫ x, h (x, y) ∂μ) ∂ν) ≤
        (∫ p, h p * Real.log (h p) ∂μ.prod ν) +
          (∫ p, h p ∂μ.prod ν) * Real.log (∫ p, h p ∂μ.prod ν) := by
  by_cases hp : 0 < ∫ p, h p ∂μ.prod ν
  · exact integral_entropy_matrix_tensorization μ ν h hm hi hn hl hAlog hBlog hp
  · have hz : (∫ p, h p ∂μ.prod ν) = 0 :=
      le_antisymm (not_lt.mp hp) (integral_nonneg hn)
    have hzero := (integral_eq_zero_iff_of_nonneg hn hi).mp hz
    have hAzero := (integral_eq_zero_iff_of_nonneg
      (fun x => integral_nonneg (fun y => hn (x, y))) hi.integral_prod_left).mp
      ((integral_prod _ hi).symm.trans hz)
    have hBzero := (integral_eq_zero_iff_of_nonneg
      (fun y => integral_nonneg (fun x => hn (x, y))) hi.integral_prod_right).mp
      ((integral_prod_symm _ hi).symm.trans hz)
    have he : (∫ p, h p * Real.log (h p) ∂μ.prod ν) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hzero] with p hp
      simp [hp]
    have heA : (∫ x, (∫ y, h (x, y) ∂ν) * Real.log (∫ y, h (x, y) ∂ν) ∂μ) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hAzero] with x hx
      simp [hx]
    have heB : (∫ y, (∫ x, h (x, y) ∂μ) * Real.log (∫ x, h (x, y) ∂μ) ∂ν) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hBzero] with y hy
      simp [hy]
    rw [he, heA, heB, hz]
    simp

/-- A bounded nonnegative density has a genuine integrable logarithmic moment
under a finite measure, despite the logarithm's singularity at zero. -/
theorem integrable_mul_log_of_bounded_nonneg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (h : α → ℝ) (hm : Measurable h) (C : ℝ)
    (hb : ∀ x, h x ∈ Set.Icc 0 C) :
    Integrable (fun x => h x * Real.log (h x)) μ := by
  obtain ⟨D, hD⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) C)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  apply memLp_one_iff_integrable.mp
  apply MemLp.of_bound (Real.continuous_mul_log.measurable.comp hm).aestronglyMeasurable D
  exact Eventually.of_forall (fun x => hD (h x) (hb x))


section Generic

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Fiber integral of a function on a product space. -/
noncomputable def fiberMoment (ν : Measure β) (h : α × β → ℝ) (x : α) : ℝ := ∫ y, h (x, y) ∂ν

/-- The chain decomposition of entropy under a product law (`Ent_{μ⊗ν} h = ∫ Ent_ν h(x,·) dμ +
Ent_μ (∫ h(·,y) dν)`). -/
theorem Ent_prod_decomposition
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    (h : α × β → ℝ)
    (hi : Integrable h (μ.prod ν))
    (hlog : Integrable (fun p => h p * Real.log (h p)) (μ.prod ν))
    (hfiber : Integrable (fun x => fiberMoment ν h x * Real.log (fiberMoment ν h x)) μ) :
    Ent (μ.prod ν) h =
      (∫ x, Ent ν (fun y => h (x, y)) ∂μ) + Ent μ (fiberMoment ν h) := by
  have him : Integrable (fun x => ∫ y, h (x, y) * Real.log (h (x, y)) ∂ν) μ :=
    hlog.integral_prod_left
  unfold Ent
  change _ = (∫ x, (∫ y, h (x, y) * Real.log (h (x, y)) ∂ν) -
      fiberMoment ν h x * Real.log (fiberMoment ν h x) ∂μ) + _
  rw [integral_sub him hfiber, integral_prod (fun p => h p * Real.log (h p)) hlog]
  have hm : (∫ x, fiberMoment ν h x ∂μ) = ∫ p, h p ∂μ.prod ν :=
    (integral_prod (fun p => h p) hi).symm
  rw [hm]
  ring

/-- **Entropy tensorization** for nonnegative integrable densities on a product of s-finite
spaces: `Ent_{μ⊗ν} h ≤ ∫ Ent_ν h(x,·) dμ + ∫ Ent_μ h(·,y) dν`.  Only the actual logarithmic
moments must be integrable. -/
theorem Ent_prod_tensorization
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hm : Measurable h) (hn : ∀ p, 0 ≤ h p)
    (hi : Integrable h (μ.prod ν))
    (hlog : Integrable (fun p => h p * Real.log (h p)) (μ.prod ν))
    (hAlog : Integrable (fun x => fiberMoment ν h x * Real.log (fiberMoment ν h x)) μ)
    (hBlog : Integrable (fun y => (∫ x, h (x, y) ∂μ) * Real.log (∫ x, h (x, y) ∂μ)) ν) :
    Ent (μ.prod ν) h ≤
      (∫ x, Ent ν (fun y => h (x, y)) ∂μ) + (∫ y, Ent μ (fun x => h (x, y)) ∂ν) := by
  have ht := integral_entropy_matrix_tensorization_nonneg μ ν h hm hi hn hlog hAlog hBlog
  unfold fiberMoment at hAlog
  unfold Ent
  dsimp only
  rw [integral_sub hlog.integral_prod_left hAlog,
    integral_sub hlog.integral_prod_right hBlog,
    ← integral_prod _ hlog, ← integral_prod_symm _ hlog]
  linarith

/-- Square entropy of a product observable. -/
theorem squareEntropy_prod_tensorization
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α × β → ℝ) (hm : Measurable f)
    (hsq : Integrable (fun p => f p ^ 2) (μ.prod ν))
    (hlog : Integrable (fun p => f p ^ 2 * Real.log (f p ^ 2)) (μ.prod ν))
    (hAlog : Integrable (fun x => (∫ y, f (x, y) ^ 2 ∂ν) *
      Real.log (∫ y, f (x, y) ^ 2 ∂ν)) μ)
    (hBlog : Integrable (fun y => (∫ x, f (x, y) ^ 2 ∂μ) *
      Real.log (∫ x, f (x, y) ^ 2 ∂μ)) ν) :
    squareEntropy (μ.prod ν) f ≤
      (∫ x, squareEntropy ν (fun y => f (x, y)) ∂μ) +
        (∫ y, squareEntropy μ (fun x => f (x, y)) ∂ν) :=
  Ent_prod_tensorization μ ν (fun p => f p ^ 2) (hm.pow_const 2) (fun p => sq_nonneg (f p))
    hsq hlog hAlog hBlog


/-- Bounded nonnegative densities satisfy entropy tensorization under any two probability laws;
all logarithmic integrability conditions are discharged. -/
theorem Ent_prod_tensorization_bounded
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : α × β → ℝ) (hm : Measurable h) (C : ℝ) (hb : ∀ p, h p ∈ Set.Icc 0 C) :
    Ent (μ.prod ν) h ≤
      (∫ x, Ent ν (fun y => h (x, y)) ∂μ) + (∫ y, Ent μ (fun x => h (x, y)) ∂ν) := by
  have hi : Integrable h (μ.prod ν) :=
    memLp_one_iff_integrable.mp (memLp_of_bounded
      (Eventually.of_forall hb) hm.aestronglyMeasurable 1)
  apply Ent_prod_tensorization μ ν h hm (fun p => (hb p).1) hi
    (integrable_mul_log_of_bounded_nonneg _ _ hm C hb)
  · have hAm : Measurable (fiberMoment ν h) :=
      hm.stronglyMeasurable.integral_prod_right'.measurable
    apply integrable_mul_log_of_bounded_nonneg μ _ hAm C
    intro x
    refine ⟨integral_nonneg (fun y => (hb (x, y)).1), ?_⟩
    have hix : Integrable (fun y => h (x, y)) ν :=
      memLp_one_iff_integrable.mp (memLp_of_bounded
        (Eventually.of_forall (fun y => hb (x, y)))
        (hm.comp measurable_prodMk_left).aestronglyMeasurable 1)
    simpa [fiberMoment] using integral_mono hix (integrable_const C)
      (fun y => (hb (x, y)).2)
  · have hBm : Measurable (fun y => ∫ x, h (x, y) ∂μ) :=
      hm.stronglyMeasurable.integral_prod_left'.measurable
    apply integrable_mul_log_of_bounded_nonneg ν _ hBm C
    intro y
    refine ⟨integral_nonneg (fun x => (hb (x, y)).1), ?_⟩
    have hiy : Integrable (fun x => h (x, y)) μ :=
      memLp_one_iff_integrable.mp (memLp_of_bounded
        (Eventually.of_forall (fun x => hb (x, y)))
        (hm.comp measurable_prodMk_right).aestronglyMeasurable 1)
    simpa using integral_mono hiy (integrable_const C) (fun x => (hb (x, y)).2)

/-- Bounded measurable observables satisfy square-entropy tensorization. -/
theorem squareEntropy_prod_tensorization_bounded
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : α × β → ℝ) (hm : Measurable f) (C : ℝ) (hb : ∀ p, |f p| ≤ C) :
    squareEntropy (μ.prod ν) f ≤
      (∫ x, squareEntropy ν (fun y => f (x, y)) ∂μ) +
        (∫ y, squareEntropy μ (fun x => f (x, y)) ∂ν) := by
  apply Ent_prod_tensorization_bounded μ ν (fun p => f p ^ 2) (hm.pow_const 2) (C ^ 2)
  intro p
  refine ⟨sq_nonneg _, ?_⟩
  nlinarith [sq_abs (f p), abs_nonneg (f p), hb p]

end Generic


/-- The continuous extension of `x log x`, including at zero. -/
def entropyPhi (x : ℝ) : ℝ := x * Real.log x

/-- The perspective identity remains valid when its numerator vanishes. -/
theorem entropyPhi_div (u v : ℝ) (hv : v ≠ 0) :
    v * entropyPhi (u / v) = entropyPhi u - u * Real.log v := by
  by_cases hu : u = 0
  · simp [hu, entropyPhi]
  · unfold entropyPhi
    rw [Real.log_div hu hv]
    field_simp

/-- Finite log-sum inequality, with vanishing columns handled without positivity
certificates or regularization assumptions. -/
theorem finite_log_sum {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (hzero : ∀ i, b i = 0 → a i = 0) (hB : 0 < ∑ i, b i) :
    entropyPhi (∑ i, a i) - (∑ i, a i) * Real.log (∑ i, b i) ≤
      ∑ i, (entropyPhi (a i) - a i * Real.log (b i)) := by
  let B := ∑ i, b i
  have hweights : ∑ i, b i / B = 1 := by
    rw [← Finset.sum_div]
    exact div_self hB.ne'
  have havg : ∑ i, (b i / B) * (a i / b i) = (∑ i, a i) / B := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hbi : b i = 0
    · simp [hbi, hzero i hbi]
    · field_simp
  have hj := Real.convexOn_mul_log.map_sum_le
    (t := Finset.univ) (w := fun i => b i / B) (p := fun i => a i / b i)
    (fun i _ => div_nonneg (hb i) hB.le) hweights
    (fun i _ => div_nonneg (ha i) (hb i))
  simp only [smul_eq_mul, havg] at hj
  have hterm (i : ι) : (b i / B) * entropyPhi (a i / b i) =
      (entropyPhi (a i) - a i * Real.log (b i)) / B := by
    by_cases hbi : b i = 0
    · simp [hbi, hzero i hbi, entropyPhi]
    · rw [← entropyPhi_div (a i) (b i) hbi]
      ring
  change entropyPhi ((∑ i, a i) / B) ≤ ∑ i, (b i / B) * entropyPhi (a i / b i) at hj
  simp_rw [hterm] at hj
  rw [← Finset.sum_div] at hj
  have hm := (mul_le_mul_of_nonneg_left hj hB.le)
  rw [entropyPhi_div _ B hB.ne', mul_div_cancel₀ _ hB.ne'] at hm
  exact hm

/-- The matrix form of entropy tensorization, before probability normalization. -/
theorem entropy_matrix_tensorization {α β : Type*} [Fintype α] [Fintype β]
    (h : α → β → ℝ) (hh : ∀ x y, 0 ≤ h x y) :
    (∑ x, entropyPhi (∑ y, h x y)) + (∑ y, entropyPhi (∑ x, h x y)) ≤
      (∑ x, ∑ y, entropyPhi (h x y)) + entropyPhi (∑ x, ∑ y, h x y) := by
  let T := ∑ x, ∑ y, h x y
  have hT : 0 ≤ T := Finset.sum_nonneg (fun x _ => Finset.sum_nonneg (fun y _ => hh x y))
  by_cases ht : T = 0
  · have hz : ∀ x y, h x y = 0 := by
      intro x y
      have hx := (Finset.sum_eq_zero_iff_of_nonneg
        (fun x _ => Finset.sum_nonneg (fun y _ => hh x y))).mp ht x (Finset.mem_univ x)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hh x y)).mp hx y (Finset.mem_univ y)
    simp [hz, entropyPhi]
  · have htpos : 0 < T := lt_of_le_of_ne hT (Ne.symm ht)
    have hrow (x : α) := finite_log_sum (h x) (fun y => ∑ x, h x y) (hh x)
      (fun y => Finset.sum_nonneg (fun x _ => hh x y))
      (fun y hy => (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hh x y)).mp hy x (Finset.mem_univ x))
      (by rw [Finset.sum_comm]; exact htpos)
    have hm := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hrow x)
    simp only [Finset.sum_sub_distrib, ← Finset.sum_mul] at hm
    have hcross : (∑ x, ∑ y, h x y * Real.log (∑ x, h x y)) =
        ∑ y, entropyPhi (∑ x, h x y) := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul, entropyPhi]
    rw [hcross] at hm
    have he : (∑ x, ∑ y, h x y) * Real.log (∑ y, ∑ x, h x y) =
        entropyPhi (∑ x, ∑ y, h x y) := by
      rw [Finset.sum_comm (f := h)]
      rfl
    rw [he] at hm
    linarith

/-- Entropy with respect to the uniform probability law on a finite set. -/
def uniformFiniteEntropy {α : Type*} [Fintype α] (h : α → ℝ) : ℝ :=
  ((∑ x, entropyPhi (h x)) - entropyPhi (∑ x, h x) +
    (∑ x, h x) * Real.log (Fintype.card α)) / Fintype.card α

/-- Entropy tensorizes over two finite uniform probability spaces. -/
theorem uniformFiniteEntropy_tensorization {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (h : α → β → ℝ) (hh : ∀ x y, 0 ≤ h x y) :
    uniformFiniteEntropy (fun p : α × β => h p.1 p.2) ≤
      (∑ y, uniformFiniteEntropy (fun x => h x y)) / Fintype.card β +
      (∑ x, uniformFiniteEntropy (h x)) / Fintype.card α := by
  have ha : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos
  have hb : (0 : ℝ) < Fintype.card β := by exact_mod_cast Fintype.card_pos
  have hm := entropy_matrix_tensorization h hh
  unfold uniformFiniteEntropy
  simp only [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    Real.log_mul ha.ne' hb.ne', ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [Finset.sum_comm (f := fun y x => entropyPhi (h x y)),
    Finset.sum_comm (f := fun y x => h x y)]
  have he :
      ((∑ x, ∑ y, entropyPhi (h x y)) - entropyPhi (∑ x, ∑ y, h x y) +
        (∑ x, ∑ y, h x y) * (Real.log (Fintype.card α) + Real.log (Fintype.card β))) ≤
      ((∑ x, ∑ y, entropyPhi (h x y)) - (∑ y, entropyPhi (∑ x, h x y)) +
        (∑ x, ∑ y, h x y) * Real.log (Fintype.card α)) +
      ((∑ x, ∑ y, entropyPhi (h x y)) - (∑ x, entropyPhi (∑ y, h x y)) +
        (∑ x, ∑ y, h x y) * Real.log (Fintype.card β)) := by linarith
  convert (div_le_div_of_nonneg_right he (mul_pos ha hb).le) using 1
  field_simp


/-- The finite formula is exactly average `x log x` minus `x log x` of the average. -/
theorem uniformFiniteEntropy_eq {α : Type*} [Fintype α] [Nonempty α]
    (h : α → ℝ) :
    uniformFiniteEntropy h = (∑ x, entropyPhi (h x)) / Fintype.card α -
      entropyPhi ((∑ x, h x) / Fintype.card α) := by
  have hn : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he := entropyPhi_div (∑ x, h x) (Fintype.card α) hn
  unfold uniformFiniteEntropy
  field_simp
  nlinarith [he]

/-- Local LSI bounds pass to a product through entropy tensorization. -/
theorem uniformFiniteLSI_tensorization {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (Eα : (α → ℝ) → ℝ) (Eβ : (β → ℝ) → ℝ)
    (hα : ∀ f, uniformFiniteEntropy (fun x => (f x) ^ 2) ≤ Eα f)
    (hβ : ∀ f, uniformFiniteEntropy (fun y => (f y) ^ 2) ≤ Eβ f)
    (f : α × β → ℝ) :
    uniformFiniteEntropy (fun p => (f p) ^ 2) ≤
      (∑ y, Eα (fun x => f (x, y))) / Fintype.card β +
      (∑ x, Eβ (fun y => f (x, y))) / Fintype.card α := by
  refine (uniformFiniteEntropy_tensorization (fun x y => (f (x, y)) ^ 2)
    (fun x y => sq_nonneg _)).trans ?_
  exact add_le_add
    (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun y _ => hα _)) (Nat.cast_nonneg _))
    (div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => hβ _)) (Nat.cast_nonneg _))


end

end MarkovTriple
