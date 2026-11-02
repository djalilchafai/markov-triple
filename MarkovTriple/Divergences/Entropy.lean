import Mathlib

/-!
# Relative entropy `Ent` and its bridge to Mathlib's `klDiv`

`Ent μ f = ∫ f log f dμ - (∫ f dμ) log (∫ f dμ)` (defined here; formerly in the legacy `MarkovTriple.Frozen.Ent`) is the single entropy functional of the library.
It unifies `entL` (cutoff-rigidity-diffusions, `Riemann/DiffTight.lean`) and `squareEntropy`
(ginibre-poincare, `Analysis/GinibreEntropy.lean`), the latter being `Ent μ (f ^ 2)`.
-/

open MeasureTheory InformationTheory
open scoped ENNReal

namespace MarkovTriple

/-- The entropy `Ent_μ(f) = ∫ f log f dμ − (∫ f dμ) log (∫ f dμ)` (BGL (5.1.1)).
Intended for `f ≥ 0` and `μ` a probability measure; uses the Mathlib conventions `0 log 0 = 0`
(`Real.log 0 = 0`). Junk value `0` if `f log f` is not integrable (Bochner convention).
(Same formula as `MarkovTriple.BGL.Ent`.) -/
noncomputable def Ent {E : Type*} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) : ℝ :=
  (∫ x, f x * Real.log (f x) ∂μ) - (∫ x, f x ∂μ) * Real.log (∫ x, f x ∂μ)

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Square entropy `Ent_μ(f²)`, definitionally an instance of `Ent`. -/
noncomputable abbrev squareEntropy (μ : Measure α) (f : α → ℝ) : ℝ :=
  Ent μ (fun x => f x ^ 2)

theorem squareEntropy_def (μ : Measure α) (f : α → ℝ) :
    squareEntropy μ f =
      (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) -
        (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ) := rfl

/-- Jensen: entropy of a nonnegative function is nonnegative for a probability law. -/
theorem Ent_nonneg (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (hf : Integrable f μ) (hlog : Integrable (fun x => f x * Real.log (f x)) μ) :
    0 ≤ Ent μ f := by
  have hj := Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall hf0) hf hlog
  exact sub_nonneg.mpr hj

theorem squareEntropy_nonneg (μ : Measure α) [IsProbabilityMeasure μ] (f : α → ℝ)
    (hf : Integrable (fun x => f x ^ 2) μ)
    (hlog : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ) :
    0 ≤ squareEntropy μ f :=
  Ent_nonneg μ _ (fun x => sq_nonneg (f x)) hf hlog

/-- Entropy transfer under an image measure. -/
theorem Ent_map (μ : Measure α) (T : α → β) (hT : AEMeasurable T μ) (f : β → ℝ)
    (hf : AEStronglyMeasurable f (μ.map T))
    (hlog : AEStronglyMeasurable (fun y => f y * Real.log (f y)) (μ.map T)) :
    Ent (μ.map T) f = Ent μ (fun x => f (T x)) := by
  unfold Ent
  rw [integral_map hT hf, integral_map hT hlog]

theorem squareEntropy_map (μ : Measure α) (T : α → β) (hT : AEMeasurable T μ) (f : β → ℝ)
    (hsq : AEStronglyMeasurable (fun y => f y ^ 2) (μ.map T))
    (hlog : AEStronglyMeasurable (fun y => f y ^ 2 * Real.log (f y ^ 2)) (μ.map T)) :
    squareEntropy (μ.map T) f = squareEntropy μ (fun x => f (T x)) :=
  Ent_map μ T hT _ hsq hlog

/-- Equal moments give equal entropy. -/
theorem Ent_eq_of_moments (μ : Measure α) (ν : Measure β) (f : α → ℝ) (g : β → ℝ)
    (h1 : (∫ x, f x ∂μ) = ∫ y, g y ∂ν)
    (h2 : (∫ x, f x * Real.log (f x) ∂μ) = ∫ y, g y * Real.log (g y) ∂ν) :
    Ent μ f = Ent ν g := by
  simp only [Ent, h1, h2]

theorem squareEntropy_eq_of_moments (μ : Measure α) (ν : Measure β) (f : α → ℝ) (g : β → ℝ)
    (hsq : (∫ x, f x ^ 2 ∂μ) = ∫ y, g y ^ 2 ∂ν)
    (hlog : (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) = ∫ y, g y ^ 2 * Real.log (g y ^ 2) ∂ν) :
    squareEntropy μ f = squareEntropy ν g :=
  Ent_eq_of_moments μ ν _ _ hsq hlog

/-! ### Bridge to `klDiv` -/

/-- For a normalized nonnegative density, the entropy is the genuine Kullback–Leibler divergence
of the weighted probability law (source: cutoff-rigidity-diffusions `EntropyDissipation.lean`). -/
theorem klDiv_withDensity_eq_ofReal_integral (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (hfInt : Integrable f μ) (hnorm : ∫ x, f x ∂μ = 1)
    (hentropy : Integrable (fun x => f x * Real.log (f x)) μ) :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (∫ x, f x * Real.log (f x) ∂μ) := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  have hprob : IsProbabilityMeasure ν := by
    constructor
    dsimp [ν]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hfInt (Filter.Eventually.of_forall hpos), hnorm]
    simp
  have hAC : ν ≪ μ := withDensity_absolutelyContinuous _ _
  have hRN : (fun x => (ν.rnDeriv μ x).toReal) =ᵐ[μ] f := by
    filter_upwards [Measure.rnDeriv_withDensity μ (by fun_prop :
      Measurable (fun x => ENNReal.ofReal (f x)))] with x hx
    rw [hx, ENNReal.toReal_ofReal (hpos x)]
  have hfun : (fun x => klFun (ν.rnDeriv μ x).toReal) =ᵐ[μ]
      (fun x => f x * Real.log (f x) + 1 - f x) := by
    filter_upwards [hRN] with x hx
    rw [hx]
    rfl
  have hInt : Integrable (fun x => klFun (ν.rnDeriv μ x).toReal) μ :=
    ((hentropy.add (integrable_const 1)).sub hfInt).congr hfun.symm
  have hllr := (integrable_klFun_rnDeriv_iff hAC).mp hInt
  rw [klDiv_eq_integral_klFun, ite_eq_left ⟨hAC, hllr⟩, integral_congr_ae hfun]
  have hsub := integral_sub (hentropy.add (integrable_const 1)) hfInt
  have hadd := integral_add hentropy (integrable_const 1)
  simp only [Pi.add_apply] at hsub hadd
  rw [hsub, hadd, integral_const, hnorm]
  simp

/-- `Ent` form of the bridge: under the same hypotheses, `klDiv ν μ = ofReal (Ent μ f)`. -/
theorem klDiv_withDensity_eq_ofReal_Ent (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (hpos : ∀ x, 0 ≤ f x)
    (hfInt : Integrable f μ) (hnorm : ∫ x, f x ∂μ = 1)
    (hentropy : Integrable (fun x => f x * Real.log (f x)) μ) :
    klDiv (μ.withDensity (fun x => ENNReal.ofReal (f x))) μ =
      ENNReal.ofReal (Ent μ f) := by
  rw [klDiv_withDensity_eq_ofReal_integral μ f hf hpos hfInt hnorm hentropy]
  simp [Ent, hnorm]

/-- Finite relative entropy is exactly integrability of `h log h`, `h = dν/dμ`. -/
theorem klDiv_ne_top_iff_integrable_rnDeriv_mul_log (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv ν μ ≠ ∞ ↔ ν ≪ μ ∧
      Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ := by
  rw [klDiv_ne_top_iff]
  constructor
  · rintro ⟨hAC, h⟩
    refine ⟨hAC, ?_⟩
    have hk := (integrable_klFun_rnDeriv_iff hAC).2 h
    have := (hk.sub (integrable_const (1 : ℝ))).add
      (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, klFun]
    ring
  · rintro ⟨hAC, h⟩
    refine ⟨hAC, (integrable_klFun_rnDeriv_iff hAC).1 ?_⟩
    have := (h.add (integrable_const (1 : ℝ))).sub (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ))
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, klFun]

/-- **Bridge** `klDiv = Ent` of the Radon–Nikodym density: for `ν ≪ μ` probability measures with
`h log h` integrable, `klDiv ν μ = ofReal (Ent μ (dν/dμ))`. -/
theorem klDiv_eq_ofReal_Ent_rnDeriv (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hAC : ν ≪ μ)
    (hent : Integrable (fun x => (ν.rnDeriv μ x).toReal * Real.log (ν.rnDeriv μ x).toReal) μ) :
    klDiv ν μ = ENNReal.ofReal (Ent μ (fun x => (ν.rnDeriv μ x).toReal)) := by
  have hnorm : ∫ x, (ν.rnDeriv μ x).toReal ∂μ = 1 := by
    rw [Measure.integral_toReal_rnDeriv hAC]; simp
  have hfin : klDiv ν μ ≠ ∞ := (klDiv_ne_top_iff_integrable_rnDeriv_mul_log μ ν).2 ⟨hAC, hent⟩
  have hk := (klDiv_ne_top_iff.1 hfin)
  have hk' := (integrable_klFun_rnDeriv_iff hAC).2 hk.2
  have := toReal_klDiv_eq_integral_klFun hAC (μ := ν) (ν := μ)
  have hsub := integral_sub (hent.add (integrable_const 1)) (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ))
  have hadd := integral_add hent (integrable_const 1)
  simp only [Pi.add_apply] at hsub hadd
  have hEnt : Ent μ (fun x => (ν.rnDeriv μ x).toReal) = (klDiv ν μ).toReal := by
    rw [this]
    simp only [klFun]
    rw [hsub, hadd, hnorm]
    simp [Ent, hnorm]
  rw [hEnt, ENNReal.ofReal_toReal hfin]

/-- Real-valued form: `(klDiv ν μ).toReal = Ent μ (dν/dμ)` when `klDiv ν μ < ∞`. -/
theorem toReal_klDiv_eq_Ent_rnDeriv (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (hfin : klDiv ν μ ≠ ∞) :
    (klDiv ν μ).toReal = Ent μ (fun x => (ν.rnDeriv μ x).toReal) := by
  obtain ⟨hAC, hent⟩ := (klDiv_ne_top_iff_integrable_rnDeriv_mul_log μ ν).1 hfin
  have h := klDiv_eq_ofReal_Ent_rnDeriv μ ν hAC hent
  have hn : 0 ≤ Ent μ (fun x => (ν.rnDeriv μ x).toReal) :=
    Ent_nonneg μ _ (fun x => ENNReal.toReal_nonneg)
      (Measure.integrable_toReal_rnDeriv (μ := ν) (ν := μ)) hent
  rw [h, ENNReal.toReal_ofReal hn]

end MarkovTriple
