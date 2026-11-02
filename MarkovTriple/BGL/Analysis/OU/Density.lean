import MarkovTriple.BGL.Analysis.OU.Hermite
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Complex.TaylorSeries

/-! # OU (Part 5): polynomials are dense in `L²(γ)` -/

open MeasureTheory Filter Topology ProbabilityTheory Polynomial
open scoped ENNReal NNReal Real

namespace MarkovTriple.Sanity.OU

section MGF

lemma integrableExpSet_univ_of {ν : Measure ℝ} (h : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) ν) :
    integrableExpSet id ν = Set.univ := by
  ext t; simpa [integrableExpSet] using h t

lemma complexMGF_series (ν : Measure ℝ) [IsFiniteMeasure ν]
    (h : ∀ t : ℝ, Integrable (fun x : ℝ => Real.exp (t * x)) ν) (z : ℂ) :
    complexMGF id ν z =
      ∑' n : ℕ, ((n.factorial : ℂ)⁻¹ * ((∫ x, x ^ n ∂ν : ℝ) : ℂ)) * z ^ n := by
  have hU := integrableExpSet_univ_of h
  have hdiff : Differentiable ℂ (complexMGF id ν) := by
    have := differentiableOn_complexMGF (X := id) (μ := ν)
    rw [hU] at this
    simp only [interior_univ, Set.mem_univ] at this
    exact differentiableOn_univ.1 (by simpa using this)
  have := Complex.taylorSeries_eq_of_entire' hdiff (c := 0) (z := z)
  rw [← this]
  refine tsum_congr fun n => ?_
  have hd : iteratedDeriv n (complexMGF id ν) 0 = ((∫ x, x ^ n ∂ν : ℝ) : ℂ) := by
    rw [iteratedDeriv_complexMGF (by simp [hU]) n]
    simp only [id, zero_mul, Complex.exp_zero, mul_one]
    have e : ∀ x : ℝ, ((x : ℂ)) ^ n = ((x ^ n : ℝ) : ℂ) := fun x => by push_cast; rfl
    simp_rw [e]
    exact integral_ofReal
  rw [hd]; simp

lemma memLp_exp_mul (t : ℝ) : MemLp (fun x : ℝ => Real.exp (t * x)) 2 γ := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  have := integrable_exp_mul_gaussianReal (μ := 0) (v := 1) (2 * t)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only []
  rw [sq, ← Real.exp_add]; ring_nf

lemma integrable_exp_withDensity {g : ℝ → ℝ} (hg : MemLp g 2 γ) (hg0 : ∀ x, 0 ≤ g x)
    (hgm : Measurable g) (t : ℝ) :
    Integrable (fun x : ℝ => Real.exp (t * x)) (γ.withDensity fun x => ENNReal.ofReal (g x)) := by
  rw [integrable_withDensity_iff_integrable_smul' (hgm.ennreal_ofReal)
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  have := hg.integrable_mul (memLp_exp_mul t)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hg0 x)]

lemma integral_pow_withDensity {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) (hgm : Measurable g) (n : ℕ) :
    ∫ x, x ^ n ∂(γ.withDensity fun x => ENNReal.ofReal (g x)) = ∫ x, g x * x ^ n ∂γ := by
  rw [integral_withDensity_eq_integral_toReal_smul hgm.ennreal_ofReal
    (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp [ENNReal.toReal_ofReal (hg0 x)]

end MGF

/-- **Polynomials are dense in `L²(γ)`** (orthogonal complement form). -/
theorem eq_zero_of_orth_poly_meas (u : ℝ → ℝ) (hum : Measurable u) (hu : MemLp u 2 γ)
    (h : ∀ n : ℕ, ∫ x, x ^ n * u x ∂γ = 0) : u =ᵐ[γ] 0 := by
  set up : ℝ → ℝ := fun x => max (u x) 0 with hup_def
  set um : ℝ → ℝ := fun x => max (-u x) 0 with hum_def
  have hup : MemLp up 2 γ := hu.pos_part
  have hun : MemLp um 2 γ := hu.neg_part
  have hupm : Measurable up := hum.max measurable_const
  have hunm : Measurable um := hum.neg.max measurable_const
  have hup0 : ∀ x, 0 ≤ up x := fun x => le_max_right _ _
  have hun0 : ∀ x, 0 ≤ um x := fun x => le_max_right _ _
  have hfin : ∀ {g : ℝ → ℝ}, MemLp g 2 γ → (∀ x, 0 ≤ g x) → Measurable g →
      IsFiniteMeasure (γ.withDensity fun x => ENNReal.ofReal (g x)) := by
    intro g hg hg0 hgm
    refine isFiniteMeasure_withDensity_ofReal ?_
    exact (hg.integrable one_le_two).hasFiniteIntegral
  have := hfin hup hup0 hupm
  have := hfin hun hun0 hunm
  set a := γ.withDensity fun x => ENNReal.ofReal (up x) with ha
  set b := γ.withDensity fun x => ENNReal.ofReal (um x) with hb
  have hmom : ∀ n : ℕ, ∫ x, x ^ n ∂a = ∫ x, x ^ n ∂b := by
    intro n
    rw [ha, hb, integral_pow_withDensity hup0 hupm, integral_pow_withDensity hun0 hunm]
    have hpn : MemLp (fun x : ℝ => x ^ n) 2 γ := by
      have := (pf_PG (X ^ n)).memLp_two
      have e : (fun x : ℝ => x ^ n) = pf (X ^ n) := by funext x; simp [pf]
      rw [e]; exact this
    have i1 : Integrable (fun x => up x * x ^ n) γ := by
      have := hup.integrable_mul hpn
      exact this
    have i2 : Integrable (fun x => um x * x ^ n) γ := hun.integrable_mul hpn
    rw [← sub_eq_zero, ← integral_sub i1 i2]
    have := h n
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hup_def, hum_def]
    rcases le_total 0 (u x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  have hmgf : complexMGF id a = complexMGF id b := by
    funext z
    rw [complexMGF_series a (integrable_exp_withDensity hup hup0 hupm),
      complexMGF_series b (integrable_exp_withDensity hun hun0 hunm)]
    exact tsum_congr fun n => by rw [hmom n]
  have hab : a = b := Measure.ext_of_complexMGF_id_eq hmgf
  have hae : (fun x => ENNReal.ofReal (up x)) =ᵐ[γ] fun x => ENNReal.ofReal (um x) :=
    (withDensity_eq_iff hupm.ennreal_ofReal.aemeasurable hunm.ennreal_ofReal.aemeasurable
      (by
        rw [← ofReal_integral_eq_lintegral_ofReal (hup.integrable one_le_two) (ae_of_all _ hup0)]
        exact ENNReal.ofReal_ne_top)).1 hab
  filter_upwards [hae] with x hx
  have := (ENNReal.ofReal_eq_ofReal_iff (hup0 x) (hun0 x)).1 hx
  simp only [hup_def, hum_def] at this
  simp only [Pi.zero_apply]
  rcases le_total 0 (u x) with hx0 | hx0
  · rw [max_eq_left hx0, max_eq_right (by linarith)] at this; linarith
  · rw [max_eq_right hx0, max_eq_left (by linarith)] at this; linarith

theorem eq_zero_of_orth_poly (u : ℝ → ℝ) (hu : MemLp u 2 γ)
    (h : ∀ n : ℕ, ∫ x, x ^ n * u x ∂γ = 0) : u =ᵐ[γ] 0 := by
  have hae := hu.aestronglyMeasurable.ae_eq_mk
  set v := hu.aestronglyMeasurable.mk u
  have hv : MemLp v 2 γ := hu.ae_eq hae
  have hvm : Measurable v := hu.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have : v =ᵐ[γ] 0 := eq_zero_of_orth_poly_meas v hvm hv (fun n => by
    rw [← h n]
    exact integral_congr_ae (by filter_upwards [hae] with x hx; rw [hx]))
  filter_upwards [hae, this] with x h1 h2
  rw [h1, h2]

end MarkovTriple.Sanity.OU
