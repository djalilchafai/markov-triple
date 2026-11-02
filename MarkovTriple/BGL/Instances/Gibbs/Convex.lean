import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Diffusion

/-!
# Uniformly convex potentials: `e^{-V}` is integrable, and the Gibbs triple is complete with `Γ₂ ≥ ρ Γ`

For `V` smooth with `V'' ≥ ρ > 0`: `V(x) ≥ V(0) + V'(0) x + ρ x²/2` (`quad_lower`), so `e^{-V}` is dominated by a
Gaussian and `GibbsData` exists (`ofConvex`).  `V = x²/2` recovers the standard Gaussian `γ` of the OU
triple (`ouData_μ`), with the same `L` and `Γ`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU hiding A₀ γ φ

namespace MarkovTriple.BGL.Instances.Gibbs

/-- quadratic lower bound from `V'' ≥ ρ`. -/
lemma quad_lower {V : ℝ → ℝ} (hV : Sm V) {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv V) x) (x : ℝ) :
    V 0 + deriv V 0 * x + ρ * x ^ 2 / 2 ≤ V x := by
  set k : ℝ → ℝ := fun y => deriv V y - deriv V 0 - ρ * y with hk
  have hkd : ∀ y, HasDerivAt k (deriv (deriv V) y - ρ) y := fun y => by
    have := ((hV.deriv'.hasDerivAt y).sub_const (deriv V 0)).sub ((hasDerivAt_id y).const_mul ρ)
    convert this using 1
    · funext z; simp [hk]
    · simp
  have kmono : Monotone k := monotone_of_deriv_nonneg (fun y => (hkd y).differentiableAt)
    (fun y => by rw [(hkd y).deriv]; linarith [hρ y])
  have k0 : k 0 = 0 := by simp [hk]
  set h : ℝ → ℝ := fun y => V y - V 0 - deriv V 0 * y - ρ * y ^ 2 / 2 with hh
  have hhd : ∀ y, HasDerivAt h (k y) y := fun y => by
    have := (((hV.hasDerivAt y).sub_const (V 0)).sub ((hasDerivAt_id y).const_mul (deriv V 0))).sub
      (((hasDerivAt_id y).pow 2).const_mul ρ |>.div_const 2)
    refine this.congr_deriv ?_
    simp only [hk]; simp; ring
  have h0 : h 0 = 0 := by simp [hh]
  rcases le_total 0 x with hx | hx
  · have : MonotoneOn h (Set.Ici 0) := monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun y _ => (hhd y).continuousAt.continuousWithinAt)
      (fun y _ => (hhd y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [(hhd y).deriv]
        have hy' : 0 < y := by simpa using hy
        have := kmono hy'.le
        simpa [k0] using this)
    have := this (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hx) hx
    rw [h0] at this
    simp only [hh] at this; linarith
  · have : AntitoneOn h (Set.Iic 0) := antitoneOn_of_deriv_nonpos (convex_Iic 0)
      (fun y _ => (hhd y).continuousAt.continuousWithinAt)
      (fun y _ => (hhd y).differentiableAt.differentiableWithinAt)
      (fun y hy => by
        rw [(hhd y).deriv]
        have hy' : y < 0 := by simpa using hy
        have := kmono hy'.le
        simpa [k0] using this)
    have := this (Set.mem_Iic.2 hx) (Set.mem_Iic.2 le_rfl) hx
    rw [h0] at this
    simp only [hh] at this; linarith

/-- `e^{-V}` is integrable for uniformly convex `V`. -/
lemma integrable_of_convex {V : ℝ → ℝ} (hV : Sm V) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : ∀ x, ρ ≤ deriv (deriv V) x) : Integrable (fun x => Real.exp (-V x)) := by
  set a := deriv V 0
  set C := Real.exp (-V 0 + a ^ 2 / ρ)
  have hg : Integrable (fun x : ℝ => C * Real.exp (-(ρ / 4) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by positivity : 0 < ρ / 4)).const_mul C |>.congr
      (Filter.Eventually.of_forall fun x => by simp [neg_mul])
  refine Integrable.mono' hg (Real.continuous_exp.comp hV.continuous.neg).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 := quad_lower hV hρ x
  have h2 : -(a * x) - ρ * x ^ 2 / 4 ≤ a ^ 2 / ρ := by
    have : 0 ≤ (ρ / 2) * (x + 2 * a / ρ) ^ 2 := by positivity
    have e : (ρ / 2) * (x + 2 * a / ρ) ^ 2 = ρ * x ^ 2 / 2 + 2 * a * x + 2 * (a ^ 2 / ρ) := by
      field_simp; ring
    nlinarith
  nlinarith

/-- Gibbs data from a uniformly convex smooth potential. -/
noncomputable def ofConvex {V : ℝ → ℝ} (hV : Sm V) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : ∀ x, ρ ≤ deriv (deriv V) x) : GibbsData :=
  ⟨V, hV, integrable_of_convex hV hρpos hρ⟩

/-- **Uniformly convex Gibbs measures** (`V'' ≥ ρ > 0`): the `DiffusionTriple` `gibbsDiff`, its completeness and
the curvature inequality `Γ₂ ≥ ρ Γ`, bundled. -/
theorem gibbs_convex {V : ℝ → ℝ} (hV : Sm V) {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : ∀ x, ρ ≤ deriv (deriv V) x) :
    (ofConvex hV hρpos hρ).gibbsDiff.IsComplete ∧
      ∀ f : ℝ → ℝ, Sm f → ∀ x, ρ * (ofConvex hV hρpos hρ).gibbsDiff.ΓA f f x ≤
        (ofConvex hV hρpos hρ).gibbsDiff.Γ₂ f f x :=
  ⟨(ofConvex hV hρpos hρ).gibbsDiff_isComplete,
    fun _ hf x => (ofConvex hV hρpos hρ).gibbsDiff_Γ₂_ge hρ hf x⟩

/-! ### The Gaussian case `V = x²/2` -/

/-- the standard Gaussian potential -/
noncomputable def ouData : GibbsData :=
  ofConvex (V := fun x : ℝ => x ^ 2 / 2) ((contDiff_id.pow 2).div_const 2) (ρ := 1) one_pos (fun x => by
    have h : deriv (fun x : ℝ => x ^ 2 / 2) = fun x => x := by
      funext y; simp
    rw [h]; simp)

lemma ouData_deriv : deriv ouData.V = fun x => x := by
  funext y; simp [ouData, ofConvex]

/-- for `V = x²/2` the generator is the OU generator `Lo`. -/
theorem ouData_L (f : ℝ → ℝ) : Lg ouData.V f = Lo f := by
  funext x; simp [Lg, Lo, ouData_deriv]

/-- for `V = x²/2` the carré du champ is the OU one (`Γ = Go` by definition). -/
theorem ouData_Γ : ouData.gibbsDiff.Γ = Go := rfl

/-- for `V = x²/2` the Gibbs probability measure is the standard Gaussian `γ = N(0,1)`. -/
theorem ouData_μ : ouData.μ = MarkovTriple.Sanity.OU.γ := by
  have hZ : ouData.Z = Real.sqrt (2 * Real.pi) := by
    unfold GibbsData.Z
    have := integral_gaussian (1 / 2 : ℝ)
    have e : (fun x : ℝ => Real.exp (-ouData.V x)) = fun x => Real.exp (-(1 / 2) * x ^ 2) := by
      funext x; simp [ouData, ofConvex]; ring_nf
    rw [e, this]
    congr 1; field_simp
  unfold MarkovTriple.Sanity.OU.γ
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero]
  unfold GibbsData.μ
  congr 1
  funext x
  rw [gaussianPDF]
  congr 1
  rw [gaussianPDFReal]
  simp only [GibbsData.w, hZ]
  have e : -ouData.V x = -(x - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) := by
    simp [ouData, ofConvex]; ring
  rw [e]
  simp
  ring

end MarkovTriple.BGL.Instances.Gibbs
