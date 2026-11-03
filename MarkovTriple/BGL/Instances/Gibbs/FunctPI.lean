import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctAlgebra
import MarkovTriple.BGL.Theory.Poincare

/-!
# Gibbs measures: Poincaré inequality with constant `1/ρ` (spectral gap `ρ`) by the book's route

BGL, Prop. 4.8.3 / Cor. 4.8.2 (route recorded in `Theory/Poincare.lean`): for a Diffusion Markov Triple

1. integrated `Γ₂`: `∫ Γ₂(f) dμ = ∫ (L f)² dμ` for `f ∈ 𝒜₀` (BGL (3.3.8));
2. `Γ₂ ≥ ρ Γ` pointwise (here the Bochner formula `Γ₂ = f''² + V'' f'²`, `gibbsDiff_Γ₂_ge`)
   gives `ρ ℰ(f) ≤ ‖L f‖²` on `𝒜₀`;
3. ESA (F10) extends it to `𝒟(L)` and, with ergodicity S10, the resolvent argument
   (`DiffusionTriple.rho_var_le_of`) gives `ρ Var(f) ≤ ℰ(f)`.

Steps 1–2 are proved here for the Gibbs triple without any semigroup input (`gibbs_integrated_CD`).
Step 3 needs F10 and S10, which the book obtains from weak hypo-ellipticity + completeness
(`gibbsDiff_esaProp`, `gibbsDiff_ergodic`); hence the Poincaré theorem below is stated under the
explicit hypothesis `WeakHypo` (BGL Def. 3.3.8) and nothing else.
It needs neither F8 (`P_t 𝒜₀ ⊂ 𝒜`) nor any gradient bound.
-/

open MeasureTheory Filter Topology
open scoped NNReal InnerProductSpace
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- `Γ₂` of the Gibbs triple as the explicit combination of test functions. -/
lemma gibbsDiff_Γ₂_eq_comb {f : ℝ → ℝ} (hf : f ∈ OA₀) :
    G.gibbsDiff.Γ₂ f f = fun x => (Lg G.V (Go f f) x - Go f (Lg G.V f) x - Go (Lg G.V f) f x) / 2 := by
  funext x
  have e1 : G.gibbsDiff.ΓA f f = Go f f := G.gibbsDiff_ΓA hf.1 hf.1
  have e2 : G.gibbsDiff.ΓA f (Lg G.V f) = Go f (Lg G.V f) := G.gibbsDiff_ΓA hf.1 (sm_Lg G.smooth hf.1)
  have e3 : G.gibbsDiff.ΓA (Lg G.V f) f = Go (Lg G.V f) f := G.gibbsDiff_ΓA (sm_Lg G.smooth hf.1) hf.1
  show (Lg G.V (G.gibbsDiff.ΓA f f) x - G.gibbsDiff.ΓA f (Lg G.V f) x -
    G.gibbsDiff.ΓA (Lg G.V f) f x) / 2 = _
  rw [e1, e2, e3]

/-- **BGL (3.3.8) on test functions for the Gibbs triple**: `∫ Γ₂(f) dμ = ∫ (L f)² dμ`. -/
theorem gibbs_integral_Γ₂ {f : ℝ → ℝ} (hf : f ∈ OA₀) :
    ∫ x, G.gibbsDiff.Γ₂ f f x ∂G.μ = ∫ x, Lg G.V f x * Lg G.V f x ∂G.μ := by
  have hLf : Lg G.V f ∈ OA₀ := G.Lg_mem hf
  have m1 : Lg G.V (Go f f) ∈ OA₀ := G.Lg_mem (A₀.Go_mem hf hf)
  have m2 : Go f (Lg G.V f) ∈ OA₀ := A₀.Go_mem hf hLf
  have m3 : Go (Lg G.V f) f ∈ OA₀ := A₀.Go_mem hLf hf
  have i1 : Integrable (Lg G.V (Go f f)) G.μ := G.gibbsDiff.integrable_of_mem m1
  have i2 : Integrable (Go f (Lg G.V f)) G.μ := G.gibbsDiff.integrable_of_mem m2
  have i3 : Integrable (Go (Lg G.V f) f) G.μ := G.gibbsDiff.integrable_of_mem m3
  have h0 : ∫ x, Lg G.V (Go f f) x ∂G.μ = 0 := G.integral_L_zero (A₀.Go_mem hf hf)
  have hib := G.ibp_sm (f := f) (g := Lg G.V f) hf.1 hLf.1 (Or.inr hf.2)
  have h2 : ∫ x, Go f (Lg G.V f) x ∂G.μ = -∫ x, Lg G.V f x * Lg G.V f x ∂G.μ := by
    have : ∫ x, Go f (Lg G.V f) x ∂G.μ = ∫ x, deriv (Lg G.V f) x * deriv f x ∂G.μ :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only [Go]; ring)
    rw [this]
    linarith
  have h3 : ∫ x, Go (Lg G.V f) f x ∂G.μ = ∫ x, Go f (Lg G.V f) x ∂G.μ :=
    integral_congr_ae (Eventually.of_forall fun x => by simp only [Go]; ring)
  rw [G.gibbsDiff_Γ₂_eq_comb hf]
  have i12 : Integrable (fun x => Lg G.V (Go f f) x - Go f (Lg G.V f) x) G.μ := i1.sub i2
  rw [integral_div, integral_sub i12 i3, integral_sub i1 i2, h0, h3, h2]
  ring

/-- **Integrated curvature on `𝒜₀`** for `V'' ≥ ρ`: `ρ ∫ f'² dμ ≤ ∫ (L f)² dμ`. -/
theorem gibbs_integrated_CD {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) {f : ℝ → ℝ} (hf : f ∈ OA₀) :
    ρ * ∫ x, deriv f x * deriv f x ∂G.μ ≤ ∫ x, Lg G.V f x * Lg G.V f x ∂G.μ := by
  have hLf : Lg G.V f ∈ OA₀ := G.Lg_mem hf
  have m1 : Lg G.V (Go f f) ∈ OA₀ := G.Lg_mem (A₀.Go_mem hf hf)
  have m2 : Go f (Lg G.V f) ∈ OA₀ := A₀.Go_mem hf hLf
  have m3 : Go (Lg G.V f) f ∈ OA₀ := A₀.Go_mem hLf hf
  have iΓ : Integrable (Go f f) G.μ := G.gibbsDiff.integrable_of_mem (A₀.Go_mem hf hf)
  have iΓ₂ : Integrable (G.gibbsDiff.Γ₂ f f) G.μ := by
    rw [G.gibbsDiff_Γ₂_eq_comb hf]
    exact (((G.gibbsDiff.integrable_of_mem m1).sub (G.gibbsDiff.integrable_of_mem m2)).sub
      (G.gibbsDiff.integrable_of_mem m3)).div_const 2
  rw [← G.gibbs_integral_Γ₂ hf, ← integral_const_mul]
  refine integral_mono_ae (iΓ.const_mul ρ) iΓ₂ (Eventually.of_forall fun x => ?_)
  have := G.gibbsDiff_Γ₂_ge hρ hf.1 x
  rw [G.gibbsDiff_ΓA hf.1 hf.1] at this
  simpa [Go] using this

/-- The integrated curvature inequality in the `L²` language required by
`DiffusionTriple.rho_var_le_of`: `ρ ℰ(a) ≤ ‖L a‖²` for every test class `a`. -/
theorem gibbs_integrated_CD_cls {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) (a : G.gibbsDiff.A₀) :
    ρ * (-inner ℝ (G.gibbsDiff.Lcls a) (G.gibbsDiff.cls a)) ≤ ‖G.gibbsDiff.Lcls a‖ ^ 2 := by
  have h := G.gibbs_integrated_CD hρ a.2
  have e1 : -inner ℝ (G.gibbsDiff.Lcls a) (G.gibbsDiff.cls a) =
      ∫ x, deriv a.1 x * deriv a.1 x ∂G.μ := by
    rw [DiffusionTriple.inner_Lcls_cls]; simp [gibbsDiff, Go]
  have e2 : ‖G.gibbsDiff.Lcls a‖ ^ 2 = ∫ x, Lg G.V a.1 x * Lg G.V a.1 x ∂G.μ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_Lcls G.gibbsDiff a] with x hx
    rw [hx]; rfl
  rw [e1, e2]
  exact h

/-- **Poincaré inequality for the Gibbs measure `e^{-V}dx` with `V'' ≥ ρ > 0`**, constant `1/ρ`
(spectral gap `ρ`): `Var_μ(f) ≤ ρ⁻¹ ∫ f'² dμ` for all `f ∈ C_c^∞(ℝ)`.  Book route (BGL Cor. 4.8.2,
Prop. 4.8.3) from integrated `Γ₂`, `Γ₂ ≥ ρ Γ`, ESA and ergodicity.  The only analytic input not proved
is the elliptic regularity `WeakHypo` (BGL Def. 3.3.8), through which the
book obtains ESA (Prop. 3.2.1) and ergodicity (Prop. 3.3.10); no semigroup regularity is used. -/
theorem gibbs_poincare {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x)
    (hH : G.WeakHypo) :
    G.gibbsDiff.PI (1 / ρ) := by
  refine ⟨(inferInstance : IsProbabilityMeasure G.gibbsDiff.μ), by positivity, fun f hf => ?_⟩
  have h := DiffusionTriple.rho_var_le_of G.gibbsDiff (G.gibbsDiff_esaProp hH) (G.gibbsDiff_ergodic hH)
    (fun a => G.gibbs_integrated_CD_cls hρ a) hf
  show ProbabilityTheory.variance f G.gibbsDiff.μ ≤ 1 / ρ * ∫ x, G.gibbsDiff.Γ f f x ∂G.gibbsDiff.μ
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hρpos]
  linarith

/-- **Spectral gap `ρ` of the Gibbs semigroup** (Hilbert form, from the Poincaré inequality). -/
theorem gibbs_spectralGap {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x)
    (hH : G.WeakHypo) :
    (DiffusionTriple.formData G.gibbsDiff).HasSpectralGap ρ := by
  have := DiffusionTriple.hasSpectralGap_of_PI G.gibbsDiff (G.gibbsDiff_esaProp hH)
    (G.gibbs_poincare hρpos hρ hH)
  simpa using this

/-- **`L²` exponential decay** of the Friedrichs semigroup `‖P_t u‖ ≤ e^{-ρ t} ‖u‖` for `u ⟂ 1`. -/
theorem gibbs_expDecay {ρ : ℝ} (hρpos : 0 < ρ) (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x)
    (hH : G.WeakHypo) :
    (DiffusionTriple.formData G.gibbsDiff).HasExpDecay ρ := by
  have := DiffusionTriple.expDecay_of_PI G.gibbsDiff (G.gibbsDiff_esaProp hH)
    (G.gibbs_poincare hρpos hρ hH)
  simpa using this

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
