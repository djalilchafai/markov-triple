import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctIBP

/-!
# Gibbs measures: the cut-off argument of BGL Prop. 3.2.1 / 3.3.10 / 3.3.11

Let `f ∈ 𝒜 = C^∞(ℝ) ∩ L²(μ)` with `L f = λ f`, `λ ∈ {0, 1}`, and let `(ζ_k)` be the complete-ness
sequence of BGL Def. 3.3.9 (`gibbsDiff_isComplete`).  Testing the equation against `f ζ_k²` (F7 on `𝒜`,
`ibp_sm`) gives, with `ε = 1/(k+1)` and `|ζ_k'| ≤ ε`,
`λ ∫ f² ζ² + ∫ ζ² f'² = -2 ∫ f ζ ζ' f' ≤ ε (‖f‖² + ∫ ζ² f'²)`
(this is the computation in the proof of BGL Prop. 3.2.1).  Letting `k → ∞` (Fatou) yields
* `λ = 1`: `f = 0` a.e. (the `ESA` criterion `ker (L* - 1) = 0`, Prop. 3.2.1);
* `λ = 0`: `f' = 0`, so `f` is constant (ergodicity, Prop. 3.3.10 once connexity is used).
-/

open MeasureTheory Filter Topology
open MarkovTriple.Sanity.OU hiding A₀ γ φ

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

/-- Fatou step: if `∫ h ζ_k² ≤ δ_k → 0` and `ζ_k → 1` a.e., then `h = 0` a.e. (`h ≥ 0`). -/
lemma zero_of_cutoff {μ : Measure ℝ} {h : ℝ → ℝ} (hm : Measurable h) (h0 : ∀ x, 0 ≤ h x)
    {ζ : ℕ → ℝ → ℝ} (hζm : ∀ k, Measurable (ζ k))
    (hζ : ∀ᵐ x ∂μ, Tendsto (fun k => ζ k x) atTop (𝓝 1))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0))
    (hint : ∀ k, Integrable (fun x => h x * (ζ k x * ζ k x)) μ)
    (hb : ∀ᶠ k in atTop, ∫ x, h x * (ζ k x * ζ k x) ∂μ ≤ δ k) : h =ᵐ[μ] 0 := by
  set F : ℕ → ℝ → ENNReal := fun k x => ENNReal.ofReal (h x * (ζ k x * ζ k x)) with hFdef
  have hF : ∀ k, Measurable (F k) := fun k =>
    ENNReal.measurable_ofReal.comp (hm.mul ((hζm k).mul (hζm k)))
  have hlim : ∀ᵐ x ∂μ, Filter.liminf (fun k => F k x) atTop = ENNReal.ofReal (h x) := by
    filter_upwards [hζ] with x hx
    have h1 : Tendsto (fun k => h x * (ζ k x * ζ k x)) atTop (𝓝 (h x * (1 * 1))) :=
      tendsto_const_nhds.mul (hx.mul hx)
    rw [mul_one, mul_one] at h1
    have h2 : Tendsto (fun k => F k x) atTop (𝓝 (ENNReal.ofReal (h x))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp h1
    exact h2.liminf_eq
  have hfat : ∫⁻ x, Filter.liminf (fun k => F k x) atTop ∂μ ≤
      Filter.liminf (fun k => ∫⁻ x, F k x ∂μ) atTop := lintegral_liminf_le hF
  have hI : ∀ k, ∫⁻ x, F k x ∂μ = ENNReal.ofReal (∫ x, h x * (ζ k x * ζ k x) ∂μ) := fun k =>
    (ofReal_integral_eq_lintegral_ofReal (hint k)
      (Eventually.of_forall fun x => mul_nonneg (h0 x) (mul_self_nonneg _))).symm
  have hδ' : Tendsto (fun k => ENNReal.ofReal (δ k)) atTop (𝓝 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hδ
    simpa [Function.comp_def] using this
  have hle : Filter.liminf (fun k => ∫⁻ x, F k x ∂μ) atTop ≤ 0 := by
    have h1 : Filter.liminf (fun k => ∫⁻ x, F k x ∂μ) atTop ≤
        Filter.liminf (fun k => ENNReal.ofReal (δ k)) atTop := by
      refine liminf_le_liminf ?_
      filter_upwards [hb] with k hk
      rw [hI k]
      exact ENNReal.ofReal_le_ofReal hk
    rw [hδ'.liminf_eq] at h1
    exact h1
  have h2 : ∫⁻ x, ENNReal.ofReal (h x) ∂μ = 0 := by
    have : ∫⁻ x, ENNReal.ofReal (h x) ∂μ = ∫⁻ x, Filter.liminf (fun k => F k x) atTop ∂μ :=
      lintegral_congr_ae (hlim.mono fun x hx => hx.symm)
    rw [this]
    exact le_antisymm (hfat.trans hle) bot_le
  have h3 := (lintegral_eq_zero_iff (ENNReal.measurable_ofReal.comp hm)).1 h2
  filter_upwards [h3] with x hx
  have : h x ≤ 0 := by simpa [ENNReal.ofReal_eq_zero] using hx
  exact le_antisymm this (h0 x)

section Cut

variable (G : GibbsData)

/-- The basic cut-off estimate: for `ζ ∈ 𝒜₀` with `|ζ'| ≤ ε` a.e., and smooth `f ∈ L²` with
`L f = λ f`:  `λ ∫ f²ζ² + ∫ f'² ζ² ≤ ε (∫ f² + ∫ f'² ζ²)` (proof of BGL Prop. 3.2.1). -/
lemma cutoff_ineq {f ζ : ℝ → ℝ} (hf : Sm f) (hfL2 : MemLp f 2 G.μ) (hζ : ζ ∈ OA₀) (lam ε : ℝ)
    (hε : 0 ≤ ε) (hζε : ∀ᵐ x ∂G.μ, deriv ζ x * deriv ζ x ≤ ε ^ 2)
    (hL : ∀ x, Lg G.V f x = lam * f x) :
    lam * ∫ x, f x ^ 2 * (ζ x * ζ x) ∂G.μ + ∫ x, deriv f x ^ 2 * (ζ x * ζ x) ∂G.μ ≤
      ε * (∫ x, f x ^ 2 ∂G.μ + ∫ x, deriv f x ^ 2 * (ζ x * ζ x) ∂G.μ) := by
  have hζs : Sm ζ := hζ.1
  have hζc : HasCompactSupport ζ := hζ.2
  have hζζc : HasCompactSupport (fun x => ζ x * ζ x) := hζc.mul_right
  set g : ℝ → ℝ := fun x => f x * (ζ x * ζ x) with hg
  have hgs : Sm g := hf.mul (hζs.mul hζs)
  have hgc : HasCompactSupport g := hζζc.mul_left
  have hdg : ∀ x, deriv g x = deriv f x * (ζ x * ζ x) +
      f x * (deriv ζ x * ζ x + ζ x * deriv ζ x) := by
    intro x
    have := (hf.hasDerivAt x).mul (((hζs.hasDerivAt x)).mul (hζs.hasDerivAt x))
    exact this.deriv
  have hibp := G.ibp_sm (f := f) (g := g) hf hgs (Or.inl hgc)
  -- integrands
  have cont_f := hf.continuous
  have cont_f' := hf.deriv'.continuous
  have cont_ζ := hζs.continuous
  have cont_ζ' := hζs.deriv'.continuous
  have iA : Integrable (fun x => f x ^ 2 * (ζ x * ζ x)) G.μ :=
    ((cont_f.pow 2).mul (cont_ζ.mul cont_ζ)).integrable_of_hasCompactSupport hζζc.mul_left
  have iB : Integrable (fun x => deriv f x ^ 2 * (ζ x * ζ x)) G.μ :=
    ((cont_f'.pow 2).mul (cont_ζ.mul cont_ζ)).integrable_of_hasCompactSupport hζζc.mul_left
  have iC : Integrable (fun x => f x * deriv ζ x * ζ x * deriv f x) G.μ := by
    refine (((cont_f.mul cont_ζ').mul cont_ζ).mul cont_f').integrable_of_hasCompactSupport ?_
    exact (hζc.mul_left (f := fun x => f x * deriv ζ x)).mul_right
  have iN : Integrable (fun x => f x ^ 2) G.μ := hfL2.integrable_sq
  -- LHS
  have hlhs : ∫ x, g x * Lg G.V f x ∂G.μ = lam * ∫ x, f x ^ 2 * (ζ x * ζ x) ∂G.μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hg, hL x]; ring
  have hrhs : ∫ x, deriv g x * deriv f x ∂G.μ =
      ∫ x, deriv f x ^ 2 * (ζ x * ζ x) ∂G.μ +
        2 * ∫ x, f x * deriv ζ x * ζ x * deriv f x ∂G.μ := by
    rw [← integral_const_mul, ← integral_add iB (iC.const_mul 2)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    dsimp only
    rw [hdg x]; ring
  rw [hlhs, hrhs] at hibp
  -- the pointwise bound
  have hbd : ∀ᵐ x ∂G.μ, -(2 * (f x * deriv ζ x * ζ x * deriv f x)) ≤
      ε * (f x ^ 2 + deriv f x ^ 2 * (ζ x * ζ x)) := by
    filter_upwards [hζε] with x hx
    set a := f x
    set b := ζ x * deriv f x with hb
    set c := deriv ζ x with hc
    have hcε : |c| ≤ ε := by
      have : c ^ 2 ≤ ε ^ 2 := by nlinarith [hx]
      exact abs_le_of_sq_le_sq' this hε |> fun h => abs_le.2 h
    have e1 : f x * deriv ζ x * ζ x * deriv f x = a * b * c := by
      simp only [hb, hc, a]; ring
    have e2 : deriv f x ^ 2 * (ζ x * ζ x) = b ^ 2 := by
      simp only [hb]; ring
    rw [e1, e2]
    have h1 : -(2 * (a * b * c)) ≤ 2 * (|a| * |b|) * ε := by
      have : |a * b * c| ≤ |a| * |b| * ε := by
        rw [abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left hcε (by positivity)
      have := neg_abs_le (a * b * c)
      have h2 := le_abs_self (a * b * c)
      nlinarith [abs_nonneg a, abs_nonneg b]
    have h2 : 2 * (|a| * |b|) ≤ a ^ 2 + b ^ 2 := by
      nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
    nlinarith [mul_le_mul_of_nonneg_right h2 hε]
  have hint : ∫ x, -(2 * (f x * deriv ζ x * ζ x * deriv f x)) ∂G.μ ≤
      ∫ x, ε * (f x ^ 2 + deriv f x ^ 2 * (ζ x * ζ x)) ∂G.μ :=
    integral_mono_ae (iC.const_mul 2).neg ((iN.add iB).const_mul ε) hbd
  rw [integral_neg, integral_const_mul, integral_const_mul, integral_add iN iB] at hint
  linarith

end Cut

end MarkovTriple.BGL.Instances.Gibbs
