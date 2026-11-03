import Mathlib
import MarkovTriple.Stochastic.RepExtend
import MarkovTriple.BGL.Instances.Circle.Semigroup
import MarkovTriple.BGL.Analysis.Circle.Modes

/-!
# Stochastic layer, part 6: the heat kernel on the circle (wrapped Gaussian)

`𝕋 = ℝ/ℤ`, `μ₀` = Haar probability, generator `L f = f''` (so `L e_n = -(2πn)² e_n`).  The heat
kernel is the **wrapped (periodised) Gaussian**
`κ_t(x, ·) = law of (x + Z mod 1)`, `Z ∼ N(0, 2t)`.

* `circleKernel t` is a Markov kernel; `circleKernel 0 = Kernel.id`;
* **exact Chapman-Kolmogorov** `κ_t ∘ₖ κ_s = κ_{s+t}`: `N(0,2s) ∗ N(0,2t) = N(0,2(s+t))`
  (Mathlib `gaussianReal_conv_gaussianReal`);
* **invariance of the Haar probability**: translation invariance of `μ₀` and Fubini;
* **identification with the Fourier-mode semigroup**: `∫ e_n dκ_t(x,·) = e^{-(2πn)² t} e_n(x)`
  (characteristic function of the Gaussian, `charFun_gaussianReal`), matching
  `P_t e_n = e^{-(2πn)² t} e_n` (`semigroup_mc`, `semigroup_ms`); hence on `trigSpan`;
* extension to all bounded measurable `L²` functions by `kernelRep_of_dense` (`trigSpan` is dense:
  Stone-Weierstrass, `dense_Atrig`), giving `circleKernelBridge : KernelBridge cT`.

Classical statements used: the heat kernel on the circle as the wrapped Gaussian (equivalently the theta
series `p_t(x,y) = Σ_n e^{-(2πn)² t} e^{2πi n (x-y)}`, Poisson summation), compare the spectral kernel (1.7.3)
of BGL Sect. 1.7; Chapman-Kolmogorov (1.3.1) of BGL Sect. 1.3 (exact here); invariance of `μ₀` (Def. 1.2.1);
characteristic function of the Gaussian (Mathlib `charFun_gaussianReal`).
-/

open MeasureTheory ProbabilityTheory AddCircle
open scoped NNReal ENNReal Real

namespace MarkovTriple.Stochastic.Circle

open MarkovTriple.BGL
open MarkovTriple.Sanity.Circle (𝕋 μ₀ trigSpan Atrig dense_Atrig Atrig_le_V V_le_A₀)
open MarkovTriple.BGL.Circle

local notation "𝒜c" => MarkovTriple.Sanity.Circle.A₀

/-- The Gaussian time-`t` law on `ℝ`: `N(0, 2t)`. -/
noncomputable abbrev heatGauss (t : ℝ≥0) : Measure ℝ := gaussianReal 0 (2 * t)

lemma measurable_coe𝕋 : Measurable (fun z : ℝ => (z : 𝕋)) :=
  (AddCircle.continuous_mk' _).measurable

/-- The **heat kernel of the circle** (wrapped Gaussian): `κ_t(x, ·) = law(x + Z mod 1)`, `Z ∼ N(0,2t)`. -/
noncomputable def circleKernel (t : ℝ≥0) : Kernel 𝕋 𝕋 where
  toFun x := (heatGauss t).map (fun z : ℝ => x + (z : 𝕋))
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
    have hmap : ∀ x : 𝕋, (heatGauss t).map (fun z : ℝ => x + (z : 𝕋)) A
        = heatGauss t (Prod.mk x ⁻¹' ((fun p : 𝕋 × ℝ => p.1 + (p.2 : 𝕋)) ⁻¹' A)) := by
      intro x
      rw [Measure.map_apply (by fun_prop) hA]
      rfl
    simp_rw [hmap]
    exact measurable_measure_prodMk_left (ν := heatGauss t)
      (measurable_fst.add (measurable_coe𝕋.comp measurable_snd) hA)

lemma circleKernel_apply (t : ℝ≥0) (x : 𝕋) :
    circleKernel t x = (heatGauss t).map (fun z : ℝ => x + (z : 𝕋)) := rfl

instance (t : ℝ≥0) : IsMarkovKernel (circleKernel t) :=
  ⟨fun x => by
    rw [circleKernel_apply]
    exact ⟨by rw [Measure.map_apply (by fun_prop) MeasurableSet.univ]; simp⟩⟩

lemma circleKernel_zero : circleKernel 0 = Kernel.id := by
  ext x : 1
  have hm : Measurable (fun z : ℝ => x + (z : 𝕋)) := by fun_prop
  rw [circleKernel_apply]
  simp only [heatGauss, mul_zero]
  rw [gaussianReal_zero_var, Kernel.id_apply]
  exact (Measure.map_dirac' hm 0).trans (by simp)

/-- **Exact Chapman-Kolmogorov** for the heat kernel of the circle. -/
theorem circleKernel_comp (s t : ℝ≥0) :
    circleKernel t ∘ₖ circleKernel s = circleKernel (s + t) := by
  ext x A hA
  rw [Kernel.comp_apply, Measure.bind_apply hA (Kernel.aemeasurable _), circleKernel_apply]
  rw [lintegral_map (Kernel.measurable_coe _ hA) (by fun_prop)]
  have hRHS : circleKernel (s + t) x A = (heatGauss s ∗ heatGauss t) ((fun c : ℝ => x + (c : 𝕋)) ⁻¹' A) := by
    rw [circleKernel_apply, Measure.map_apply (by fun_prop) hA]
    simp only [heatGauss, mul_add]
    rw [gaussianReal_conv_gaussianReal, add_zero]
  rw [hRHS, Measure.conv, Measure.map_apply measurable_add (by exact hA.preimage (by fun_prop))]
  have hm : MeasurableSet ((fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' ((fun c : ℝ => x + (c : 𝕋)) ⁻¹' A)) :=
    (hA.preimage (by fun_prop)).preimage measurable_add
  rw [Measure.prod_apply hm]
  refine lintegral_congr fun a => ?_
  rw [circleKernel_apply, Measure.map_apply (by fun_prop) hA]
  simp only [Set.preimage_preimage, AddCircle.coe_add, add_assoc]

/-- **The Haar probability measure `μ₀` is invariant** for the heat kernel. -/
theorem circleKernel_invariant (t : ℝ≥0) : μ₀.bind (circleKernel t) = μ₀ := by
  ext A hA
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  have h1 : ∀ x : 𝕋, circleKernel t x A = ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) (x + (z : 𝕋)) ∂(heatGauss t) := by
    intro x
    rw [circleKernel_apply, Measure.map_apply (by fun_prop) hA,
      ← lintegral_indicator_one (hA.preimage (by fun_prop))]
    rfl
  simp_rw [h1]
  have hmeas : Measurable fun p : 𝕋 × ℝ => A.indicator (fun _ => (1 : ℝ≥0∞)) (p.1 + (p.2 : 𝕋)) :=
    (measurable_const.indicator hA).comp
      (measurable_fst.add (measurable_coe𝕋.comp measurable_snd))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  have h2 : ∀ z : ℝ, ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) (x + (z : 𝕋)) ∂μ₀ = μ₀ A := by
    intro z
    have hpre : MeasurableSet ((fun x : 𝕋 => x + (z : 𝕋)) ⁻¹' A) := hA.preimage (by fun_prop)
    rw [show (fun x : 𝕋 => A.indicator (fun _ => (1 : ℝ≥0∞)) (x + (z : 𝕋))) =
        ((fun x : 𝕋 => x + (z : 𝕋)) ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) from by
      funext x; by_cases h : x + (z : 𝕋) ∈ A <;> simp [Set.indicator, h]]
    rw [lintegral_indicator_const hpre, one_mul]
    exact measure_preimage_add_right μ₀ (z : 𝕋) A
  simp_rw [h2]
  simp


/-! ### Fourier modes -/

/-- **Fourier mode of the heat kernel** (characteristic function of `N(0, 2t)`):
`∫ e_n(x + z) dN(0,2t)(z) = e^{-(2πn)² t} e_n(x)`. -/
theorem integral_fourier_heat (t : ℝ≥0) (n : ℤ) (x : 𝕋) :
    ∫ z : ℝ, fourier n (x + (z : 𝕋)) ∂(heatGauss t)
      = fourier n x * ((Real.exp (-lam n * t) : ℝ) : ℂ) := by
  have e1 : ∀ z : ℝ, fourier n (x + (z : 𝕋)) = fourier n x *
      Complex.exp (((2 * π * n : ℝ) : ℂ) * (z : ℂ) * Complex.I) := by
    intro z
    rw [fourier_pt_add, fourier_coe_apply]
    congr 2
    push_cast
    ring
  simp_rw [e1]
  rw [integral_const_mul, ← charFun_apply_real, charFun_gaussianReal]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  simp only [lam]
  push_cast
  ring

lemma integrable_fourier_heat (t : ℝ≥0) (n : ℤ) (x : 𝕋) :
    Integrable (fun z : ℝ => fourier n (x + (z : 𝕋))) (heatGauss t) := by
  refine Integrable.of_bound (C := 1) ?_ ?_
  · exact ((fourier n).continuous.comp (by fun_prop)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by simp

lemma integral_mc_kernel (t : ℝ≥0) (n : ℤ) (x : 𝕋) :
    ∫ y, mc n y ∂(circleKernel t x) = Real.exp (-lam n * t) * mc n x := by
  have hc : Continuous (mc n) := Complex.continuous_re.comp (fourier n).continuous
  rw [circleKernel_apply, integral_map (by fun_prop) hc.aestronglyMeasurable]
  have : ∀ z : ℝ, mc n (x + (z : 𝕋)) = (fourier n (x + (z : 𝕋))).re := fun z => rfl
  simp_rw [this]
  have h := integral_re (𝕜 := ℂ) (integrable_fourier_heat t n x)
  simp only [RCLike.re_to_complex] at h
  rw [h, integral_fourier_heat]
  rw [Complex.re_mul_ofReal, mul_comm]; rfl

lemma integral_ms_kernel (t : ℝ≥0) (n : ℤ) (x : 𝕋) :
    ∫ y, ms n y ∂(circleKernel t x) = Real.exp (-lam n * t) * ms n x := by
  have hc : Continuous (ms n) := Complex.continuous_im.comp (fourier n).continuous
  rw [circleKernel_apply, integral_map (by fun_prop) hc.aestronglyMeasurable]
  have : ∀ z : ℝ, ms n (x + (z : 𝕋)) = (fourier n (x + (z : 𝕋))).im := fun z => rfl
  simp_rw [this]
  have h := integral_im (𝕜 := ℂ) (integrable_fourier_heat t n x)
  simp only [RCLike.im_to_complex] at h
  rw [h, integral_fourier_heat]
  rw [Complex.im_mul_ofReal, mul_comm]; rfl

/-! ### Representation of the Friedrichs semigroup on `trigSpan` -/

lemma integrable_circleKernel {f : 𝕋 → ℝ} (hf : f ∈ cT.A₀) (t : ℝ≥0) (x : 𝕋) :
    Integrable f (circleKernel t x) := by
  obtain ⟨C, hC⟩ := cT.bounded f hf
  exact Integrable.of_bound (cT.measurable f hf).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)

lemma rep_mode (t : ℝ≥0) (g : 𝕋 → ℝ) (c : ℝ)
    (hgs : ∀ hL : MemLp g 2 cT.μ, cT.semigroup t (hL.toLp g) = Real.exp (-c * t) • hL.toLp g)
    (hker : ∀ x, ∫ y, g y ∂(circleKernel t x) = Real.exp (-c * t) * g x)
    (hL : MemLp g 2 cT.μ) :
    (cT.semigroup t (hL.toLp g) : 𝕋 → ℝ) =ᵐ[cT.μ] fun x => ∫ y, g y ∂(circleKernel t x) := by
  rw [hgs hL]
  filter_upwards [Lp.coeFn_smul (Real.exp (-c * t)) (hL.toLp g), hL.coeFn_toLp] with x h2 h3
  rw [h2, Pi.smul_apply, h3, smul_eq_mul, hker]

/-- **The heat kernel represents the Friedrichs semigroup on the trigonometric span.** -/
theorem circleKernel_rep_trigSpan (t : ℝ≥0) {f : 𝕋 → ℝ} (hf : f ∈ trigSpan) (hL : MemLp f 2 cT.μ) :
    (cT.semigroup t (hL.toLp f) : 𝕋 → ℝ) =ᵐ[cT.μ] fun x => ∫ y, f y ∂(circleKernel t x) := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨n, rfl⟩ | ⟨n, rfl⟩
    · exact rep_mode t (mc n) (lam n) (fun _ => semigroup_mc t n) (integral_mc_kernel t n) hL
    · exact rep_mode t (ms n) (lam n) (fun _ => semigroup_ms t n) (integral_ms_kernel t n) hL
  | zero =>
    rw [MemLp.toLp_zero, map_zero]
    filter_upwards [Lp.coeFn_zero ℝ 2 cT.μ] with x hx
    rw [hx]; simp
  | add g h hg hh ihg ihh =>
    have hgL : MemLp g 2 cT.μ := cT.memLp g (V_le_A₀ hg) 2 (by norm_num) (by norm_num)
    have hhL : MemLp h 2 cT.μ := cT.memLp h (V_le_A₀ hh) 2 (by norm_num) (by norm_num)
    have e : hL.toLp (g + h) = hgL.toLp g + hhL.toLp h := (hgL.toLp_add hhL).symm ▸ rfl
    rw [e, map_add]
    filter_upwards [Lp.coeFn_add (cT.semigroup t (hgL.toLp g)) (cT.semigroup t (hhL.toLp h)),
      ihg hgL, ihh hhL] with x h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3]
    exact (integral_add (integrable_circleKernel (V_le_A₀ hg) t x)
      (integrable_circleKernel (V_le_A₀ hh) t x)).symm
  | smul a g hg ihg =>
    have hgL : MemLp g 2 cT.μ := cT.memLp g (V_le_A₀ hg) 2 (by norm_num) (by norm_num)
    have e : hL.toLp (a • g) = a • hgL.toLp g := (hgL.toLp_const_smul a).symm ▸ rfl
    rw [e, map_smul]
    filter_upwards [Lp.coeFn_smul a (cT.semigroup t (hgL.toLp g)), ihg hgL] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    exact (integral_const_mul a _).symm

/-! ### The circle `KernelBridge` -/

/-- The heat kernels of the circle form a **Markov kernel semigroup** (exact Chapman-Kolmogorov). -/
noncomputable def circleSemigroup : SubMarkovKernelSemigroup 𝕋 where
  κ := circleKernel
  subMarkov := fun t x => (measure_univ (μ := circleKernel t x)).le
  zero := circleKernel_zero
  add := fun s t => (circleKernel_comp s t).symm

theorem circleSemigroup_isMarkov : circleSemigroup.IsMarkov :=
  fun t x => measure_univ (μ := circleKernel t x)

theorem circleSemigroup_invariant : circleSemigroup.IsInvariant cT.μ := circleKernel_invariant

/-- **The heat kernel of the circle is a full `KernelBridge`**: exact Chapman-Kolmogorov, `μ₀`
invariant, and `P_t [g] = (x ↦ ∫ g dκ_t(x,·))` `μ₀`-a.e. for **every** bounded measurable `g ∈ L²(μ₀)`
(extension from `trigSpan` by `kernelRep_of_dense`). -/
noncomputable def circleKernelBridge : KernelBridge cT where
  toSubMarkovKernelSemigroup := circleSemigroup
  rep := kernelRep_of_dense (D := (trigSpan : Set (𝕋 → ℝ))) circleKernel
    circleSemigroup.subMarkov (fun t => (circleSemigroup_invariant t).le)
    (fun f hf => cT.measurable f (V_le_A₀ hf)) (fun f hf => cT.bounded f (V_le_A₀ hf))
    (fun f hf => cT.memLp f (V_le_A₀ hf) 2 (by norm_num) (by norm_num))
    (dense_Atrig.mono (by
      rintro u ⟨f, hf, huf⟩
      exact ⟨f, Atrig_le_V hf, huf⟩))
    (fun t f hf => circleKernel_rep_trigSpan t hf _)
  invariant := circleSemigroup_invariant

theorem circleKernelBridge_κ : circleKernelBridge.κ = circleKernel := rfl

/-- The circle kernel representation in the a.e.-Chapman-Kolmogorov interface. -/
noncomputable def circleKernelRepresentation : KernelRepresentation cT :=
  circleKernelBridge.toKernelRepresentation

/-- Full circle representation: `P_t g = (x ↦ ∫ g dκ_t(x,·))` a.e. for bounded measurable `g ∈ L²`. -/
theorem circle_rep_full (t : ℝ≥0) (g : 𝕋 → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 cT.μ) :
    (cT.semigroup t (hL.toLp g) : 𝕋 → ℝ) =ᵐ[cT.μ] fun x => ∫ y, g y ∂(circleKernel t x) :=
  circleKernelBridge.rep t g hg hb hL

end MarkovTriple.Stochastic.Circle
