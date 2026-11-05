import Mathlib
import MarkovTriple.Stochastic.R24.Bridge
import MarkovTriple.Stochastic.R24.Exact
import MarkovTriple.Stochastic.R24.Operator
import MarkovTriple.Stochastic.R23.Lebesgue
import MarkovTriple.BGL.Instances.Lebesgue.Full

/-!
# Round 29 (O), part 1: `lebesgueFull` (the 1-d Lebesgue `FullTriple` on `ℝ`) is `C_0`-Feller and has a `MarkovProcessBridge`

Port of R25 (`lebesgueRd_isFellerC0`, `heatKernelRd`) to the one-dimensional heat operator `heatM`:

* `semigroup_cc_aux1`: `P_t u = heatM (√(2t)) f` a.e. for a compactly supported continuous `f` (symmetry of Gaussian smoothing for
  continuous bounded integrable functions, then `semigroup_eq_heat` on the test class);
* `lebesgue_isFellerC0`;
* the Feller kernels are `N(x, 2t)` at every point (`fellerKernelInf_lebesgue`), so `hM` holds;
* `lebesgueFull_bridge`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R29

open MarkovTriple.BGL MarkovTriple.BGL.Lebesgue MarkovTriple.Stochastic MarkovTriple.Stochastic.R24

variable {φ ψ : ℝ → ℝ}

lemma continuous_heatM (hc : Continuous φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (a : ℝ) :
    Continuous (heatM a φ) := by
  unfold heatM
  exact continuous_of_dominated (bound := fun _ => C)
    (fun x => (hc.comp (by fun_prop)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun z => by simpa using hC _) (integrable_const C)
    (ae_of_all _ fun z => hc.comp (by fun_prop))

lemma tendsto_heatM_cocompact (hc : Continuous φ) (hcs : HasCompactSupport φ) (a : ℝ) :
    Tendsto (heatM a φ) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  have : (cocompact ℝ).IsCountablyGenerated := by
    rw [← comap_dist_left_atTop_eq_cocompact (0 : ℝ)]; infer_instance
  have := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 1)
    (l := cocompact ℝ) (F := fun x z => φ (x - a * z)) (f := fun _ => (0 : ℝ))
    (fun _ => C)
    (Eventually.of_forall fun x => (hc.comp (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ae_of_all _ fun z => hC _) (integrable_const C)
    (ae_of_all _ fun z => hcs.is_zero_at_infty.comp
      ((Homeomorph.subRight (a * z)).isClosedEmbedding.tendsto_cocompact))
  rw [integral_zero] at this
  exact this

/-- symmetry of Gaussian smoothing for continuous bounded integrable functions (1-d port of `integral_mul_heat_comm_gen`) -/
theorem integral_mul_heatM_comm_gen (hφc : Continuous φ) (hψc : Continuous ψ) {C D : ℝ}
    (hC : ∀ x, |φ x| ≤ C) (hD : ∀ x, |ψ x| ≤ D) (hφi : Integrable φ volume)
    (hψi : Integrable ψ volume) (a : ℝ) :
    ∫ x, ψ x * heatM a φ x = ∫ x, φ x * heatM a ψ x := by
  have h1 : ∀ x, ψ x * heatM a φ x = ∫ z, ψ x * φ (x - a * z) ∂(gaussianReal 0 1) := fun x => by
    unfold heatM; rw [integral_const_mul]
  have h2 : ∀ y, φ y * heatM a ψ y = ∫ z, φ y * ψ (y + a * z) ∂(gaussianReal 0 1) := fun y => by
    unfold heatM
    rw [← integral_const_mul, ← integral_gauss_neg (fun z => φ y * ψ (y - a * z))]
    simp
  simp only [h1, h2]
  have hint1 : Integrable (Function.uncurry fun (x z : ℝ) => ψ x * φ (x - a * z))
      (volume.prod (gaussianReal 0 1)) := by
    refine Integrable.mono' ((hψi.norm.comp_fst (gaussianReal 0 1)).const_mul C)
      ((hψc.comp continuous_fst).mul (hφc.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
  have hint2 : Integrable (Function.uncurry fun (z y : ℝ) => φ y * ψ (y + a * z))
      ((gaussianReal 0 1).prod volume) := by
    refine Integrable.mono' ((hφi.norm.comp_snd (gaussianReal 0 1)).const_mul D)
      ((hφc.comp continuous_snd).mul (hψc.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
    rw [mul_comm D]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  rw [integral_integral_swap hint1, ← integral_integral_swap hint2]
  congr 1
  funext z
  have := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun x => ψ x * φ (x - a * z)) (a * z)
  simp only [add_sub_cancel_right] at this
  rw [← this]
  congr 1
  funext y
  ring

lemma inner_toLp1 {f g : ℝ → ℝ} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, f x * g x := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
  rw [h1, h2]

lemma coeFn_heatL2 {ψ : ℝ → ℝ} (hψ : IsTest ψ) (b : ℝ) :
    (heatL2 hψ b : ℝ → ℝ) =ᵐ[volume] heatM b ψ :=
  (hψ.memLp_heatM b).coeFn_toLp

theorem semigroup_cc_aux1 (t : ℝ≥0) (f : C_c(ℝ, ℝ))
    (u : Lp ℝ 2 lebesgueDiffusion.μ)
    (hu : (u : ℝ → ℝ) =ᵐ[lebesgueDiffusion.μ] f) :
    (lebesgueDiffusion.semigroup t u : ℝ → ℝ) =ᵐ[lebesgueDiffusion.μ] heatM (Real.sqrt (2 * t)) f := by
  change (u : ℝ → ℝ) =ᵐ[volume] f at hu
  change (lebesgueDiffusion.semigroup t u : ℝ → ℝ) =ᵐ[volume] _
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hC' : ∀ x, |f x| ≤ C := fun x => by simpa using hC x
  have hfi : Integrable f volume := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hL := memLp_two_heatM_gen f.continuous hfi hC' (Real.sqrt (2 * t))
  have key : lebesgueDiffusion.semigroup t u = hL.toLp _ := by
    rw [← sub_eq_zero]
    refine lebesgueDiffusion.eq_zero_of_orth _ (fun g => ?_)
    rw [inner_sub_left, sub_eq_zero]
    obtain ⟨D, -, hD⟩ := (isTest_of g.2).bdd
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      (lebesgueDiffusion.semigroup_isSelfAdjoint t) u (lebesgueDiffusion.cls g)
    refine hsym.trans ?_
    have e : lebesgueDiffusion.semigroup t (lebesgueDiffusion.cls g) =
        heatL2 (isTest_of g.2) (Real.sqrt (2 * t)) := semigroup_eq_heat g.2 t
    erw [e]
    rw [L2_inner_eq, L2_inner_eq]
    have h1 : ∀ᵐ x ∂(volume : Measure ℝ),
        (u : ℝ → ℝ) x * (heatL2 (isTest_of g.2) (Real.sqrt (2 * t)) : ℝ → ℝ) x
          = f x * heatM (Real.sqrt (2 * t)) g.1 x := by
      filter_upwards [hu, coeFn_heatL2 (isTest_of g.2) (Real.sqrt (2 * t))] with x h1 h2
      rw [h1, h2]
    have h2 : ∀ᵐ x ∂(volume : Measure ℝ),
        (hL.toLp _ : ℝ → ℝ) x * (lebesgueDiffusion.cls g : ℝ → ℝ) x
          = g.1 x * heatM (Real.sqrt (2 * t)) f x := by
      filter_upwards [hL.coeFn_toLp, lebesgueDiffusion.coeFn_cls g] with x h1 h2
      rw [h1, h2, mul_comm]; rfl
    rw [integral_congr_ae h1, integral_congr_ae h2]
    exact (integral_mul_heatM_comm_gen f.continuous (isTest_of g.2).cont hC' hD
      hfi (isTest_of g.2).integrable _).symm
  rw [key]
  exact hL.coeFn_toLp

/-- `lebesgueFull.μ` is Lebesgue measure: locally finite and of full support. -/
instance : lebesgueFull.toDiffusionTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs (volume : Measure ℝ).IsOpenPosMeasure

/-- **`(ℝ, Lebesgue)` (the 1-d `FullTriple`) is `C_0`-Feller**; the `C_0` representative of `P_t f` is `heatM (√(2t)) f`. -/
theorem lebesgue_isFellerC0 : IsFellerC0 lebesgueFull.toDiffusionTriple := by
  intro t f u hu
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hC' : ∀ x, |f x| ≤ C := fun x => by simpa using hC x
  refine ⟨⟨⟨heatM (Real.sqrt (2 * t)) f, continuous_heatM f.continuous hC' _⟩,
    tendsto_heatM_cocompact f.continuous f.hasCompactSupport _⟩, ?_⟩
  exact semigroup_cc_aux1 t f u hu

/-- **The heat kernel on `ℝ`**: `κ_t(x, ·) = N(x, 2t)`. -/
noncomputable def heatKernel1 (t : ℝ≥0) : Kernel ℝ ℝ where
  toFun x := gaussianReal x (2 * t)
  measurable' := by
    have : Measurable (fun x : ℝ => ((x, 2 * t) : ℝ × ℝ≥0)) := by fun_prop
    exact measurable_gaussianReal.comp this

lemma heatKernel1_apply (t : ℝ≥0) (x : ℝ) : heatKernel1 t x = gaussianReal x (2 * t) := rfl

instance (t : ℝ≥0) (x : ℝ) : IsProbabilityMeasure (heatKernel1 t x) := by
  rw [heatKernel1_apply]; infer_instance

instance (t : ℝ≥0) : IsMarkovKernel (heatKernel1 t) := ⟨fun _ => inferInstance⟩

lemma gaussianReal_eq_map_heat (t : ℝ≥0) (x : ℝ) :
    gaussianReal x (2 * t) = (gaussianReal 0 1).map (fun z => x + Real.sqrt (2 * t) * z) := by
  have h2 : (fun w : ℝ => x + Real.sqrt (2 * t) * w)
      = (fun w => w + x) ∘ (fun w => Real.sqrt (2 * t) * w) := by
    funext w; simp [add_comm]
  rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  congr 1
  · simp [add_comm]
  · rw [mul_one]
    ext
    show (2 * (t : ℝ)) = Real.sqrt (2 * t) ^ 2
    rw [Real.sq_sqrt (by positivity)]

theorem integral_heatKernel1 (t : ℝ≥0) (x : ℝ) (g : ℝ → ℝ) (hg : Continuous g) :
    ∫ y, g y ∂(heatKernel1 t x) = heatM (Real.sqrt (2 * t)) g x := by
  rw [heatKernel1_apply, gaussianReal_eq_map_heat,
    integral_map (by fun_prop) hg.aestronglyMeasurable]
  unfold heatM
  rw [← integral_gauss_neg (fun z => g (x - Real.sqrt (2 * t) * z))]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp [sub_eq_add_neg]

/-- **Identification, at every point**: the exact Feller kernels of `(ℝ, Lebesgue)` are `N(x, 2t)`. -/
theorem fellerKernelInf_lebesgue (t : ℝ≥0) (x : ℝ) :
    fellerKernelInf lebesgue_isFellerC0 t x = gaussianReal x (2 * t) := by
  symm
  refine fellerKernelInf_unique lebesgue_isFellerC0 t (heatKernel1 t) ?_ ?_ x
  · intro f
    have : (fun x => ∫ y, f y ∂(heatKernel1 t x)) = heatM (Real.sqrt (2 * t)) f := by
      funext x; exact integral_heatKernel1 t x f f.continuous
    rw [this]
    obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
    exact continuous_heatM f.continuous (fun x => by simpa using hC x) _
  · intro f u hu
    refine (semigroup_cc_aux1 t f u hu).trans (Eventually.of_forall fun x => ?_)
    exact (integral_heatKernel1 t x f f.continuous).symm

theorem fellerKernelInf_lebesgue_kernel (t : ℝ≥0) :
    fellerKernelInf lebesgue_isFellerC0 t = heatKernel1 t :=
  Kernel.ext fun x => fellerKernelInf_lebesgue t x

theorem lebesgue_hM (t : ℝ≥0) (x : ℝ) : fellerKernelInf lebesgue_isFellerC0 t x Set.univ = 1 := by
  rw [fellerKernelInf_lebesgue]; exact measure_univ

/-- **Brownian motion on `ℝ` as a `MarkovProcessBridge` for `lebesgueFull`** (infinite invariant measure `volume`). -/
noncomputable def lebesgueFull_bridge : MarkovProcessBridge lebesgueFull.toDiffusionTriple :=
  fellerMarkovProcessBridgeInf lebesgue_isFellerC0 lebesgue_hM

theorem lebesgueFull_bridge_kernel (t : ℝ≥0) (x : ℝ) :
    lebesgueFull_bridge.kernel t x = gaussianReal x (2 * t) :=
  fellerKernelInf_lebesgue t x

theorem lebesgueFull_bridge_isMarkov (t : ℝ≥0) (x : ℝ) : lebesgueFull_bridge.kernel t x Set.univ = 1 :=
  lebesgue_hM t x

/-- exact Chapman-Kolmogorov for the 1-d heat kernels (all `x`, `s`, `t`) -/
theorem heatKernel1_add (s t : ℝ≥0) : heatKernel1 (s + t) = heatKernel1 t ∘ₖ heatKernel1 s := by
  rw [← fellerKernelInf_lebesgue_kernel, ← fellerKernelInf_lebesgue_kernel,
    ← fellerKernelInf_lebesgue_kernel]
  exact fellerKernelInf_add _ s t

/-- invariance of Lebesgue measure under the heat kernels -/
theorem heatKernel1_bind (t : ℝ≥0) : (volume : Measure ℝ).bind (heatKernel1 t) = volume := by
  rw [← fellerKernelInf_lebesgue_kernel]
  exact fellerKernelInf_bind lebesgue_isFellerC0 lebesgue_hM t

end MarkovTriple.Stochastic.R29
