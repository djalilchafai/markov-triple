import Mathlib
import MarkovTriple.Stochastic.OU
import MarkovTriple.Stochastic.RepExtend
import MarkovTriple.Stochastic.MarkovProcessInterface
import MarkovTriple.BGL.Instances.LebesgueRd.Full.GaussFinite
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDefs

/-!
# Round 29 (O), part 4: the product Mehler kernels on `ℝ^d` (unconditional) and the conditional bridge for `gaussRdFull d`

`mehlerKernelRd d t (x, ·) = N(e^{-t} x, (1 - e^{-2t}) I_d) = ⊗_i ouKernel t (x_i)`.  Proved unconditionally: Markov, `κ_0 = id`, exact
Chapman-Kolmogorov, invariance of the standard Gaussian `gam d = N(0, I_d)`, joint measurability in `(t, x)`.

The bridge for `gaussRdFull d` itself needs two further facts which are NOT proved in the library (see GAPS "Round 29, Stream O"):
(i) `(gaussRdFull d).μ = gam d` (the normalised Gibbs density of `|x|²/2` is the product Gaussian: the library comment calls this "informal");
(ii) the Mehler formula `P_t [f] = κ_t f` a.e. for `f ∈ C_c^∞(ℝ^d)` for the Friedrichs semigroup of `gaussRdFull d` (`IsTestClassRep`).
`gaussRdFull_bridge_of_rep` is the bridge CONDITIONAL on (i) and (ii).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R29

open MarkovTriple.BGL MarkovTriple.BGL.LebesgueRd MarkovTriple.Stochastic MarkovTriple.Stochastic.OU

variable {d : ℕ}

/-- **The Mehler (OU) kernel on `ℝ^d`**: `κ_t(x, ·) = N(e^{-t} x, (1 - e^{-2t}) I_d)`, the image of `N(0, I_d)` under `z ↦ e^{-t} x + √(1-e^{-2t}) z`. -/
noncomputable def mehlerKernelRd (d : ℕ) (t : ℝ≥0) : Kernel (Fin d → ℝ) (Fin d → ℝ) where
  toFun x := (gam d).map (fun z => ouA t • x + Real.sqrt (ouVar t) • z)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have h : ∀ x : Fin d → ℝ, ((gam d).map (fun z => ouA t • x + Real.sqrt (ouVar t) • z)) s
        = gam d {z | ouA t • x + Real.sqrt (ouVar t) • z ∈ s} := fun x => by
      rw [Measure.map_apply (by fun_prop) hs]; rfl
    simp_rw [h]
    exact measurable_measure_prodMk_left (ν := gam d)
      (s := {p : (Fin d → ℝ) × (Fin d → ℝ) | ouA t • p.1 + Real.sqrt (ouVar t) • p.2 ∈ s})
      (hs.preimage (by fun_prop))

lemma mehlerKernelRd_apply (t : ℝ≥0) (x : Fin d → ℝ) :
    mehlerKernelRd d t x = (gam d).map (fun z => ouA t • x + Real.sqrt (ouVar t) • z) := rfl

instance (t : ℝ≥0) (x : Fin d → ℝ) : IsProbabilityMeasure (mehlerKernelRd d t x) := by
  rw [mehlerKernelRd_apply]; infer_instance

instance (t : ℝ≥0) : IsMarkovKernel (mehlerKernelRd d t) := ⟨fun _ => inferInstance⟩

/-- `κ_t(x, ·) = ⊗_i N(e^{-t} x_i, 1 - e^{-2t})` -/
theorem mehlerKernelRd_apply_pi (t : ℝ≥0) (x : Fin d → ℝ) :
    mehlerKernelRd d t x = Measure.pi (fun i => ouKernel t (x i)) := by
  rw [mehlerKernelRd_apply]
  have h1 : (fun z : Fin d → ℝ => ouA t • x + Real.sqrt (ouVar t) • z)
      = fun z i => (fun (i : Fin d) (w : ℝ) => ouA t * x i + Real.sqrt (ouVar t) * w) i (z i) := by
    funext z i; simp
  have h0 := Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal 0 1)
    (f := fun (i : Fin d) (w : ℝ) => ouA t * x i + Real.sqrt (ouVar t) * w) (fun i => by fun_prop)
  rw [h1, gam, h0]
  congr 1
  funext i
  have h2 : (fun w : ℝ => ouA t * x i + Real.sqrt (ouVar t) * w)
      = (fun w => w + ouA t * x i) ∘ (fun w => Real.sqrt (ouVar t) * w) := by
    funext w; simp [add_comm]
  rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const, ouKernel_apply]
  congr 1
  · simp
  · rw [mul_one]
    ext
    show Real.sqrt (ouVar t) ^ 2 = ouVar t
    exact Real.sq_sqrt (ouVar t).2

theorem mehlerKernelRd_zero : mehlerKernelRd d 0 = Kernel.id := by
  refine Kernel.ext fun x => ?_
  rw [mehlerKernelRd_apply, ouVar_zero]
  simp [ouA, Measure.map_const, Kernel.id_apply]

/-- the product of a box under the Mehler kernel -/
lemma mehlerKernelRd_pi (t : ℝ≥0) (x : Fin d → ℝ) (B : Fin d → Set ℝ) :
    mehlerKernelRd d t x (Set.univ.pi B) = ∏ i, ouKernel t (x i) (B i) := by
  rw [mehlerKernelRd_apply_pi, Measure.pi_pi]

/-- **Exact Chapman-Kolmogorov** for the Mehler kernels on `ℝ^d` (all `x`, `s`, `t`). -/
theorem mehlerKernelRd_add (s t : ℝ≥0) :
    mehlerKernelRd d (s + t) = (mehlerKernelRd d t).comp (mehlerKernelRd d s) := by
  refine Kernel.ext fun x => ?_
  rw [mehlerKernelRd_apply_pi (s + t) x]
  refine (Measure.pi_eq fun B hB => ?_)
  have hm : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  rw [Kernel.comp_apply' _ _ _ hm]
  simp_rw [mehlerKernelRd_pi]
  -- convert to real integrals
  have hF : ∀ i, Measurable fun y : ℝ => (ouKernel t y (B i)).toReal := fun i =>
    (Kernel.measurable_coe _ (hB i)).ennreal_toReal
  have hbd : ∀ i, ∀ y, ‖(ouKernel t y (B i)).toReal‖ ≤ 1 := fun i y => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using prob_le_one (μ := ouKernel t y) (s := B i))
  have hint : ∀ i, Integrable (fun y : ℝ => (ouKernel t y (B i)).toReal) (ouKernel s (x i)) := fun i =>
    Integrable.of_bound (hF i).aestronglyMeasurable 1 (ae_of_all _ (hbd i))
  have e1 : ∫⁻ y, ∏ i, ouKernel t (y i) (B i) ∂(mehlerKernelRd d s x)
      = ENNReal.ofReal (∫ y, ∏ i, (ouKernel t (y i) (B i)).toReal ∂(mehlerKernelRd d s x)) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
      exact Finset.prod_congr rfl fun i _ => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    · refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun y => ?_)
      · exact (Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
        exact Finset.prod_le_one₀ (fun i _ => ENNReal.toReal_nonneg) (fun i _ => by
          simpa [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hbd i (y i))
    · exact ae_of_all _ fun y => Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg
  rw [e1, mehlerKernelRd_apply_pi s x, integral_fintype_prod_eq_prod (f := fun i y => (ouKernel t y (B i)).toReal),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun y => ENNReal.toReal_nonneg)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h3 : ENNReal.ofReal (∫ y, (ouKernel t y (B i)).toReal ∂(ouKernel s (x i)))
      = ∫⁻ y, ouKernel t y (B i) ∂(ouKernel s (x i)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint i) (ae_of_all _ fun y => ENNReal.toReal_nonneg)]
    exact lintegral_congr fun y => ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [h3, ← Kernel.comp_apply' _ _ _ (hB i), ouKernel_comp]

/-- the standard Gaussian `N(0, I_d)` is invariant for the Mehler kernels -/
theorem mehlerKernelRd_bind (t : ℝ≥0) : (gam d).bind (mehlerKernelRd d t) = gam d := by
  symm
  show Measure.pi (fun _ : Fin d => gaussianReal 0 1) = _
  refine (Measure.pi_eq fun B hB => ?_)
  have hm : MeasurableSet (Set.univ.pi B) := MeasurableSet.univ_pi hB
  rw [Measure.bind_apply hm (Kernel.aemeasurable _)]
  simp_rw [mehlerKernelRd_pi]
  have hF : ∀ i, Measurable fun y : ℝ => (ouKernel t y (B i)).toReal := fun i =>
    (Kernel.measurable_coe _ (hB i)).ennreal_toReal
  have hbd : ∀ i, ∀ y, ‖(ouKernel t y (B i)).toReal‖ ≤ 1 := fun i y => by
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by simpa using prob_le_one (μ := ouKernel t y) (s := B i))
  have hint : ∀ i, Integrable (fun y : ℝ => (ouKernel t y (B i)).toReal) (gaussianReal 0 1) := fun i =>
    Integrable.of_bound (hF i).aestronglyMeasurable 1 (ae_of_all _ (hbd i))
  have e1 : ∫⁻ y, ∏ i, ouKernel t (y i) (B i) ∂(gam d)
      = ENNReal.ofReal (∫ y, ∏ i, (ouKernel t (y i) (B i)).toReal ∂(gam d)) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · refine lintegral_congr fun y => ?_
      rw [ENNReal.ofReal_prod_of_nonneg (fun i _ => ENNReal.toReal_nonneg)]
      exact Finset.prod_congr rfl fun i _ => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    · refine Integrable.of_bound (C := 1) ?_ (ae_of_all _ fun y => ?_)
      · exact (Finset.measurable_prod _ fun i _ => (hF i).comp (measurable_pi_apply i)).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg)]
        exact Finset.prod_le_one₀ (fun i _ => ENNReal.toReal_nonneg) (fun i _ => by
          simpa [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] using hbd i (y i))
    · exact ae_of_all _ fun y => Finset.prod_nonneg fun i _ => ENNReal.toReal_nonneg
  rw [e1, gam, integral_fintype_prod_eq_prod (f := fun i y => (ouKernel t y (B i)).toReal),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg fun y => ENNReal.toReal_nonneg)]
  refine Finset.prod_congr rfl fun i _ => ?_
  have h3 : ENNReal.ofReal (∫ y, (ouKernel t y (B i)).toReal ∂(gaussianReal 0 1))
      = ∫⁻ y, ouKernel t y (B i) ∂(gaussianReal 0 1) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hint i) (ae_of_all _ fun y => ENNReal.toReal_nonneg)]
    exact lintegral_congr fun y => ENNReal.ofReal_toReal (measure_ne_top _ _)
  rw [h3, ← Measure.bind_apply (hB i) (Kernel.aemeasurable _)]
  have := ouKernel_invariant t
  exact congrFun (congrArg DFunLike.coe this) (B i)

/-- joint measurability of the Mehler kernels in `(t, x)` -/
theorem mehlerKernelRd_measurable_joint :
    Measurable fun p : ℝ≥0 × (Fin d → ℝ) => mehlerKernelRd d p.1 p.2 := by
  have hvar : Measurable ouVar := by
    have : ouVar = fun t : ℝ≥0 => (1 - Real.exp (-2 * (t : ℝ))).toNNReal := by
      funext t
      apply NNReal.eq
      rw [coe_ouVar, Real.coe_toNNReal _ (by rw [← coe_ouVar]; exact NNReal.coe_nonneg _)]
    rw [this]
    exact measurable_real_toNNReal.comp (by fun_prop)
  have hA : Measurable ouA := by unfold ouA; fun_prop
  have hs : Measurable fun t : ℝ≥0 => Real.sqrt (ouVar t) :=
    (measurable_coe_nnreal_real.comp hvar).sqrt
  refine Measure.measurable_of_measurable_coe _ fun A hA' => ?_
  have hφ : Measurable fun q : (ℝ≥0 × (Fin d → ℝ)) × (Fin d → ℝ) =>
      ouA q.1.1 • q.1.2 + Real.sqrt (ouVar q.1.1) • q.2 :=
    (((hA.comp (measurable_fst.comp measurable_fst)).smul (measurable_snd.comp measurable_fst))).add
      ((hs.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have h : ∀ p : ℝ≥0 × (Fin d → ℝ), mehlerKernelRd d p.1 p.2 A
      = gam d (Prod.mk p ⁻¹' ((fun q : (ℝ≥0 × (Fin d → ℝ)) × (Fin d → ℝ) =>
        ouA q.1.1 • q.1.2 + Real.sqrt (ouVar q.1.1) • q.2) ⁻¹' A)) := fun p => by
    rw [mehlerKernelRd_apply, Measure.map_apply (by fun_prop) hA']
    rfl
  simp_rw [h]
  exact Kernel.measurable_kernel_prodMk_left (κ := (Kernel.const (ℝ≥0 × (Fin d → ℝ)) (gam d)))
    (hφ hA')

/-- the Mehler kernels as a Markov kernel semigroup (exact Chapman-Kolmogorov, `κ_0 = id`) -/
noncomputable def mehlerSemigroup (d : ℕ) : SubMarkovKernelSemigroup (Fin d → ℝ) where
  κ := mehlerKernelRd d
  subMarkov := fun t x => (measure_univ (μ := mehlerKernelRd d t x)).le
  zero := mehlerKernelRd_zero
  add := fun s t => mehlerKernelRd_add s t

theorem mehlerSemigroup_isMarkov : (mehlerSemigroup d).IsMarkov := fun t x =>
  measure_univ (μ := mehlerKernelRd d t x)

/-- **Conditional bridge for `gaussRdFull d`**: if the reference measure is the product Gaussian and the Mehler kernels represent the
Friedrichs semigroup on `𝒜₀`, then `gaussRdFull d` has a `MarkovProcessBridge` (kernels = product Mehler kernels). -/
noncomputable def gaussRdFull_bridge_of_rep (hμ : (gaussRdFull d).toDiffusionTriple.μ = gam d)
    (hrep : IsTestClassRep (gaussRdFull d).toDiffusionTriple (mehlerKernelRd d)) :
    MarkovProcessBridge (gaussRdFull d).toDiffusionTriple :=
  (KernelBridge.ofTestClass (T := (gaussRdFull d).toDiffusionTriple) (mehlerSemigroup d)
    (fun t => by rw [hμ]; exact mehlerKernelRd_bind t) hrep).toMarkovProcessBridge
    mehlerKernelRd_measurable_joint

end MarkovTriple.Stochastic.R29
