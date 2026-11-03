import Mathlib
import MarkovTriple.Stochastic.KernelRep
import MarkovTriple.Stochastic.Bridge
import MarkovTriple.BGL.Instances.OU.Semigroup

/-!
# Stochastic layer, part 2: the Ornstein–Uhlenbeck transition kernels

For the OU triple (`ouDiff`, reference measure `γ = N(0,1)`), the Mehler kernel
`κ_t(x, ·) = N(e^{-t} x, 1 - e^{-2t})` is an explicit family of **Markov kernels** on `ℝ`.

Fully proved here:

* `ouKernel t : Kernel ℝ ℝ`, `IsMarkovKernel`;
* **exact Chapman–Kolmogorov**: `ouKernel t ∘ₖ ouKernel s = ouKernel (s + t)` (everywhere, not only
  a.e.), and `ouKernel 0 = Kernel.id`;
* `γ` is invariant: `ouKernel t ∘ₘ γ = γ`;
* **identification with the `L²` semigroup on the test class**: for `f ∈ C_c^∞` (`OA₀`),
  `P_t [f] = (x ↦ ∫ f dκ_t(x,·))` `γ`-a.e. (from the Mehler formula `Pt_mehler`).

The representation for ALL bounded measurable `L²` functions (the field `rep` of `KernelRepresentation`) is proved in
`MarkovTriple/Stochastic/OUFull.lean` (`ou_rep_full`, `ouKernelBridge`) by `L²`-contractivity of `g ↦ κ_t g` and density of `OA₀`
(audit R15-6: this header was stale).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀
open MarkovTriple.BGL MarkovTriple.BGL.Instances.OU

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.Stochastic.OU

/-- Mehler scaling `a_t = e^{-t}`. -/
noncomputable def ouA (t : ℝ≥0) : ℝ := Real.exp (-(t : ℝ))

/-- Mehler variance `v_t = 1 - e^{-2t}` as a nonnegative real. -/
noncomputable def ouVar (t : ℝ≥0) : ℝ≥0 :=
  ⟨1 - Real.exp (-2 * (t : ℝ)), by
    have : Real.exp (-2 * (t : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [t.2])
    linarith⟩

lemma ouA_sq (t : ℝ≥0) : ouA t ^ 2 = Real.exp (-2 * (t : ℝ)) := by
  rw [ouA, ← Real.exp_nat_mul]; congr 1; push_cast; ring

lemma ouA_add (s t : ℝ≥0) : ouA (s + t) = ouA t * ouA s := by
  rw [ouA, ouA, ouA, ← Real.exp_add]; congr 1; push_cast; ring

lemma coe_ouVar (t : ℝ≥0) : (ouVar t : ℝ) = 1 - Real.exp (-2 * (t : ℝ)) := rfl

lemma ouVar_zero : ouVar 0 = 0 := by
  apply NNReal.eq; rw [coe_ouVar]; simp

lemma ouVar_add (s t : ℝ≥0) :
    ouVar (s + t) = NNReal.mk (ouA t ^ 2) (sq_nonneg _) * ouVar s + ouVar t := by
  apply NNReal.eq
  rw [NNReal.coe_add, NNReal.coe_mul, coe_ouVar, coe_ouVar, coe_ouVar,
    show ((NNReal.mk (ouA t ^ 2) (sq_nonneg _) : ℝ≥0) : ℝ) = ouA t ^ 2 from rfl, ouA_sq,
    show -2 * (((s + t : ℝ≥0)) : ℝ) = -2 * (s : ℝ) + -2 * (t : ℝ) by push_cast; ring,
    Real.exp_add]
  ring

/-- The **Mehler (OU) transition kernel**: `κ_t(x, ·) = N(e^{-t} x, 1 - e^{-2t})`. -/
noncomputable def ouKernel (t : ℝ≥0) : Kernel ℝ ℝ where
  toFun x := gaussianReal (ouA t * x) (ouVar t)
  measurable' := by
    have : Measurable (fun x : ℝ => ((ouA t * x, ouVar t) : ℝ × ℝ≥0)) := by fun_prop
    exact measurable_gaussianReal.comp this

lemma ouKernel_apply (t : ℝ≥0) (x : ℝ) :
    ouKernel t x = gaussianReal (ouA t * x) (ouVar t) := rfl

instance (t : ℝ≥0) : IsMarkovKernel (ouKernel t) :=
  ⟨fun x => by rw [ouKernel_apply]; infer_instance⟩

lemma ouKernel_zero : ouKernel 0 = Kernel.id := by
  ext x : 1
  simp [ouKernel_apply, ouVar_zero, gaussianReal_zero_var, ouA, Kernel.id_apply]

/-- Pushing a Gaussian through the Mehler kernel gives a Gaussian. -/
theorem bind_ouKernel (t : ℝ≥0) (m : ℝ) (v : ℝ≥0) :
    (gaussianReal m v).bind (ouKernel t)
      = gaussianReal (ouA t * m) (NNReal.mk (ouA t ^ 2) (sq_nonneg _) * v + ouVar t) := by
  have h1 : ∀ y, ouKernel t y = (gaussianReal 0 (ouVar t)).map (fun z => ouA t * y + z) := by
    intro y
    rw [ouKernel_apply, gaussianReal_map_const_add]; simp
  have h2 : (gaussianReal m v).bind (ouKernel t)
      = ((gaussianReal m v).map (fun y => ouA t * y)) ∗ (gaussianReal 0 (ouVar t)) := by
    ext A hA
    have hm : Measurable fun u => (gaussianReal 0 (ouVar t))
        (Prod.mk u ⁻¹' (fun p : ℝ × ℝ => p.1 + p.2) ⁻¹' A) :=
      measurable_measure_prodMk_left (measurable_add hA)
    rw [Measure.bind_apply hA (Kernel.aemeasurable _), Measure.conv,
      Measure.map_apply measurable_add hA, Measure.prod_apply (measurable_add hA),
      lintegral_map hm (by fun_prop)]
    refine lintegral_congr fun y => ?_
    rw [h1, Measure.map_apply (by fun_prop) hA]
    rfl
  rw [h2, gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal, add_zero]

/-- **Exact Chapman–Kolmogorov** for the Mehler kernels. -/
theorem ouKernel_comp (s t : ℝ≥0) : ouKernel t ∘ₖ ouKernel s = ouKernel (s + t) := by
  ext x : 1
  rw [Kernel.comp_apply, ouKernel_apply s, bind_ouKernel, ouKernel_apply, ouVar_add, ouA_add,
    mul_assoc]

/-- The Gaussian measure `γ` is invariant for the Mehler kernels. -/
theorem ouKernel_invariant (t : ℝ≥0) : γ.bind (ouKernel t) = γ := by
  rw [bind_ouKernel, mul_zero]
  congr 1
  apply NNReal.eq
  rw [NNReal.coe_add, NNReal.coe_mul, coe_ouVar,
    show ((NNReal.mk (ouA t ^ 2) (sq_nonneg _) : ℝ≥0) : ℝ) = ouA t ^ 2 from rfl, ouA_sq]
  simp

lemma gaussian_eq_map (m c : ℝ) :
    gaussianReal m (NNReal.mk (c ^ 2) (sq_nonneg _)) = γ.map (fun y => m + c * y) := by
  have : (fun y : ℝ => m + c * y) = (fun z => m + z) ∘ (fun y => c * y) := rfl
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_const_add]
  simp

/-- For `f` bounded measurable, `κ_t f(x)` is the Mehler average `∫ f(a x + c y) dγ(y)`. -/
lemma integral_ouKernel {f : ℝ → ℝ} (hf : Measurable f) (t : ℝ≥0) (x : ℝ) :
    ∫ y, f y ∂(ouKernel t x)
      = Mh (Real.exp (-(t : ℝ))) (√(1 - Real.exp (-(t : ℝ)) ^ 2)) f x := by
  have hc : (ouVar t) = NNReal.mk (√(1 - Real.exp (-(t : ℝ)) ^ 2) ^ 2) (sq_nonneg _) := by
    apply NNReal.eq
    have h0 : 0 ≤ 1 - Real.exp (-(t : ℝ)) ^ 2 := by
      have h1 : Real.exp (-(t : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
      nlinarith [Real.exp_pos (-(t : ℝ))]
    rw [NNReal.coe_mk, Real.sq_sqrt h0, coe_ouVar, ← ouA_sq]
    rfl
  rw [ouKernel_apply, hc, gaussian_eq_map, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rfl

/-- **OU kernel = `L²` semigroup on the test class**: for `f ∈ C_c^∞`,
`P_t [f] = (x ↦ ∫ f dκ_t(x,·))` `γ`-a.e. -/
theorem ouKernel_rep_OA₀ (t : ℝ≥0) {f : ℝ → ℝ} (hf : f ∈ OA₀) (u : Lp ℝ 2 ouDiff.μ)
    (hu : (u : ℝ → ℝ) =ᵐ[γ] f) :
    ((Pt t u : Lp ℝ 2 ouDiff.μ) : ℝ → ℝ) =ᵐ[γ] fun x => ∫ y, f y ∂(ouKernel t x) := by
  have hm : Measurable f := ouDiff.measurable f hf
  filter_upwards [Pt_mehler t hf u hu] with x hx
  rw [hx, integral_ouKernel hm]

/-- The OU Mehler kernels form a **Markov** kernel semigroup (exact Chapman–Kolmogorov). -/
noncomputable def ouSemigroup : SubMarkovKernelSemigroup ℝ where
  κ := ouKernel
  subMarkov := fun t x => (measure_univ (μ := ouKernel t x)).le
  zero := ouKernel_zero
  add := fun s t => (ouKernel_comp s t).symm

theorem ouSemigroup_isMarkov : ouSemigroup.IsMarkov := fun t x => measure_univ (μ := ouKernel t x)

theorem ouSemigroup_invariant : ouSemigroup.IsInvariant ouDiff.μ := ouKernel_invariant

/-- The OU Mehler kernels represent the `L²` semigroup on the test algebra (`IsTestClassRep`). -/
theorem ou_isTestClassRep : IsTestClassRep ouDiff ouKernel := by
  intro t f hf u hu
  exact ouKernel_rep_OA₀ t hf u hu

end MarkovTriple.Stochastic.OU
