import Mathlib
import MarkovTriple.Stochastic.R24.Instances
import MarkovTriple.Stochastic.OUFull

/-!
# Round 24 (C), part 10: the Ornstein-Uhlenbeck semigroup on `ℝ` is `C_0`-Feller (a NON-compact instance)

The Mehler kernel `κ_t(x, ·) = N(e^{-t} x, 1 - e^{-2t})` maps `C_c(ℝ)` into `C_0(ℝ)`:
`∫ f dκ_t(x,·) = ∫ f(z + e^{-t} x) dN(0, v)(z)` is continuous in `x` (dominated convergence) and tends to `0` as `|x| → ∞`
(`f` has compact support, `e^{-t} > 0`).  Combined with `ou_rep_full` this is `IsFellerC0 ouDiff`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.BGL.Instances.OU MarkovTriple.Sanity.OU MarkovTriple.Stochastic.OU
  MarkovTriple.Stochastic

lemma ouKernel_integral_eq (t : ℝ≥0) (f : ℝ → ℝ) (hf : Measurable f) (x : ℝ) :
    ∫ y, f y ∂(ouKernel t x) = ∫ z, f (z + ouA t * x) ∂(gaussianReal 0 (ouVar t)) := by
  have h : gaussianReal (ouA t * x) (ouVar t)
      = (gaussianReal 0 (ouVar t)).map (· + ouA t * x) := by
    rw [gaussianReal_map_add_const]; simp
  rw [ouKernel_apply, h, integral_map (measurable_add_const _).aemeasurable hf.aestronglyMeasurable]

lemma ouA_pos (t : ℝ≥0) : 0 < ouA t := Real.exp_pos _

lemma ou_tendsto_of (t : ℝ≥0) (f : C_c(ℝ, ℝ)) {C : ℝ} (hC : ∀ y, |f y| ≤ C) (l : Filter ℝ)
    [l.IsCountablyGenerated] (hl : ∀ z : ℝ, Tendsto (fun x : ℝ => z + ouA t * x) l (cocompact ℝ)) :
    Tendsto (fun x : ℝ => ∫ z, f (z + ouA t * x) ∂(gaussianReal 0 (ouVar t))) l (𝓝 0) := by
  have hz : Tendsto f (cocompact ℝ) (𝓝 0) := f.hasCompactSupport.is_zero_at_infty
  have h1 := tendsto_integral_filter_of_dominated_convergence (μ := gaussianReal 0 (ouVar t))
    (l := l) (F := fun (x : ℝ) z => f (z + ouA t * x)) (f := fun _ => (0 : ℝ))
    (fun _ => C) (Filter.Eventually.of_forall fun x => (f.continuous.comp
      (continuous_id.add continuous_const)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun z => by
      simpa [Real.norm_eq_abs] using hC _)
    (integrable_const _)
    (Filter.Eventually.of_forall fun z => by
      exact hz.comp (hl z))
  simpa using h1

/-- **`x ↦ ∫ f dκ_t(x,·)` lies in `C_0(ℝ)`** for `f ∈ C_c(ℝ)`. -/
lemma ou_C0 (t : ℝ≥0) (f : C_c(ℝ, ℝ)) : ∃ g : C₀(ℝ, ℝ), ∀ x, g x = ∫ y, f y ∂(ouKernel t x) := by
  obtain ⟨C, hC⟩ : ∃ C, ∀ y, |f y| ≤ C := by
    obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y⟩
  have hfm : Measurable f := f.continuous.measurable
  have hcont : Continuous fun x : ℝ => ∫ y, f y ∂(ouKernel t x) := by
    have e : (fun x : ℝ => ∫ y, f y ∂(ouKernel t x))
        = fun x => ∫ z, f (z + ouA t * x) ∂(gaussianReal 0 (ouVar t)) :=
      funext fun x => ouKernel_integral_eq t f hfm x
    rw [e]
    refine continuous_of_dominated (bound := fun _ => C)
      (fun x => (f.continuous.comp (continuous_id.add continuous_const)).aestronglyMeasurable)
      (fun x => Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hC _)
      (integrable_const _) (Filter.Eventually.of_forall fun z => ?_)
    exact f.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))
  refine ⟨⟨⟨fun x => ∫ y, f y ∂(ouKernel t x), hcont⟩, ?_⟩, fun x => rfl⟩
  have e : (fun x : ℝ => ∫ y, f y ∂(ouKernel t x))
      = fun x => ∫ z, f (z + ouA t * x) ∂(gaussianReal 0 (ouVar t)) :=
    funext fun x => ouKernel_integral_eq t f hfm x
  show Tendsto (fun x : ℝ => ∫ y, f y ∂(ouKernel t x)) (cocompact ℝ) (𝓝 0)
  rw [e, cocompact_eq_atBot_atTop]
  refine Tendsto.sup ?_ ?_
  · refine ou_tendsto_of t f hC atBot fun z => ?_
    rw [cocompact_eq_atBot_atTop]
    refine Tendsto.mono_right ?_ le_sup_left
    exact tendsto_atBot_add_const_left _ z (Tendsto.const_mul_atBot (ouA_pos t) tendsto_id)
  · refine ou_tendsto_of t f hC atTop fun z => ?_
    rw [cocompact_eq_atBot_atTop]
    refine Tendsto.mono_right ?_ le_sup_right
    exact tendsto_atTop_add_const_left _ z (tendsto_id.const_mul_atTop (ouA_pos t))

/-- **The OU semigroup on `ℝ` is `C_0`-Feller** (non-compact instance of the R24 theory; `γ` finite, full support). -/
theorem ou_isFellerC0 : IsFellerC0 ouDiff := by
  intro t f u hu
  obtain ⟨g, hg⟩ := ou_C0 t f
  have hb : ∃ C, ∀ x, |f x| ≤ C := by
    obtain ⟨C, hC⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
    exact ⟨C, fun y => by simpa [Real.norm_eq_abs] using hC y⟩
  have hL : MemLp f 2 ouDiff.μ := cc_memLp (T := ouDiff) f
  have e : u = hL.toLp f := Lp.ext (hu.trans hL.coeFn_toLp.symm)
  refine ⟨g, ?_⟩
  rw [e]
  filter_upwards [ou_rep_full t f f.continuous.measurable hb hL] with x hx
  rw [hg x]
  exact hx

end MarkovTriple.Stochastic.R24
