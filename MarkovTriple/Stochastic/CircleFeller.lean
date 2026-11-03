import Mathlib
import MarkovTriple.Stochastic.FellerKernel
import MarkovTriple.Stochastic.Circle
import MarkovTriple.BGL.Instances.Circle.Ergodic

/-!
# Stochastic layer, part 17: the circle is Feller; Riesz kernels = wrapped Gaussians (round 16, `STATEMENTS_R16.md` T3)

* `circleKernel_continuous`: `x ↦ ∫ f dκ_t(x,·)` is continuous for `f ∈ C(𝕋)` (dominated convergence).
* `circle_isFeller`: `P_t [f]` has the continuous representative `x ↦ ∫ f dκ_t(x,·)`
  (from the already-proved `circle_rep_full`, applied to continuous `f`).
* `circle_fellerKernel_eq`: the Feller (Riesz-Markov) kernels of the circle equal `circleKernel` **at every point**
  (weak continuity in `x` of both + `μ₀` has full support: `fellerKernel_unique`).
-/

open MeasureTheory ProbabilityTheory AddCircle

open scoped NNReal ENNReal


namespace MarkovTriple.Stochastic.Circle

open MarkovTriple.BGL MarkovTriple.BGL.Circle
open MarkovTriple.Sanity.Circle (𝕋 μ₀)

/-- Weak continuity of the wrapped Gaussian kernel in the starting point. -/
theorem circleKernel_continuous (t : ℝ≥0) (f : C(𝕋, ℝ)) :
    Continuous fun x => ∫ y, f y ∂(circleKernel t x) := by
  have h : ∀ x : 𝕋, ∫ y, f y ∂(circleKernel t x) = ∫ z : ℝ, f (x + (z : 𝕋)) ∂(heatGauss t) := by
    intro x
    rw [circleKernel_apply, integral_map (by fun_prop) f.continuous.aestronglyMeasurable]
  simp_rw [h]
  refine continuous_of_dominated (bound := fun _ => ‖f‖) ?_ ?_ ?_ ?_
  · intro x
    exact (f.continuous.comp (by fun_prop : Continuous fun z : ℝ => x + (z : 𝕋))).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall fun z => ContinuousMap.norm_coe_le_norm f _
  · exact integrable_const _
  · exact Filter.Eventually.of_forall fun z =>
      f.continuous.comp (by fun_prop : Continuous fun x : 𝕋 => x + (z : 𝕋))

instance : Measure.IsOpenPosMeasure cT.μ := inferInstanceAs (Measure.IsOpenPosMeasure μ₀)

/-- **The circle is Feller.** -/
theorem circle_isFeller : IsFeller cT := by
  intro t f
  refine ⟨⟨fun x => ∫ y, f y ∂(circleKernel t x), circleKernel_continuous t f⟩, ?_⟩
  have hL : MemLp (f : 𝕋 → ℝ) 2 cT.μ :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
  have e : hL.toLp f = clsC cT.μ f := Lp.ext (hL.coeFn_toLp.trans (coeFn_clsC f).symm)
  rw [← e]
  exact circle_rep_full t f f.continuous.measurable
    ⟨‖f‖, fun x => by simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f x⟩ hL

/-- **Riesz kernels = wrapped Gaussians, everywhere** (not only a.e.). -/
theorem circle_fellerKernel_eq (t : ℝ≥0) (x : 𝕋) :
    fellerKernel circle_isFeller t x = circleKernel t x := by
  symm
  refine fellerKernel_unique circle_isFeller t (circleKernel t) (circleKernel_continuous t) ?_ x
  intro f
  have hL : MemLp (f : 𝕋 → ℝ) 2 cT.μ :=
    MemLp.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Filter.Eventually.of_forall fun x => ContinuousMap.norm_coe_le_norm f x)
  have e : hL.toLp f = clsC cT.μ f := Lp.ext (hL.coeFn_toLp.trans (coeFn_clsC f).symm)
  rw [← e]
  exact circle_rep_full t f f.continuous.measurable
    ⟨‖f‖, fun x => by simpa [Real.norm_eq_abs] using ContinuousMap.norm_coe_le_norm f x⟩ hL

theorem circle_fellerKernel_eq' (t : ℝ≥0) : fellerKernel circle_isFeller t = circleKernel t :=
  Kernel.ext fun x => circle_fellerKernel_eq t x

/-- The Feller bridge of the circle (conservative by `semigroup_one`); its kernels are `circleKernel`. -/
noncomputable def circleFellerBridge : KernelBridge cT :=
  fellerBridge circle_isFeller (fun t => MarkovTriple.BGL.Circle.semigroup_one t)

theorem circleFellerBridge_κ : circleFellerBridge.κ = circleKernel := by
  funext t
  exact circle_fellerKernel_eq' t

end MarkovTriple.Stochastic.Circle
