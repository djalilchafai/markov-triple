import Mathlib
import MarkovTriple.BGL.Frozen.Semigroup
import MarkovTriple.BGL.Semigroup.Markov

/-!
# Stochastic layer, part 1: kernel representations of the triple semigroup

This file is the *interface* between the (analytic) semigroup `P_t = e^{tL}` of a
`DiffusionTriple` and probability theory.  It is deliberately independent of any external
Markov-process library (Armstrong's `MarkovProcess` is **not** a dependency): everything is stated
with Mathlib's `ProbabilityTheory.Kernel`.

* `KernelRepresentation T`: a family of sub-Markov kernels `κ t : Kernel E E` realizing `P_t`
  on bounded measurable `L²(μ)` functions: `P_t [g] = (x ↦ ∫ g dκ_t(x,·))` `μ`-a.e.
  (`IsMarkovRep` = conservative case.)
* `KernelRepresentation.ck_integral`: Chapman–Kolmogorov, `μ`-a.e. and on bounded measurable
  functions, `κ_{s+t}(x,g) = ∫ κ_t(y,g) κ_s(x,dy)`; this is *derived* from the semigroup law
  `P_{s+t} = P_s P_t` (finite `μ`).
* `KernelRepresentation.ck_ae` : the same on measures, `κ_{s+t}(x,·) = (κ_t ∘ₖ κ_s)(x,·)`
  for `μ`-a.e. `x`, when the σ-algebra is countably generated.

A bridge to a `MarkovProcess`-style `SubMarkovKernelSemigroup` would instantiate
`KernelRepresentation` (see `MarkovTriple/Stochastic/Bridge.lean`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- A **sub-Markov kernel representation** of the semigroup of `T`: sub-Markov kernels `κ t`
with `P_t [g] = ∫ g dκ_t(x, ·)` `μ`-a.e., for every bounded measurable `g ∈ L²(μ)`. -/
structure KernelRepresentation (T : DiffusionTriple E) where
  /-- the transition kernels `κ_t(x, dy)` -/
  κ : ℝ≥0 → Kernel E E
  /-- each `κ_t(x, ·)` is a sub-probability measure -/
  subMarkov : ∀ t x, κ t x Set.univ ≤ 1
  /-- the kernels realize `P_t` on bounded measurable `L²` functions -/
  rep : ∀ (t : ℝ≥0) (g : E → ℝ) (_hg : Measurable g) (_hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 T.μ),
    (T.semigroup t (hL.toLp g) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(κ t x)

/-- The conservative (Markov) case: every `κ_t(x,·)` is a probability measure. -/
def KernelRepresentation.IsMarkovRep {T : DiffusionTriple E} (K : KernelRepresentation T) : Prop :=
  ∀ t x, K.κ t x Set.univ = 1

namespace KernelRepresentation

variable {T : DiffusionTriple E} (K : KernelRepresentation T)

instance (t : ℝ≥0) : IsFiniteKernel (K.κ t) :=
  ⟨⟨1, ENNReal.one_lt_top, fun x => K.subMarkov t x⟩⟩

lemma abs_integral_le {t : ℝ≥0} {g : E → ℝ} {C : ℝ} (hC : ∀ x, |g x| ≤ C) (x : E) :
    |∫ y, g y ∂(K.κ t x)| ≤ |C| := by
  have h1 : ‖∫ y, g y ∂(K.κ t x)‖ ≤ |C| * (K.κ t x).real Set.univ :=
    norm_integral_le_of_norm_le_const (C := |C|)
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using (hC y).trans (le_abs_self C))
  have h2 : (K.κ t x).real Set.univ ≤ 1 := by
    have := K.subMarkov t x
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top this
  calc |∫ y, g y ∂(K.κ t x)| ≤ |C| * (K.κ t x).real Set.univ := by simpa using h1
    _ ≤ |C| * 1 := by gcongr
    _ = |C| := mul_one _

/-- **Chapman–Kolmogorov (functional form)**: for finite `μ`, bounded measurable `g`, and
`s t : ℝ≥0`, `μ`-a.e. `κ_{s+t}(x, g) = ∫ κ_t(y, g) κ_s(x, dy)`. -/
theorem ck_integral [IsFiniteMeasure T.μ] (s t : ℝ≥0) (g : E → ℝ) (hg : Measurable g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) :
    ∀ᵐ x ∂T.μ, ∫ y, g y ∂(K.κ (s + t) x) = ∫ y, (∫ z, g z ∂(K.κ t y)) ∂(K.κ s x) := by
  obtain ⟨C, hC⟩ := hb
  have hgL : MemLp g 2 T.μ := MemLp.of_bound hg.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)
  set h : E → ℝ := fun y => ∫ z, g z ∂(K.κ t y) with hh
  have hhm : Measurable h := (hg.stronglyMeasurable.integral_kernel (κ := K.κ t)).measurable
  have hhb : ∃ C', ∀ x, |h x| ≤ C' := ⟨|C|, fun x => K.abs_integral_le hC x⟩
  have hhL : MemLp h 2 T.μ := MemLp.of_bound hhm.aestronglyMeasurable |C|
    (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using K.abs_integral_le hC x)
  have e1 : T.semigroup t (hgL.toLp g) = hhL.toLp h := by
    refine Lp.ext ?_
    filter_upwards [K.rep t g hg ⟨C, hC⟩ hgL, hhL.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  have e2 := K.rep s h hhm hhb hhL
  have e3 := K.rep (s + t) g hg ⟨C, hC⟩ hgL
  rw [DiffusionTriple.semigroup_add] at e3
  change ((T.semigroup s (T.semigroup t (hgL.toLp g)) : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] _ at e3
  rw [e1] at e3
  filter_upwards [e2, e3] with x h2 h3
  rw [← h3, h2]

lemma countable_generatePiSystem {α : Type*} {S : Set (Set α)} (hS : S.Countable) :
    (generatePiSystem S).Countable := by
  have h : generatePiSystem S ⊆ (fun F : Set (Set α) => ⋂₀ F) ''
      {F | F.Finite ∧ F ⊆ S} := by
    intro t ht
    induction ht with
    | base hs => exact ⟨{_}, ⟨Set.finite_singleton _, by simpa using hs⟩, by simp⟩
    | inter _ _ _ ih1 ih2 =>
      obtain ⟨F, ⟨hF, hFS⟩, rfl⟩ := ih1
      obtain ⟨G, ⟨hG, hGS⟩, rfl⟩ := ih2
      exact ⟨F ∪ G, ⟨hF.union hG, Set.union_subset hFS hGS⟩, by simp [Set.sInter_union]⟩
  exact ((Set.countable_ofPred_finite_subset hS).image _).mono h

/-- **Chapman–Kolmogorov (measure form)**: if the σ-algebra is countably generated and `μ` is
finite, then for `μ`-a.e. `x`, `κ_{s+t}(x, ·) = (κ_t ∘ₖ κ_s)(x, ·)`. -/
theorem ck_ae [IsFiniteMeasure T.μ] [MeasurableSpace.CountablyGenerated E] (s t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, K.κ (s + t) x = (K.κ t ∘ₖ K.κ s) x := by
  have key : ∀ A : Set E, MeasurableSet A →
      ∀ᵐ x ∂T.μ, K.κ (s + t) x A = (K.κ t ∘ₖ K.κ s) x A := by
    intro A hA
    have hb : ∃ C, ∀ x, |A.indicator (fun _ => (1 : ℝ)) x| ≤ C :=
      ⟨1, fun x => by by_cases h : x ∈ A <;> simp [h]⟩
    filter_upwards [K.ck_integral s t _ (measurable_const.indicator hA) hb] with x hx
    have hint : Integrable (A.indicator (fun _ => (1 : ℝ))) ((K.κ t ∘ₖ K.κ s) x) := by
      exact (integrable_const (1 : ℝ)).indicator hA
    rw [← Kernel.integral_comp hint] at hx
    simp only [integral_indicator hA, integral_const, smul_eq_mul, mul_one,
      Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Measure.real] at hx
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 hx
  set S := MeasurableSpace.countableGeneratingSet E with hS
  have hSc : S.Countable := MeasurableSpace.countable_countableGeneratingSet
  have hSm : ∀ A ∈ S, MeasurableSet A := fun A hA =>
    MeasurableSpace.measurableSet_countableGeneratingSet hA
  have hall : ∀ᵐ x ∂T.μ, ∀ A ∈ generatePiSystem S,
      K.κ (s + t) x A = (K.κ t ∘ₖ K.κ s) x A := by
    rw [ae_ball_iff (countable_generatePiSystem hSc)]
    exact fun A hA => key A (generatePiSystem_measurableSet hSm A hA)
  filter_upwards [hall, key Set.univ MeasurableSet.univ] with x hx hu
  exact ext_of_generate_finite (generatePiSystem S)
    (by rw [generateFrom_generatePiSystem_eq]
        exact (MeasurableSpace.generateFrom_countableGeneratingSet (α := E)).symm)
    (isPiSystem_generatePiSystem S) hx hu

end KernelRepresentation

end MarkovTriple.Stochastic
