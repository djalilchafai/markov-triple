import Mathlib
import MarkovTriple.Stochastic.OUFull

/-!
# Round 22 (E3), part (ii): the defining properties of a `KernelRepresentation` do not give exact CK

The Riesz kernels of R15 are only characterised by `rieszKernel_subMarkov`, `rieszKernel_continuous`
(for every `t` separately, `Classical.choose`).  This file shows that these (in fact all) properties of a
`KernelRepresentation` are insufficient for exact Chapman-Kolmogorov: on the OU triple, the Mehler
kernels modified at ONE point at ONE time form a `KernelRepresentation` with `γ.bind κ_t ≤ γ`, whose
Chapman-Kolmogorov identity fails at that point.  Hence no `MarkovProcessBridge` for the plain Riesz
kernels can be extracted from their API (the existence of *some* exact all-time kernel semigroup for an
arbitrary compact-space triple is NOT claimed or refuted).
See `STATEMENTS_R22_E3.md`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open MarkovTriple.BGL MarkovTriple.BGL.Instances.OU MarkovTriple.Sanity.OU

namespace MarkovTriple.Stochastic.R22

open MarkovTriple.Stochastic.OU MarkovTriple.Stochastic

/-- the Mehler kernel at time `2`, modified at the single point `0` -/
noncomputable def badKernel2 : Kernel ℝ ℝ :=
  ⟨fun x => if x = 0 then Measure.dirac (5 : ℝ) else ouKernel 2 x, by
    refine Measurable.ite (measurableSet_singleton 0) measurable_const (ouKernel 2).measurable⟩

lemma badKernel2_ae : (fun x => badKernel2 x) =ᵐ[γ] fun x => ouKernel 2 x := by
  have h0 : γ {0} = 0 := by
    refine gaussianReal_absolutelyContinuous 0 one_ne_zero ?_
    simp
  have : ∀ᵐ x ∂γ, x ≠ 0 := by
    rw [ae_iff]; simpa using h0
  filter_upwards [this] with x hx
  simp [badKernel2, hx]

/-- the modified family of kernels -/
noncomputable def badKappa (t : ℝ≥0) : Kernel ℝ ℝ := if t = 2 then badKernel2 else ouKernel t

lemma badKappa_of_ne {t : ℝ≥0} (h : t ≠ 2) : badKappa t = ouKernel t := by simp [badKappa, h]

lemma badKappa_two : badKappa 2 = badKernel2 := by simp [badKappa]

/-- a `KernelRepresentation` of the OU semigroup obtained from the Mehler kernels by changing one
point at one time -/
noncomputable def badRep : KernelRepresentation ouDiff where
  κ := badKappa
  subMarkov := fun t x => by
    by_cases h : t = 2
    · subst h
      rw [badKappa_two]
      by_cases hx : x = 0
      · simp [badKernel2, hx]
      · have : (badKernel2 x) = ouKernel 2 x := by simp [badKernel2, hx]
        rw [this]; exact (measure_univ (μ := ouKernel 2 x)).le
    · rw [badKappa_of_ne h]; exact (measure_univ (μ := ouKernel t x)).le
  rep := fun t g hg hb hL => by
    by_cases h : t = 2
    · subst h
      filter_upwards [ouKernelRepresentation.rep 2 g hg hb hL, badKernel2_ae] with x h1 h2
      rw [badKappa_two, h2]; exact h1
    · simp only [badKappa_of_ne h]
      exact ouKernelRepresentation.rep t g hg hb hL

theorem badRep_subInvariant (t : ℝ≥0) : ouDiff.μ.bind (badRep.κ t) ≤ ouDiff.μ := by
  by_cases h : t = 2
  · subst h
    have : ouDiff.μ.bind (badKernel2) = ouDiff.μ.bind (ouKernel 2) :=
      Measure.bind_congr_right badKernel2_ae
    show γ.bind (badKappa 2) ≤ γ
    rw [badKappa_two]
    exact (Measure.bind_congr_right badKernel2_ae).trans_le (ouKernel_invariant 2).le
  · show γ.bind (badKappa t) ≤ γ
    rw [badKappa_of_ne h]; exact (ouKernel_invariant t).le

/-- **Obstruction.**  A `KernelRepresentation` (with `μ.bind κ_t ≤ μ`) need not satisfy exact
Chapman-Kolmogorov. -/
theorem exists_kernelRepresentation_not_exact_ck :
    ∃ K : KernelRepresentation ouDiff, (∀ t, ouDiff.μ.bind (K.κ t) ≤ ouDiff.μ) ∧
      ∃ (s t : ℝ≥0) (x : ℝ), K.κ (s + t) x ≠ (K.κ t ∘ₖ K.κ s) x := by
  refine ⟨badRep, badRep_subInvariant, 1, 1, 0, ?_⟩
  have h2 : (1 : ℝ≥0) + 1 = 2 := by norm_num
  have h1 : (1 : ℝ≥0) ≠ 2 := by norm_num
  show badKappa (1 + 1) 0 ≠ (badKappa 1 ∘ₖ badKappa 1) 0
  rw [h2, badKappa_two, badKappa_of_ne h1, ouKernel_comp, h2]
  intro hne
  have e1 : badKernel2 0 = Measure.dirac (5 : ℝ) := by simp [badKernel2]
  rw [e1, ouKernel_apply] at hne
  have := congrArg (fun m : Measure ℝ => m {5}) hne
  simp only [Measure.dirac_apply_of_mem (Set.mem_singleton (5 : ℝ))] at this
  have hv : ouVar 2 ≠ 0 := by
    intro h
    have : (ouVar 2 : ℝ) = 0 := by rw [h]; rfl
    rw [coe_ouVar] at this
    have : Real.exp (-2 * ((2 : ℝ≥0) : ℝ)) < 1 := by simp
    linarith
  have h5 : gaussianReal (ouA 2 * 0) (ouVar 2) {5} = 0 :=
    gaussianReal_absolutelyContinuous _ hv (by simp)
  rw [h5] at this
  simp at this

end MarkovTriple.Stochastic.R22
