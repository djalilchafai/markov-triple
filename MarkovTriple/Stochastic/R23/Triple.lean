import Mathlib
import MarkovTriple.Stochastic.R23.SubInv
import MarkovTriple.Stochastic.RepExtend

/-!
# Round 23 (S), part 3: `KernelRepresentation` of a `DiffusionTriple` with infinite `μ`

`T.μ` finite on compacts (e.g. Lebesgue on `ℝ`, Gibbs-type infinite measures with continuous density).  The
semigroup `P_t` is positivity preserving, `L^∞`-contractive and symmetric (`semigroup_nonneg`,
`semigroup_le_one`, `semigroup_isSelfAdjoint`; none of them uses finiteness of `T.μ`), so the kernels of
`exists_kernel_of_posContraction_locFinite_subInv` exist for each `t`; `C_c` is dense in `L²(T.μ)`, and
`kernelRep_of_dense` (R15; stated without finiteness) extends the representation to all bounded measurable
`L²` functions.  See `STATEMENTS_R23_S.md`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty

namespace MarkovTriple.Stochastic.R23

open MarkovTriple.BGL MarkovTriple.Stochastic

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

section Triple

variable (T : DiffusionTriple X) [IsFiniteMeasureOnCompacts T.μ]

lemma ncInf_exists (t : ℝ≥0) :
    ∃ κ : Kernel X X, (∀ x, κ x Set.univ ≤ 1) ∧ T.μ.bind κ ≤ T.μ ∧
      ∀ (f : C₀(X, ℝ)) (u : Lp ℝ 2 T.μ), (u : X → ℝ) =ᵐ[T.μ] f →
        (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ x) :=
  exists_kernel_of_posContraction_locFinite_subInv (T.semigroup t)
    (fun _ hu => T.semigroup_nonneg t hu) (fun u hu => T.semigroup_le_one t u hu)
    (T.semigroup_isSelfAdjoint t)

/-- The (non-compact, infinite-`μ`) Riesz kernels of the semigroup of `T`. -/
noncomputable def ncKernelInf (t : ℝ≥0) : Kernel X X := Classical.choose (ncInf_exists T t)

theorem ncKernelInf_subMarkov (t : ℝ≥0) (x : X) : ncKernelInf T t x Set.univ ≤ 1 :=
  (Classical.choose_spec (ncInf_exists T t)).1 x

theorem ncKernelInf_subInvariant (t : ℝ≥0) : T.μ.bind (ncKernelInf T t) ≤ T.μ :=
  (Classical.choose_spec (ncInf_exists T t)).2.1

theorem ncKernelInf_C0 (t : ℝ≥0) (f : C₀(X, ℝ)) (u : Lp ℝ 2 T.μ) (hu : (u : X → ℝ) =ᵐ[T.μ] f) :
    (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(ncKernelInf T t x) :=
  (Classical.choose_spec (ncInf_exists T t)).2.2 f u hu

/-- the test class: continuous functions with compact support -/
def ccSet : Set (X → ℝ) := {f | Continuous f ∧ HasCompactSupport f}

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] [BorelSpace X] [MeasurableSpace X] in
lemma ccSet_bdd {f : X → ℝ} (hf : f ∈ ccSet) : ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.2.exists_bound_of_continuous hf.1
  exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma ccSet_memLp {f : X → ℝ} (hf : f ∈ ccSet) : MemLp f 2 T.μ :=
  hf.1.memLp_of_hasCompactSupport hf.2

/-- compactly supported continuous functions are dense in `L²(μ)`, `μ` finite on compacts. -/
lemma cc_dense :
    Dense {u : Lp ℝ 2 T.μ | ∃ f ∈ (ccSet : Set (X → ℝ)), (u : X → ℝ) =ᵐ[T.μ] f} := by
  rw [Metric.dense_iff]
  intro u r hr
  obtain ⟨g, hgc, hg1, hgcont, hgL⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le
    (μ := T.μ) (p := 2) (by norm_num) (ε := ENNReal.ofReal (r / 2)) (by simpa using by positivity)
  refine ⟨hgL.toLp g, ?_, g, ⟨hgcont, hgc⟩, hgL.coeFn_toLp⟩
  rw [Metric.mem_ball, dist_comm, dist_eq_norm, Lp.norm_def]
  have e : eLpNorm (⇑(u - hgL.toLp g)) 2 T.μ = eLpNorm ((u : X → ℝ) - g) 2 T.μ := by
    refine eLpNorm_congr_ae ?_
    filter_upwards [Lp.coeFn_sub u (hgL.toLp g), hgL.coeFn_toLp] with x h1 h2
    rw [h1]; simp [h2]
  rw [e]
  have hle : eLpNorm ((u : X → ℝ) - g) 2 T.μ ≤ ENNReal.ofReal (r / 2) := hg1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  linarith

/-- **Kernel representation of the semigroup of a `DiffusionTriple` with infinite `μ`**
(finite on compacts): sub-Markov kernels representing `P_t` on all bounded measurable `L²` functions. -/
noncomputable def ncKernelRepInf : KernelRepresentation T where
  κ := ncKernelInf T
  subMarkov := ncKernelInf_subMarkov T
  rep := by
    refine kernelRep_of_dense (D := (ccSet : Set (X → ℝ))) (ncKernelInf T)
      (ncKernelInf_subMarkov T) (ncKernelInf_subInvariant T) ?_ ?_ ?_ (cc_dense T) ?_
    · intro f hf; exact hf.1.measurable
    · intro f hf; exact ccSet_bdd hf
    · intro f hf; exact ccSet_memLp T hf
    · intro t f hf
      exact ncKernelInf_C0 T t ⟨⟨f, hf.1⟩, hf.2.is_zero_at_infty⟩ _ (ccSet_memLp T hf).coeFn_toLp

theorem ncKernelRepInf_κ (t : ℝ≥0) : (ncKernelRepInf T).κ t = ncKernelInf T t := rfl

theorem ncKernelRepInf_subInvariant (t : ℝ≥0) : T.μ.bind ((ncKernelRepInf T).κ t) ≤ T.μ :=
  ncKernelInf_subInvariant T t

theorem ncKernelRepInf_C0 (t : ℝ≥0) (f : C₀(X, ℝ)) (u : Lp ℝ 2 T.μ)
    (hu : (u : X → ℝ) =ᵐ[T.μ] f) :
    (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂((ncKernelRepInf T).κ t x) :=
  ncKernelInf_C0 T t f u hu

end Triple

end MarkovTriple.Stochastic.R23
