import Mathlib
import MarkovTriple.Stochastic.R24.Exact

/-!
# Round 24 (C), part 6: joint measurability of the exact Feller kernels in `(t, x)`

For `f ∈ C_c(X)` and fixed `x`, `t ↦ Q_t f (x)` is a pointwise limit of the continuous functions
`t ↦ ⟨P_t [f], ψ_k⟩ / ∫ ψ_k` (`ψ_k` bumps at `x`; `t ↦ P_t [f]` is `L²`-continuous: BGL Sect. 1.2-1.4 strong continuity;
`Q_t f` is continuous at `x`; full support gives `∫ ψ_k dμ > 0`).  Together with the continuity of `x ↦ Q_t f (x)` this
is a Caratheodory function, hence jointly measurable; `measurable_of_integrals_cc` finishes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R23

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- bump functions at `x` inside the `k`-th basic neighbourhood -/
lemma exists_bump (x : X) (U : Set X) (hU : U ∈ 𝓝 x) :
    ∃ φ : C_c(X, ℝ), (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧ φ x = 1 ∧ ∀ y, y ∉ U → φ y = 0 := by
  obtain ⟨φ, hφ1, hφ2, hφ3, hφ4⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_singleton (x := x)) (isOpen_interior (s := U))
    (Set.singleton_subset_iff.2 (mem_interior_iff_mem_nhds.2 hU))
  refine ⟨⟨φ, hasCompactSupport_def.mpr hφ2⟩, hφ4, ?_, fun y hy => ?_⟩
  · simpa using hφ1 (Set.mem_singleton x)
  · by_contra hne
    exact hy (interior_subset (hφ3 (subset_tsupport _ hne)))

/-- for fixed `x`, `t ↦ Q_t f (x)` is measurable -/
theorem measurable_Qop_time (f : C_c(X, ℝ)) (x : X) : Measurable fun t : ℝ≥0 => Qop hF t f x := by
  obtain ⟨u, hu⟩ := (𝓝 x).exists_antitone_basis
  choose φ hφ using fun k => exists_bump x (u k) (hu.mem k)
  have hφL : ∀ k, MemLp (φ k) 2 T.μ := fun k => cc_memLp (φ k)
  have hm : ∀ k, 0 < ∫ y, φ k y ∂T.μ := fun k =>
    (φ k).continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (φ k).hasCompactSupport
      (fun y => (hφ k).1 y |>.1) (show (φ k).toContinuousMap x ≠ 0 by
        rw [show (φ k).toContinuousMap x = 1 from (hφ k).2.1]; exact one_ne_zero)
  set c : ℕ → ℝ≥0 → ℝ := fun k t => (∫ y, Qop hF t f y * φ k y ∂T.μ) / ∫ y, φ k y ∂T.μ with hc
  have hcont : ∀ k, Continuous (c k) := by
    intro k
    have e : ∀ t, ∫ y, Qop hF t f y * φ k y ∂T.μ = inner ℝ (ccL2 T (φ k)) (T.semigroup t (ccL2 T f)) := by
      intro t
      rw [l2_inner_eq]
      refine integral_congr_ae ?_
      filter_upwards [Qop_ae hF t f, coeFn_ccL2 (T := T) (φ k)] with y h1 h2
      rw [h1, h2, mul_comm]
    simp_rw [hc, e]
    exact ((continuous_const.inner (T.continuous_semigroup_apply _))).div_const _
  have hlim : ∀ t, Tendsto (fun k => c k t) atTop (𝓝 (Qop hF t f x)) := by
    intro t
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hcx : ∀ᶠ y in 𝓝 x, |Qop hF t f y - Qop hF t f x| < ε / 2 := by
      have := (Qop hF t f).continuous.continuousAt (x := x)
      have h2 := (Metric.tendsto_nhds.1 this) (ε / 2) (by positivity)
      filter_upwards [h2] with y hy
      simpa [Real.dist_eq] using hy
    have hsub := hu.eventually_subset hcx
    filter_upwards [hsub] with k hk
    have hmk := hm k
    have hQφ : Integrable (fun y => Qop hF t f y * φ k y) T.μ :=
      ((Qop hF t f).continuous.mul (φ k).continuous).integrable_of_hasCompactSupport
        ((φ k).hasCompactSupport.mul_left)
    have hint : Integrable (fun y => φ k y) T.μ :=
      (φ k).continuous.integrable_of_hasCompactSupport (φ k).hasCompactSupport
    have e1 : c k t - Qop hF t f x = (∫ y, (Qop hF t f y - Qop hF t f x) * φ k y ∂T.μ) /
        ∫ y, φ k y ∂T.μ := by
      have : ∫ y, (Qop hF t f y - Qop hF t f x) * φ k y ∂T.μ
          = ∫ y, Qop hF t f y * φ k y ∂T.μ - Qop hF t f x * ∫ y, φ k y ∂T.μ := by
        simp_rw [sub_mul]
        rw [integral_sub hQφ (hint.const_mul _), integral_const_mul]
      rw [this, hc]
      field_simp
    have hb : ‖∫ y, (Qop hF t f y - Qop hF t f x) * φ k y ∂T.μ‖ ≤ ε / 2 * ∫ y, φ k y ∂T.μ := by
      rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (hint.const_mul _) (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      by_cases hy : y ∈ u k
      · have h1 : |Qop hF t f y - Qop hF t f x| < ε / 2 := hk hy
        have h2 : |φ k y| = φ k y := abs_of_nonneg ((hφ k).1 y).1
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1.le ((hφ k).1 y).1
      · have : φ k y = 0 := (hφ k).2.2 y hy
        simp [this]
    rw [Real.dist_eq, e1, abs_div, abs_of_pos hmk]
    rw [div_lt_iff₀ hmk]
    have := hb
    rw [Real.norm_eq_abs] at this
    nlinarith
  exact measurable_of_tendsto_metrizable (fun k => (hcont k).measurable) (tendsto_pi_nhds.2 hlim)

/-- `(t, x) ↦ Q_t f (x)` is jointly measurable -/
theorem measurable_Qop_joint (f : C_c(X, ℝ)) :
    Measurable fun p : ℝ≥0 × X => Qop hF p.1 f p.2 := by
  have : TopologicalSpace.MetrizableSpace X := TopologicalSpace.metrizableSpace_of_t3_secondCountable X
  have h : Measurable (Function.uncurry fun (x : X) (t : ℝ≥0) => Qop hF t f x) :=
    measurable_uncurry_of_continuous_of_measurable (ι := X) (α := ℝ≥0) (β := ℝ)
      (u := fun (x : X) (t : ℝ≥0) => Qop hF t f x)
      (fun t => (Qop hF t f).continuous) (fun x => measurable_Qop_time hF f x)
  have e : (fun p : ℝ≥0 × X => Qop hF p.1 f p.2) =
      (Function.uncurry fun (x : X) (t : ℝ≥0) => Qop hF t f x) ∘ Prod.swap := by
    funext p; rfl
  rw [e]
  exact h.comp (measurable_swap : Measurable (Prod.swap : ℝ≥0 × X → X × ℝ≥0))

/-- **Joint measurability** of the exact Feller kernels in `(t, x)`. -/
theorem fellerKernelInf_measurable_joint :
    Measurable fun p : ℝ≥0 × X => fellerKernelInf hF p.1 p.2 := by
  refine measurable_of_integrals_cc (κ := fun p : ℝ≥0 × X => fellerKernelInf hF p.1 p.2) fun f => ?_
  simp_rw [integral_fellerKernelInf]
  exact measurable_Qop_joint hF f

end MarkovTriple.Stochastic.R24
