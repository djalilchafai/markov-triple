import Mathlib
import MarkovTriple.BGL.Analysis.Hilbert.Resolvent
import MarkovTriple.BGL.Analysis.Hilbert.ResolventGenerator

/-!
# The generator of the Friedrichs semigroup

For `S : FormData H` (a densely defined symmetric nonnegative operator `A`), the semigroup
`P_t = e^{tL}` (`S.semigroup t`) has as generator exactly the self-adjoint operator
`S.generator = 1 - R⁻¹ = -A_F` (`A_F` the Friedrichs extension of `A`):

* `FormData.hasRightDeriv_semigroup_of_mem_range`: `t⁻¹ (P_t (R g) - R g) → R g - g`;
* `FormData.tendsto_generator_iff`: `x ∈ dom G ∧ G x = v` iff `t⁻¹ (P_t x - x) → v`.
* `FormData.generator_extends`: for `f ∈ D`, `f ∈ dom G` and `G f = -A f`.
-/

open Filter Topology Set MeasureTheory
open scoped NNReal LinearPMap

set_option linter.unusedSectionVars false

namespace MarkovTriple.Hilbert

open Cx

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- Right derivative at `0` of the semigroup in a direction `w`: `t⁻¹ ∫₀ᵗ P_s w → w`. -/
lemma tendsto_avg_semigroup (w : H) :
    Tendsto (fun t : ℝ => t⁻¹ • ∫ s in (0 : ℝ)..t, S.semigroup s.toNNReal w) (𝓝[>] 0) (𝓝 w) := by
  have hc : Continuous fun s : ℝ => S.semigroup s.toNNReal w :=
    (S.continuous_semigroup_apply w).comp continuous_real_toNNReal
  have h := (hc.integral_hasStrictDerivAt 0 0).hasDerivAt.tendsto_slope_zero_right
  have h0 : S.semigroup (0 : ℝ).toNNReal w = w := by simp [semigroup_zero S]
  simp only [zero_add, intervalIntegral.integral_same, sub_zero, h0] at h
  exact h

/-- The right derivative at `0` of `t ↦ P_t (R g)` is `R g - g`. -/
theorem hasRightDeriv_semigroup_of_mem_range (g : H) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S.semigroup t (S.R g) - S.R g))
      (𝓝[>] 0) (𝓝 (S.R g - g)) := by
  have h1 := (S.tendsto_avg_semigroup (g - S.R g)).neg
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact_mod_cast ht
  have h2 := h1.comp hcoe
  have e : -(g - S.R g) = S.R g - g := by abel
  rw [e] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply]
  rw [S.semigroup_integral g t, smul_neg]

/-- The self-adjoint generator `G = 1 - R⁻¹ = -A_F` of the semigroup. -/
noncomputable def generator : H →ₗ.[ℝ] H := resolventGenerator S.R

lemma denseRange_R : DenseRange S.R :=
  denseRange_of_injective S.R_unitOp S.R_injective

theorem generator_selfAdjoint : IsSelfAdjoint S.generator :=
  resolventGenerator_selfAdjoint S.R S.R_unitOp.selfAdjoint S.R_injective S.denseRange_R

theorem generator_isClosed : S.generator.IsClosed := S.generator_selfAdjoint.isClosed

theorem generator_dense_domain : Dense (S.generator.domain : Set H) :=
  resolventGenerator_dense_domain S.R S.R_injective S.denseRange_R

theorem mem_domain_generator_iff (x : H) : x ∈ S.generator.domain ↔ ∃ y, S.R (x - y) = x :=
  mem_domain_resolventGenerator_iff S.R S.R_injective x

theorem generator_apply_eq_iff {x : H} (hx : x ∈ S.generator.domain) (y : H) :
    S.generator ⟨x, hx⟩ = y ↔ S.R (x - y) = x :=
  resolventGenerator_apply_eq_iff S.R S.R_injective hx y

/-- `G (R g) = R g - g`. -/
theorem generator_R (g : H) :
    ∃ h : S.R g ∈ S.generator.domain, S.generator ⟨S.R g, h⟩ = S.R g - g := by
  have h : S.R g ∈ S.generator.domain := (S.mem_domain_generator_iff _).2 ⟨S.R g - g, by
    rw [show S.R g - (S.R g - g) = g by abel]⟩
  refine ⟨h, (S.generator_apply_eq_iff h _).2 ?_⟩
  rw [show S.R g - (S.R g - g) = g by abel]

/-- **The generator extends `-A`**: for `f ∈ D`, `f ∈ dom G` and `G f = -A f`. -/
theorem generator_extends (f : S.D) :
    ∃ h : (f : H) ∈ S.generator.domain, S.generator ⟨f, h⟩ = -S.A f := by
  have hf : S.R ((f : H) + S.A f) = f := S.R_resolvent ⟨f, f.2⟩
  have h : (f : H) ∈ S.generator.domain := (S.mem_domain_generator_iff _).2 ⟨-S.A f, by
    rw [show (f : H) - -S.A f = (f : H) + S.A f by abel, hf]⟩
  refine ⟨h, (S.generator_apply_eq_iff h _).2 ?_⟩
  rw [show (f : H) - -S.A f = (f : H) + S.A f by abel, hf]

/-- The semigroup commutes with `R`. -/
lemma semigroup_comm_R (t : ℝ≥0) (u : H) : S.semigroup t (S.R u) = S.R (S.semigroup t u) := by
  have h : Commute (S.semigroup t) S.R := by
    have := S.R_unitOp.commute_rcfc (hfun t) id
    rw [S.R_unitOp.rcfc_id] at this
    exact this
  exact congrArg (fun T => T u) h.eq

/-- **The semigroup has generator exactly `G`**: `x ∈ dom G` with `G x = v` iff
`t⁻¹ (P_t x - x) → v` as `t ↓ 0`. -/
theorem tendsto_generator_iff (x v : H) :
    (∃ h : x ∈ S.generator.domain, S.generator ⟨x, h⟩ = v) ↔
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S.semigroup t x - x)) (𝓝[>] 0) (𝓝 v) := by
  constructor
  · rintro ⟨h, hv⟩
    obtain ⟨y, hy⟩ := (S.mem_domain_generator_iff x).1 h
    -- `x = R (x - v)`
    have hx : x = S.R (x - v) := ((S.generator_apply_eq_iff h v).1 hv).symm
    have := S.hasRightDeriv_semigroup_of_mem_range (x - v)
    rw [← hx, show x - (x - v) = v by abel] at this
    exact this
  · intro hlim
    -- apply `R` to the difference quotients
    have h1 : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (S.semigroup t (S.R x) - S.R x))
        (𝓝[>] 0) (𝓝 (S.R v)) := by
      have := (S.R.continuous.tendsto v).comp hlim
      refine this.congr (fun t => ?_)
      simp [map_smul, map_sub, semigroup_comm_R S]
    have h2 := S.hasRightDeriv_semigroup_of_mem_range x
    have hne : (𝓝[>] (0 : ℝ≥0)).NeBot := inferInstance
    have h3 : S.R v = S.R x - x := tendsto_nhds_unique h1 h2
    have hx : S.R (x - v) = x := by
      rw [map_sub, h3]; abel
    have hdom : x ∈ S.generator.domain := (S.mem_domain_generator_iff x).2 ⟨v, hx⟩
    exact ⟨hdom, (S.generator_apply_eq_iff hdom v).2 hx⟩

end FormData

end MarkovTriple.Hilbert
