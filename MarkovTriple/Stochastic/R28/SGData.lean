import Mathlib
import MarkovTriple.Stochastic.FellerMeasurable
import MarkovTriple.Stochastic.RepExtend

/-!
# Round 28 (M), part 1: abstract semigroup data

The compact Feller layer of R16/R17 (`FellerKernel.lean`, `FellerMeasurable.lean`) is stated for `T : DiffusionTriple X`
but only uses the `L²(μ)` semigroup of `T` and the finite measure `T.μ`: positivity preservation, sub-Markov property,
self-adjointness, `P_0 = 1`, `P_{s+t} = P_s P_t`, strong continuity.  `SGData X` packages exactly these properties, so that
the same construction applies to a semigroup transported to another space (see `R28/Transport.lean`).  Every
`DiffusionTriple` gives one (`DiffusionTriple.toSGData`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R28

open MarkovTriple.BGL MarkovTriple.Stochastic

/-- A symmetric positivity preserving sub-Markov strongly continuous semigroup on `L²(μ)`. -/
structure SGData (X : Type*) [MeasurableSpace X] where
  /-- the reference measure -/
  μ : Measure X
  /-- the semigroup -/
  semigroup : ℝ≥0 → (Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  semigroup_zero : semigroup 0 = 1
  semigroup_add : ∀ s t, semigroup (s + t) = semigroup s * semigroup t
  continuous_semigroup_apply : ∀ u : Lp ℝ 2 μ, Continuous fun t : ℝ≥0 => semigroup t u
  semigroup_isSelfAdjoint : ∀ t, IsSelfAdjoint (semigroup t)
  semigroup_nonneg : ∀ (t : ℝ≥0) {u : Lp ℝ 2 μ}, 0 ≤ᵐ[μ] u → 0 ≤ᵐ[μ] semigroup t u
  semigroup_le_one : ∀ (t : ℝ≥0) (u : Lp ℝ 2 μ), (u : X → ℝ) ≤ᵐ[μ] (1 : X → ℝ) →
    (semigroup t u : X → ℝ) ≤ᵐ[μ] (1 : X → ℝ)
  norm_semigroup_apply_le : ∀ (t : ℝ≥0) (u : Lp ℝ 2 μ), ‖semigroup t u‖ ≤ ‖u‖

/-- the semigroup data of a `DiffusionTriple`. -/
noncomputable def _root_.MarkovTriple.BGL.DiffusionTriple.toSGData {X : Type*} [MeasurableSpace X]
    (T : DiffusionTriple X) : SGData X where
  μ := T.μ
  semigroup := T.semigroup
  semigroup_zero := T.semigroup_zero
  semigroup_add := T.semigroup_add
  continuous_semigroup_apply := T.continuous_semigroup_apply
  semigroup_isSelfAdjoint := T.semigroup_isSelfAdjoint
  semigroup_nonneg := fun t _ hu => T.semigroup_nonneg t hu
  semigroup_le_one := fun t u hu => T.semigroup_le_one t u hu
  norm_semigroup_apply_le := fun t u => T.norm_semigroup_apply_le t u

namespace SGData

variable {X : Type*} [MeasurableSpace X] (T : SGData X)

/-- the constant `1` in `L²(μ)` (finite `μ`) -/
noncomputable def one2 [IsFiniteMeasure T.μ] : Lp ℝ 2 T.μ := (memLp_const (1 : ℝ)).toLp _

lemma coeFn_one2 [IsFiniteMeasure T.μ] : (T.one2 : X → ℝ) =ᵐ[T.μ] fun _ => (1 : ℝ) := MemLp.coeFn_toLp _

variable [IsFiniteMeasure T.μ]

/-- mass is non-increasing (`P_t 1 ≤ 1`, symmetry) -/
theorem integral_semigroup_le (t : ℝ≥0) (u : Lp ℝ 2 T.μ) (hu : 0 ≤ᵐ[T.μ] u) :
    ∫ x, (T.semigroup t u : X → ℝ) x ∂T.μ ≤ ∫ x, (u : X → ℝ) x ∂T.μ := by
  have hone := T.coeFn_one2
  have hPone : (T.semigroup t T.one2 : X → ℝ) ≤ᵐ[T.μ] 1 :=
    T.semigroup_le_one t _ (hone.le)
  have hsa : IsSelfAdjoint (T.semigroup t) := T.semigroup_isSelfAdjoint t
  have hsym := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hsa) u T.one2
  have e1 : ∫ x, (T.semigroup t u : X → ℝ) x ∂T.μ = inner ℝ (T.semigroup t u) T.one2 := by
    rw [L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [hone] with x hx
    rw [hx, mul_one]
  have e2 : inner ℝ u (T.semigroup t T.one2) = ∫ x, (u : X → ℝ) x * (T.semigroup t T.one2 : X → ℝ) x ∂T.μ :=
    L2_inner_eq _ _
  have hi1 : Integrable (fun x => (u : X → ℝ) x * (T.semigroup t T.one2 : X → ℝ) x) T.μ := by
    have := MeasureTheory.L2.integrable_inner (𝕜 := ℝ) u (T.semigroup t T.one2)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp [mul_comm]
  have hi2 : Integrable (fun x => (u : X → ℝ) x) T.μ :=
    (Lp.memLp u).integrable (by norm_num)
  have hsym' : inner ℝ (T.semigroup t u) T.one2 = inner ℝ u (T.semigroup t T.one2) := hsym
  rw [e1, hsym', e2]
  refine integral_mono_ae hi1 hi2 ?_
  filter_upwards [hu, hPone] with x h1 h2
  have h1' : 0 ≤ (u : X → ℝ) x := h1
  calc (u : X → ℝ) x * (T.semigroup t T.one2 : X → ℝ) x ≤ (u : X → ℝ) x * 1 := mul_le_mul_of_nonneg_left h2 h1'
    _ = (u : X → ℝ) x := mul_one _

end SGData

end MarkovTriple.Stochastic.R28
