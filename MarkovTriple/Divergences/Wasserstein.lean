import Mathlib

/-!
# The quadratic Wasserstein distance `W₂`: couplings and basic properties

One definition replaces `squaredWasserstein` (cutoff-rigidity `Transport.lean`), `wasserstein2` /
`cost2` (cutoff-rigidity `Statements.lean`, `Riemann/TransportW2.lean`) and `wassersteinSq`
(cutoff-fastdiff `Cutfast/Defs.lean`):
* `Coupling μ ν` : measures on `α × α` with marginals `μ`, `ν`;
* `wassersteinSq μ ν : ℝ≥0∞` : `inf_π ∫ edist² dπ` (squared distance, may be `∞`);
* `wasserstein2 μ ν := wassersteinSq μ ν ^ (1/2)`.

Note on the cutoff-fastdiff variant: it quantifies over couplings required to be *probability*
measures; for probability `μ`, `ν` this is automatic (`Coupling.isProbabilityMeasure`), so the
definitions agree there (they may differ only for non-probability `μ`, `ν`).
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovTriple

variable {α β : Type*} [PseudoEMetricSpace α] [MeasurableSpace α]
  [PseudoEMetricSpace β] [MeasurableSpace β]

/-- A coupling of `μ` and `ν`: a measure on the product with marginals `μ` and `ν`. -/
def Coupling (μ ν : Measure α) :=
  {π : Measure (α × α) // π.map Prod.fst = μ ∧ π.map Prod.snd = ν}

/-- Squared quadratic transport cost `W₂²(μ,ν) = inf_π ∫ edist(x,y)² dπ`, with values in `[0,∞]`. -/
noncomputable def wassersteinSq (μ ν : Measure α) : ℝ≥0∞ :=
  ⨅ π : Coupling μ ν, ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val

/-- The `L²` Wasserstein distance `W₂ = (inf_π ∫ edist² dπ)^{1/2}`. -/
noncomputable def wasserstein2 (μ ν : Measure α) : ℝ≥0∞ :=
  wassersteinSq μ ν ^ (1 / 2 : ℝ)

theorem wasserstein2_sq_eq (μ ν : Measure α) : wasserstein2 μ ν ^ 2 = wassersteinSq μ ν := by
  rw [wasserstein2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- The independent product is a coupling. -/
noncomputable def productCoupling (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : Coupling μ ν :=
  ⟨μ.prod ν, by simp⟩

/-- Every coupling of a probability first marginal is a probability measure. -/
theorem Coupling.isProbabilityMeasure {μ ν : Measure α} [IsProbabilityMeasure μ]
    (π : Coupling μ ν) : IsProbabilityMeasure π.val := by
  apply (Measure.isProbabilityMeasure_map_iff (μ := π.val) measurable_fst.aemeasurable).mp
  rw [π.property.1]
  infer_instance

/-- The diagonal coupling of `μ` with itself. -/
noncomputable def Coupling.diag (μ : Measure α) : Coupling μ μ :=
  ⟨μ.map (fun x => (x, x)), by
    constructor
    · rw [Measure.map_map measurable_fst (by fun_prop)]; simp [Function.comp_def]
    · rw [Measure.map_map measurable_snd (by fun_prop)]; simp [Function.comp_def]⟩

/-- Swapping the coordinates of a coupling. -/
noncomputable def Coupling.swap {μ ν : Measure α} (π : Coupling μ ν) : Coupling ν μ :=
  ⟨π.val.map Prod.swap, by
    constructor
    · rw [Measure.map_map measurable_fst measurable_swap]
      exact π.property.2
    · rw [Measure.map_map measurable_snd measurable_swap]
      exact π.property.1⟩

theorem wassersteinSq_le_cost {μ ν : Measure α} (π : Coupling μ ν) :
    wassersteinSq μ ν ≤ ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val :=
  iInf_le _ π

theorem wasserstein2_le_cost {μ ν : Measure α} (π : Coupling μ ν) :
    wasserstein2 μ ν ≤ (∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val) ^ (1 / 2 : ℝ) :=
  ENNReal.rpow_le_rpow (wassersteinSq_le_cost π) (by norm_num)

/-- `W₂²(μ,μ) = 0`. -/
@[simp] theorem wassersteinSq_self (μ : Measure α) : wassersteinSq μ μ = 0 := by
  apply le_antisymm _ bot_le
  refine (wassersteinSq_le_cost (Coupling.diag μ)).trans ?_
  refine (lintegral_map_le _ (measurable_id.prodMk measurable_id).aemeasurable).trans ?_
  simp

@[simp] theorem wasserstein2_self (μ : Measure α) : wasserstein2 μ μ = 0 := by
  simp [wasserstein2]

/-- `W₂²` is symmetric. -/
theorem wassersteinSq_comm (μ ν : Measure α) : wassersteinSq μ ν = wassersteinSq ν μ := by
  have key : ∀ μ ν : Measure α, wassersteinSq ν μ ≤ wassersteinSq μ ν := by
    intro μ ν
    refine le_iInf fun π => ?_
    refine (wassersteinSq_le_cost π.swap).trans ?_
    refine (lintegral_map_le _ measurable_swap.aemeasurable).trans ?_
    simp only [Prod.fst_swap, Prod.snd_swap, edist_comm]
    exact le_rfl
  exact le_antisymm (key ν μ) (key μ ν)

theorem wasserstein2_comm (μ ν : Measure α) : wasserstein2 μ ν = wasserstein2 ν μ := by
  rw [wasserstein2, wasserstein2, wassersteinSq_comm]

section Dirac

variable {α : Type*} [MetricSpace α] [MeasurableSpace α] [BorelSpace α]
  [SecondCountableTopology α]

/-- A deterministic first marginal forces that coordinate to equal its atom. -/
theorem Coupling.fst_ae_eq {x : α} {ν : Measure α} (π : Coupling (Measure.dirac x) ν) :
    ∀ᵐ z ∂π.val, z.1 = x := by
  apply ae_of_ae_map (μ := π.val) (p := fun y : α => y = x) measurable_fst.aemeasurable
  rw [π.property.1]
  simp

/-- The only coupling with a Dirac first marginal is the product with the second marginal. -/
theorem Coupling.eq_dirac_prod {x : α} {ν : Measure α} [IsProbabilityMeasure ν]
    (π : Coupling (Measure.dirac x) ν) : π.val = (Measure.dirac x).prod ν := by
  have hae : (fun z : α × α => z) =ᵐ[π.val] (fun z => (x, z.2)) := by
    filter_upwards [π.fst_ae_eq] with z hz
    exact Prod.ext hz rfl
  calc
    π.val = π.val.map (fun z => z) := by simp
    _ = π.val.map (fun z => (x, z.2)) := Measure.map_congr hae
    _ = (π.val.map Prod.snd).map (Prod.mk x) := by
      rw [Measure.map_map measurable_prodMk_left measurable_snd]
      rfl
    _ = ν.map (Prod.mk x) := by rw [π.property.2]
    _ = (Measure.dirac x).prod ν := (Measure.dirac_prod x).symm

/-- Transport cost from a deterministic initial point is the second moment about that point. -/
theorem wassersteinSq_dirac (x : α) (ν : Measure α) [IsProbabilityMeasure ν] :
    wassersteinSq (Measure.dirac x) ν = ∫⁻ y, edist x y ^ 2 ∂ν := by
  have hcost (π : Coupling (Measure.dirac x) ν) :
      (∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val) = ∫⁻ y, edist x y ^ 2 ∂ν := by
    rw [π.eq_dirac_prod, Measure.dirac_prod]
    exact lintegral_map (by fun_prop) measurable_prodMk_left
  have : Nonempty (Coupling (Measure.dirac x) ν) := ⟨productCoupling _ _⟩
  unfold wassersteinSq
  simp_rw [hcost]
  simp

end Dirac

/-- Applying the same measurable map to both coordinates of a coupling. -/
noncomputable def Coupling.map {μ ν : Measure α} (π : Coupling μ ν)
    {T : α → β} (hT : Measurable T) : Coupling (μ.map T) (ν.map T) := by
  refine ⟨π.val.map (fun z => (T z.1, T z.2)), ?_, ?_⟩
  · rw [Measure.map_map measurable_fst (by fun_prop)]
    change π.val.map (T ∘ Prod.fst) = μ.map T
    rw [← Measure.map_map hT measurable_fst, π.property.1]
  · rw [Measure.map_map measurable_snd (by fun_prop)]
    change π.val.map (T ∘ Prod.snd) = ν.map T
    rw [← Measure.map_map hT measurable_snd, π.property.2]

/-- A Lipschitz map multiplies the cost of any coupling by at most `K²`. -/
theorem Coupling.map_cost_le {μ ν : Measure α} (π : Coupling μ ν)
    {T : α → β} {K : ℝ≥0} (hT : Measurable T) (hL : LipschitzWith K T) :
    (∫⁻ z, edist z.1 z.2 ^ 2 ∂(π.map hT).val) ≤
      (K : ℝ≥0∞) ^ 2 * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
  change (∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val.map (fun z => (T z.1, T z.2))) ≤ _
  refine (lintegral_map_le _ (by fun_prop)).trans ?_
  calc
    (∫⁻ z, edist (T z.1) (T z.2) ^ 2 ∂π.val) ≤
        ∫⁻ z, ((K : ℝ≥0∞) * edist z.1 z.2) ^ 2 ∂π.val :=
      lintegral_mono fun z => pow_le_pow_left' (hL.edist_le_mul z.1 z.2) 2
    _ = (K : ℝ≥0∞) ^ 2 * ∫⁻ z, edist z.1 z.2 ^ 2 ∂π.val := by
      simp only [mul_pow]
      exact lintegral_const_mul' _ _ (by simp)

/-- A Lipschitz measurable map is `K²`-Lipschitz for `W₂²`. -/
theorem wassersteinSq_map_le (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : α → β} {K : ℝ≥0}
    (hT : Measurable T) (hL : LipschitzWith K T) :
    wassersteinSq (μ.map T) (ν.map T) ≤ (K : ℝ≥0∞) ^ 2 * wassersteinSq μ ν := by
  have hneT : ((K : ℝ≥0∞) ^ 2) ≠ ⊤ := by simp
  have : Nonempty (Coupling μ ν) := ⟨productCoupling μ ν⟩
  unfold wassersteinSq
  rw [ENNReal.mul_iInf (by simp)]
  refine le_iInf fun π => ?_
  exact (wassersteinSq_le_cost (π.map hT)).trans (π.map_cost_le hT hL)

/-- Lipschitz maps are `K`-Lipschitz for `W₂`. -/
theorem wasserstein2_map_le (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {T : α → β} {K : ℝ≥0}
    (hT : Measurable T) (hL : LipschitzWith K T) :
    wasserstein2 (μ.map T) (ν.map T) ≤ (K : ℝ≥0∞) * wasserstein2 μ ν := by
  have h := wassersteinSq_map_le μ ν hT hL
  have h2 := ENNReal.rpow_le_rpow h (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at h2
  have hK : ((K : ℝ≥0∞) ^ 2) ^ (1 / 2 : ℝ) = K := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  rw [hK] at h2
  exact h2

end MarkovTriple
