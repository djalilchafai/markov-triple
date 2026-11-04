import Mathlib
import MarkovTriple.Stochastic.FellerKernel
import MarkovTriple.Stochastic.R24.Exact

/-!
# Round 24 (C), part 8: what an exact all-time semigroup needs (compact triples, and the `C_0` analogue)

R22-E3-2 (`R22.exists_kernelRepresentation_not_exact_ck`): a `KernelRepresentation` with `μ.bind κ_t ≤ μ` need NOT satisfy
exact Chapman-Kolmogorov.  The additional hypothesis which makes exact CK provable is weak-Feller continuity of the
kernels, equivalently (full-support `μ`) the Feller property of `P_t`:

* `isFeller_iff_exists_continuous_kernel` (compact `X`, finite full-support `μ`):
  `IsFeller T ↔ ∃ κ` sub-Markov kernels, `x ↦ ∫ f dκ_t(x,·)` continuous for each `f ∈ C(X)`, representing `P_t` on `C(X)`;
* `weakFeller_kernel_unique`: two such families coincide at every point (so the family is determined by `P_t`);
* `weakFeller_zero`, `weakFeller_add`: every such family satisfies `κ_0 = id` and `κ_{s+t} = κ_t ∘ₖ κ_s` EXACTLY;
* `isFellerC0_iff_exists_C0_kernel` (locally compact `X`, `μ` finite on compacts, full support): the `C_0` analogue.

No claim is made that a non-Feller `P_t` has no exact all-time kernel semigroup (neither proved nor refuted).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.Stochastic

section CompactCase

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] {T : DiffusionTriple X} [IsFiniteMeasure T.μ]
  [T.μ.IsOpenPosMeasure]

omit [T.μ.IsOpenPosMeasure] in
/-- weak-Feller kernel families: sub-Markov, weakly continuous in `x`, representing `P_t` on `C(X)` a.e. -/
def IsWeakFellerRep (κ : ℝ≥0 → Kernel X X) : Prop :=
  (∀ t x, κ t x Set.univ ≤ 1) ∧
  (∀ (t : ℝ≥0) (f : C(X, ℝ)), Continuous fun x => ∫ y, f y ∂(κ t x)) ∧
  (∀ (t : ℝ≥0) (f : C(X, ℝ)),
    (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ t x))

/-- **Feller ⇔ existence of a weakly continuous kernel representation** (compact `X`, full support). -/
theorem isFeller_iff_exists_continuous_kernel :
    IsFeller T ↔ ∃ κ : ℝ≥0 → Kernel X X, (∀ t x, κ t x Set.univ ≤ 1) ∧
      (∀ (t : ℝ≥0) (f : C(X, ℝ)), Continuous fun x => ∫ y, f y ∂(κ t x)) ∧
      (∀ (t : ℝ≥0) (f : C(X, ℝ)),
        (T.semigroup t (clsC T.μ f) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ t x)) := by
  constructor
  · intro hF
    refine ⟨fellerKernel hF, fellerKernel_subMarkov hF, fun t f => ?_, fun t f => ?_⟩
    · simp_rw [integral_fellerKernel]
      exact (fellerOp hF t f).continuous
    · simp_rw [integral_fellerKernel]
      exact fellerOp_ae hF t f
  · rintro ⟨κ, -, hc, hr⟩ t f
    exact ⟨⟨fun x => ∫ y, f y ∂(κ t x), hc t f⟩, hr t f⟩

/-- **Uniqueness at every point** of weak-Feller kernel families. -/
theorem weakFeller_kernel_unique {κ κ' : ℝ≥0 → Kernel X X} (h : IsWeakFellerRep (T := T) κ)
    (h' : IsWeakFellerRep (T := T) κ') (t : ℝ≥0) (x : X) : κ t x = κ' t x := by
  have hF : IsFeller T := isFeller_iff_exists_continuous_kernel.2 ⟨κ, h.1, h.2.1, h.2.2⟩
  have fin : ∀ s y, IsFiniteMeasure (κ s y) := fun s y => ⟨lt_of_le_of_lt (h.1 s y) ENNReal.one_lt_top⟩
  have fin' : ∀ s y, IsFiniteMeasure (κ' s y) := fun s y => ⟨lt_of_le_of_lt (h'.1 s y) ENNReal.one_lt_top⟩
  rw [fellerKernel_unique hF t (κ t) (h.2.1 t) (h.2.2 t) x,
    fellerKernel_unique hF t (κ' t) (h'.2.1 t) (h'.2.2 t) x]

/-- every weak-Feller kernel family has `κ_0 = id` exactly -/
theorem weakFeller_zero {κ : ℝ≥0 → Kernel X X} (h : IsWeakFellerRep (T := T) κ) : κ 0 = Kernel.id := by
  have hF : IsFeller T := isFeller_iff_exists_continuous_kernel.2 ⟨κ, h.1, h.2.1, h.2.2⟩
  ext x : 1
  have fin : ∀ s y, IsFiniteMeasure (κ s y) := fun s y => ⟨lt_of_le_of_lt (h.1 s y) ENNReal.one_lt_top⟩
  rw [fellerKernel_unique hF 0 (κ 0) (h.2.1 0) (h.2.2 0) x]
  rw [fellerKernel_zero hF]

/-- **Exact Chapman-Kolmogorov for every weak-Feller kernel family** (all `s, t`, all `x`). -/
theorem weakFeller_add {κ : ℝ≥0 → Kernel X X} (h : IsWeakFellerRep (T := T) κ) (s t : ℝ≥0) :
    κ (s + t) = κ t ∘ₖ κ s := by
  have hF : IsFeller T := isFeller_iff_exists_continuous_kernel.2 ⟨κ, h.1, h.2.1, h.2.2⟩
  have hκ : ∀ u, κ u = fellerKernel hF u := fun u => by
    ext x : 1
    have fin : ∀ s y, IsFiniteMeasure (κ s y) := fun s y => ⟨lt_of_le_of_lt (h.1 s y) ENNReal.one_lt_top⟩
    exact fellerKernel_unique hF u (κ u) (h.2.1 u) (h.2.2 u) x
  rw [hκ (s + t), hκ t, hκ s]
  exact fellerKernel_add hF s t

end CompactCase

section C0Case

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]

/-- **`C_0`-Feller ⇔ existence of a kernel family sending `C_c` to `C_0` and representing `P_t`** (full support). -/
theorem isFellerC0_iff_exists_C0_kernel :
    IsFellerC0 T ↔ ∃ κ : ℝ≥0 → Kernel X X,
      (∀ t x, κ t x Set.univ ≤ 1) ∧
      (∀ (t : ℝ≥0) (f : C_c(X, ℝ)), ∃ g : C₀(X, ℝ), ∀ x, g x = ∫ y, f y ∂(κ t x)) ∧
      (∀ (t : ℝ≥0) (f : C_c(X, ℝ)) (u : Lp ℝ 2 T.μ), (u : X → ℝ) =ᵐ[T.μ] f →
        (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ t x)) := by
  constructor
  · intro hF
    refine ⟨fellerKernelInf hF, fellerKernelInf_subMarkov hF, fun t f => ⟨Qop hF t f, fun x =>
      (integral_fellerKernelInf hF t x f).symm⟩, fun t f u hu => ?_⟩
    obtain ⟨g, hg, hae⟩ := fellerKernelInf_integral_cc hF t f u hu
    refine hae.trans (Filter.Eventually.of_forall fun x => ?_)
    exact hg x
  · rintro ⟨κ, -, hC0, hr⟩ t f u hu
    obtain ⟨g, hg⟩ := hC0 t f
    refine ⟨g, (hr t f u hu).trans (Filter.Eventually.of_forall fun x => (hg x).symm)⟩

end C0Case

end MarkovTriple.Stochastic.R24
