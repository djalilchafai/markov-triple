import Mathlib
import MarkovTriple.Stochastic.RepExtend
import MarkovTriple.Stochastic.RieszRep

/-!
# Stochastic layer, part 19: Feller-free exact Chapman-Kolmogorov on a conull set (round 17, `STATEMENTS_R17.md` (B))

A `KernelRepresentation` of a symmetric Markov semigroup satisfies Chapman-Kolmogorov only `μ`-a.e.
(`KernelRepresentation.ck_ae`, BGL Sect. 1.2: the kernel is determined by `P_t` only up to `μ`-null sets of
starting points).  For a **countable** set `S` of times, the a.e. statements can be made *exact* by removing a
null set of starting points, provided the removed set is "properly exceptional" (`κ_s(x, ·)` does not charge it for
the remaining `x` and `s ∈ S`).  This is the discrete-time form of Fukushima's regularisation, and it uses exactly
BGL's symmetry/sub-invariance: `μ.bind κ_s ≤ μ`.

* `ae_measure_eq_of_forall`: two measure-valued maps agreeing on each measurable set a.e. agree a.e. (countably generated).
* `KernelRepresentation.kappa_zero_ae`: `κ_0(x, ·) = δ_x` for `μ`-a.e. `x` (from `P_0 = id`).
* `KernelRepresentation.exists_exact_ck`: for countable `S ⊆ ℝ≥0` there is a measurable conull `G` which is
  `κ_s`-closed (`κ_s(x, Gᶜ) = 0` for `x ∈ G`, `s ∈ S`), and on which `κ_{s+t}(x,·) = (κ_t ∘ₖ κ_s)(x,·)` for all
  `s, t ∈ S` and `κ_0(x, ·) = δ_x`.
* `rieszKernel_exists_exact_ck`: the corollary for the Riesz kernels of any triple on a compact metrizable space.

What is **not** obtained (no overclaim): a statement for *all* real times simultaneously (this is the content of the
Feller property in `FellerKernel.lean`; without it one would need pathwise right-continuity in `t`, which `L²`-strong
continuity does not give), nor a `KernelBridge` / `MarkovProcessBridge` (they require all `s, t` and all `x`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic

open MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- Two families of finite measures which agree on every measurable set `μ`-a.e. agree `μ`-a.e. as measures,
when the σ-algebra is countably generated. -/
lemma ae_measure_eq_of_forall [MeasurableSpace.CountablyGenerated E] {μ : Measure E}
    {m₁ m₂ : E → Measure E} [∀ x, IsFiniteMeasure (m₁ x)] [∀ x, IsFiniteMeasure (m₂ x)]
    (h : ∀ A : Set E, MeasurableSet A → ∀ᵐ x ∂μ, m₁ x A = m₂ x A) : ∀ᵐ x ∂μ, m₁ x = m₂ x := by
  set S := MeasurableSpace.countableGeneratingSet E with hS
  have hSc : S.Countable := MeasurableSpace.countable_countableGeneratingSet
  have hSm : ∀ A ∈ S, MeasurableSet A := fun A hA =>
    MeasurableSpace.measurableSet_countableGeneratingSet hA
  have hall : ∀ᵐ x ∂μ, ∀ A ∈ generatePiSystem S, m₁ x A = m₂ x A := by
    rw [ae_ball_iff (KernelRepresentation.countable_generatePiSystem hSc)]
    exact fun A hA => h A (generatePiSystem_measurableSet hSm A hA)
  filter_upwards [hall, h Set.univ MeasurableSet.univ] with x hx hu
  exact ext_of_generate_finite (generatePiSystem S)
    (by rw [generateFrom_generatePiSystem_eq]
        exact (MeasurableSpace.generateFrom_countableGeneratingSet (α := E)).symm)
    (isPiSystem_generatePiSystem S) hx hu

namespace KernelRepresentation

variable {T : DiffusionTriple E} [IsFiniteMeasure T.μ] (K : KernelRepresentation T)

/-- `κ_0(x, ·) = δ_x` for `μ`-a.e. `x` (from `P_0 = id`). -/
theorem kappa_zero_ae [MeasurableSpace.CountablyGenerated E] :
    ∀ᵐ x ∂T.μ, K.κ 0 x = Measure.dirac x := by
  have : ∀ x, IsFiniteMeasure (K.κ 0 x) := fun x =>
    ⟨lt_of_le_of_lt (K.subMarkov 0 x) ENNReal.one_lt_top⟩
  refine ae_measure_eq_of_forall (m₂ := fun x => Measure.dirac x) fun A hA => ?_
  have hgm : Measurable (A.indicator (fun _ => (1 : ℝ))) := measurable_const.indicator hA
  have hb : ∃ C, ∀ x, |A.indicator (fun _ => (1 : ℝ)) x| ≤ C :=
    ⟨1, fun x => by by_cases h : x ∈ A <;> simp [h]⟩
  have hL : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 T.μ := MemLp.of_bound hgm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by by_cases h : x ∈ A <;> simp [h])
  have e : T.semigroup 0 (hL.toLp _) = hL.toLp _ := by
    rw [DiffusionTriple.semigroup_zero]; rfl
  have hr := K.rep 0 _ hgm hb hL
  rw [e] at hr
  filter_upwards [hr, hL.coeFn_toLp] with x h1 h2
  have h3 : ∫ y, A.indicator (fun _ => (1 : ℝ)) y ∂(K.κ 0 x) = (K.κ 0 x).real A := by
    rw [integral_indicator hA]; simp
  rw [h3] at h1
  have h4 := h1.symm.trans h2
  rw [Measure.dirac_apply' _ hA]
  by_cases hx : x ∈ A
  · simp only [hx, Set.indicator_of_mem] at h4 ⊢
    simp only [Measure.real] at h4
    simpa using (ENNReal.toReal_eq_one_iff _).1 h4
  · simp only [hx, Set.indicator_of_notMem, not_false_eq_true] at h4 ⊢
    simp only [Measure.real] at h4
    rcases (ENNReal.toReal_eq_zero_iff _).1 h4 with h | h
    · simpa using h
    · exact absurd h (measure_ne_top _ _)

/-- One step of the construction: shrink a measurable conull set `G` so that the remaining points have
`κ_s(x, Gᶜ) = 0` for `s ∈ S`. -/
def shrink (S : Set ℝ≥0) (G : Set E) : Set E := G ∩ {x | ∀ s ∈ S, K.κ s x Gᶜ = 0}

omit [IsFiniteMeasure T.μ] in
lemma measurableSet_shrink (S : Set ℝ≥0) (hS : S.Countable) {G : Set E} (hG : MeasurableSet G) :
    MeasurableSet (K.shrink S G) := by
  refine hG.inter ?_
  have : {x | ∀ s ∈ S, K.κ s x Gᶜ = 0} = ⋂ s ∈ S, {x | K.κ s x Gᶜ = 0} := by
    ext x; simp
  rw [this]
  exact MeasurableSet.biInter hS fun s _ =>
    (Kernel.measurable_coe (K.κ s) hG.compl) (measurableSet_singleton 0)

omit [IsFiniteMeasure T.μ] in
lemma measure_shrink_compl (S : Set ℝ≥0) (hS : S.Countable)
    (hbind : ∀ t, T.μ.bind (K.κ t) ≤ T.μ) {G : Set E} (hG : MeasurableSet G) (h0 : T.μ Gᶜ = 0) :
    T.μ (K.shrink S G)ᶜ = 0 := by
  have hae : ∀ᵐ x ∂T.μ, ∀ s ∈ S, K.κ s x Gᶜ = 0 := by
    rw [ae_ball_iff hS]
    intro s _
    have h1 : ∫⁻ x, K.κ s x Gᶜ ∂T.μ = 0 := by
      have := Measure.bind_apply hG.compl (K.κ s).aemeasurable (m := T.μ)
      rw [← this]
      exact le_antisymm ((hbind s) Gᶜ |>.trans h0.le) zero_le
    exact (lintegral_eq_zero_iff (Kernel.measurable_coe (K.κ s) hG.compl)).1 h1
  have h2 : T.μ {x | ¬ ∀ s ∈ S, K.κ s x Gᶜ = 0} = 0 := ae_iff.1 hae
  have h3 : (K.shrink S G)ᶜ ⊆ Gᶜ ∪ {x | ¬ ∀ s ∈ S, K.κ s x Gᶜ = 0} := by
    intro x hx
    by_contra hcon
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq] at hcon
    exact hx ⟨hcon.1, hcon.2⟩
  exact measure_mono_null h3 (measure_union_null h0 h2)

omit [IsFiniteMeasure T.μ] in
/-- The iterated shrinkings, starting from `G₀`. -/
def iterShrink (K : KernelRepresentation T) (S : Set ℝ≥0) (G₀ : Set E) : ℕ → Set E
  | 0 => G₀
  | n + 1 => K.shrink S (iterShrink K S G₀ n)

omit [IsFiniteMeasure T.μ] in
lemma iterShrink_good (S : Set ℝ≥0) (hS : S.Countable) (hbind : ∀ t, T.μ.bind (K.κ t) ≤ T.μ)
    {G₀ : Set E} (hG₀ : MeasurableSet G₀) (h0 : T.μ G₀ᶜ = 0) (n : ℕ) :
    MeasurableSet (K.iterShrink S G₀ n) ∧ T.μ (K.iterShrink S G₀ n)ᶜ = 0 := by
  induction n with
  | zero => exact ⟨hG₀, h0⟩
  | succ n ih =>
    exact ⟨K.measurableSet_shrink S hS ih.1, K.measure_shrink_compl S hS hbind ih.1 ih.2⟩

/-- **Exact Chapman-Kolmogorov on a conull, properly exceptional set, for countably many times**
(discrete-time Fukushima regularisation; BGL Sect. 1.2 symmetry gives `μ.bind κ_s ≤ μ`). -/
theorem exists_exact_ck [MeasurableSpace.CountablyGenerated E] (S : Set ℝ≥0) (hS : S.Countable)
    (hbind : ∀ t, T.μ.bind (K.κ t) ≤ T.μ) :
    ∃ G : Set E, MeasurableSet G ∧ T.μ Gᶜ = 0 ∧
      (∀ x ∈ G, ∀ s ∈ S, K.κ s x Gᶜ = 0) ∧
      (∀ x ∈ G, ∀ s ∈ S, ∀ t ∈ S, K.κ (s + t) x = (K.κ t ∘ₖ K.κ s) x) ∧
      (0 ∈ S → ∀ x ∈ G, K.κ 0 x = Measure.dirac x) := by
  have hae : ∀ᵐ x ∂T.μ, (∀ s ∈ S, ∀ t ∈ S, K.κ (s + t) x = (K.κ t ∘ₖ K.κ s) x) ∧
      (0 ∈ S → K.κ 0 x = Measure.dirac x) := by
    have h1 : ∀ᵐ x ∂T.μ, ∀ s ∈ S, ∀ t ∈ S, K.κ (s + t) x = (K.κ t ∘ₖ K.κ s) x := by
      rw [ae_ball_iff hS]
      intro s hs
      rw [ae_ball_iff hS]
      intro t _
      exact K.ck_ae s t
    filter_upwards [h1, K.kappa_zero_ae] with x hx1 hx2
    exact ⟨hx1, fun _ => hx2⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hae)
  set G₀ : Set E := Nᶜ with hG₀
  have hG₀m : MeasurableSet G₀ := hNm.compl
  have hG₀c : T.μ G₀ᶜ = 0 := by rw [hG₀, compl_compl]; exact hN0
  have hG₀good : ∀ x ∈ G₀, (∀ s ∈ S, ∀ t ∈ S, K.κ (s + t) x = (K.κ t ∘ₖ K.κ s) x) ∧
      (0 ∈ S → K.κ 0 x = Measure.dirac x) := by
    intro x hx
    by_contra hcon
    exact hx (hNsub hcon)
  have hgood := K.iterShrink_good S hS hbind hG₀m hG₀c
  set G : Set E := ⋂ n, K.iterShrink S G₀ n with hG
  have hsub : ∀ n, G ⊆ K.iterShrink S G₀ n := fun n => Set.iInter_subset _ n
  have hGm : MeasurableSet G := MeasurableSet.iInter fun n => (hgood n).1
  have hGc : T.μ Gᶜ = 0 := by
    rw [hG, Set.compl_iInter]
    exact measure_iUnion_null fun n => (hgood n).2
  have hmono : ∀ n, K.iterShrink S G₀ (n + 1) ⊆ K.iterShrink S G₀ n := fun n x hx => hx.1
  have hG0 : ∀ n, K.iterShrink S G₀ n ⊆ G₀ := by
    intro n
    induction n with
    | zero => exact fun _ h => h
    | succ n ih => exact (hmono n).trans ih
  refine ⟨G, hGm, hGc, ?_, ?_, ?_⟩
  · intro x hx s hs
    have : Gᶜ ⊆ ⋃ n, (K.iterShrink S G₀ n)ᶜ := by
      rw [hG, Set.compl_iInter]
    refine measure_mono_null this (measure_iUnion_null fun n => ?_)
    have hx' : x ∈ K.iterShrink S G₀ (n + 1) := hsub (n + 1) hx
    exact hx'.2 s hs
  · intro x hx
    exact (hG₀good x (hG0 0 (hsub 0 hx))).1
  · intro h0 x hx
    exact (hG₀good x (hG0 0 (hsub 0 hx))).2 h0

end KernelRepresentation

section Riesz

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] (T : DiffusionTriple X) [IsFiniteMeasure T.μ]

/-- **Exact Chapman-Kolmogorov for the Riesz kernels** of every triple on a compact metrizable space, on a conull
properly exceptional set, for any countable set `S` of times (e.g. the nonnegative rationals). -/
theorem rieszKernel_exists_exact_ck (S : Set ℝ≥0) (hS : S.Countable) :
    ∃ G : Set X, MeasurableSet G ∧ T.μ Gᶜ = 0 ∧
      (∀ x ∈ G, ∀ s ∈ S, rieszKernel T s x Gᶜ = 0) ∧
      (∀ x ∈ G, ∀ s ∈ S, ∀ t ∈ S, rieszKernel T (s + t) x = (rieszKernel T t ∘ₖ rieszKernel T s) x) ∧
      (0 ∈ S → ∀ x ∈ G, rieszKernel T 0 x = Measure.dirac x) :=
  (rieszKernelRep T).exists_exact_ck S hS (rieszKernelRep_subInvariant T)

end Riesz

end MarkovTriple.Stochastic
