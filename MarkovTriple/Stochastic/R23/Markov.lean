import Mathlib
import MarkovTriple.Stochastic.R23.Triple
import MarkovTriple.BGL.Semigroup.Conservative

/-!
# Round 23 (S), part 4: conservative triples give Markov kernels (infinite `μ`)

For a `StandardTriple` (so `P_t u_n → 1` a.e. along exhaustion sequences, field `conservative`; for infinite `μ`
this is the only meaning of `P_t 1 = 1`) with `μ` finite on compacts, the kernels `κ_t` of `ncKernelRepInf`
have total mass `1` for `μ`-a.e. `x`.  Route: `κ_t(x, X) ≥ ∫ u_n dκ_t(x,·) = P_t u_n(x) → 1`, where the
representation on the bounded measurable `u_n ∈ 𝒜₀ ⊆ L²` is the one of `ncKernelRepInf`, and `u_n ≤ 1`
`κ_t(x,·)`-a.e. for `μ`-a.e. `x` by sub-invariance.  Redefining `κ_t(x,·) := δ_x` on the null set
`{κ_t(x,X) ≠ 1}` gives `IsMarkovRep`.  See `STATEMENTS_R23_S.md`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R23

open MarkovTriple.BGL MarkovTriple.Stochastic

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

variable (S : StandardTriple X) [IsFiniteMeasureOnCompacts S.μ]

/-- **Conservativity gives mass one a.e.** -/
theorem ncKernelRepInf_univ_ae (t : ℝ≥0) :
    ∀ᵐ x ∂S.μ, (ncKernelRepInf S.toDiffusionTriple).κ t x Set.univ = 1 := by
  set T := S.toDiffusionTriple with hT
  set K := ncKernelRepInf T with hK
  obtain ⟨v, hv, hv0⟩ := T.exists_nonneg_exhaustion
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have hv : IsExhaustion T.μ T.A₀ v := ⟨hv1, hv2, hv3⟩
  have hcons := S.conservative v hv (fun n => Filter.Eventually.of_forall (hv0 n)) t
  have hvm : ∀ n, Measurable (v n) := fun n => T.measurable _ (hv1 n)
  have hvb : ∀ n, ∃ C, ∀ x, |v n x| ≤ C := fun n => T.bounded _ (hv1 n)
  have hvL : ∀ n, MemLp (v n) 2 T.μ := fun n => T.memLp _ (hv1 n) 2 (by norm_num) (by norm_num)
  -- `v n ≤ 1` a.e.
  have hle1 : ∀ᵐ x ∂T.μ, ∀ n, v n x ≤ 1 := by
    have h1 : ∀ᵐ x ∂T.μ, ∀ n, v n x ≤ v (n + 1) x := ae_all_iff.2 hv2
    filter_upwards [h1, hv3] with x h1 h2 n
    exact (monotone_nat_of_le_succ h1).ge_of_tendsto h2 n
  -- hence `κ x {v n > 1} = 0` for a.e. `x`
  have hκ1 : ∀ᵐ x ∂T.μ, ∀ n, ∀ᵐ y ∂(K.κ t x), v n y ≤ 1 := by
    have hnull : ∀ n, (T.μ.bind (K.κ t)) {y | ¬ v n y ≤ 1} = 0 := by
      intro n
      refine le_antisymm ?_ bot_le
      refine (ncKernelRepInf_subInvariant T t _).trans ?_
      have := hle1
      rw [ae_all_iff] at this
      exact le_of_eq (by simpa [ae_iff] using this n)
    have hm : ∀ n, MeasurableSet {y | ¬ v n y ≤ 1} := fun n =>
      (measurableSet_le (hvm n) measurable_const).compl
    have : ∀ n, ∀ᵐ x ∂T.μ, K.κ t x {y | ¬ v n y ≤ 1} = 0 := fun n => by
      have h0 := hnull n
      rw [Measure.bind_apply (hm n) (K.κ t).aemeasurable] at h0
      exact (lintegral_eq_zero_iff ((K.κ t).measurable_coe (hm n))).1 h0
    filter_upwards [ae_all_iff.2 this] with x hx n
    exact hx n
  -- representation
  have hrep : ∀ᵐ x ∂T.μ, ∀ n, (T.semigroup t (T.cls ⟨v n, hv1 n⟩) : X → ℝ) x
      = ∫ y, v n y ∂(K.κ t x) := by
    refine ae_all_iff.2 fun n => ?_
    have e : T.cls ⟨v n, hv1 n⟩ = (hvL n).toLp (v n) := by
      refine Lp.ext ?_
      filter_upwards [DiffusionTriple.coeFn_cls T ⟨v n, hv1 n⟩, (hvL n).coeFn_toLp] with x h1 h2
      rw [h1, h2]
    rw [e]
    exact K.rep t (v n) (hvm n) (hvb n) (hvL n)
  filter_upwards [hcons, hrep, hκ1] with x h1 h2 h3
  have hfin : IsFiniteMeasure (K.κ t x) := ⟨lt_of_le_of_lt (K.subMarkov t x) ENNReal.one_lt_top⟩
  have hreal : (K.κ t x).real Set.univ ≤ 1 := by
    have := K.subMarkov t x
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top this
  have hge : ∀ n, (T.semigroup t (T.cls ⟨v n, hv1 n⟩) : X → ℝ) x ≤ (K.κ t x).real Set.univ := by
    intro n
    rw [h2 n]
    have hi : Integrable (v n) (K.κ t x) := by
      obtain ⟨C, hC⟩ := hvb n
      exact Integrable.of_bound (hvm n).aestronglyMeasurable C
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
    calc ∫ y, v n y ∂(K.κ t x) ≤ ∫ y, (1 : ℝ) ∂(K.κ t x) :=
          integral_mono_ae hi (integrable_const _) (h3 n)
      _ = (K.κ t x).real Set.univ := by simp
  have h4 : 1 ≤ (K.κ t x).real Set.univ := le_of_tendsto h1 (Filter.Eventually.of_forall hge)
  have h5 : (K.κ t x).real Set.univ = 1 := le_antisymm hreal h4
  rw [Measure.real] at h5
  exact (ENNReal.toReal_eq_one_iff _).1 h5

/-- **Markov representation for conservative triples with infinite `μ`.** -/
theorem exists_markovRep : ∃ K : KernelRepresentation S.toDiffusionTriple, K.IsMarkovRep := by
  classical
  set K0 := ncKernelRepInf S.toDiffusionTriple with hK0
  have hs : ∀ t, MeasurableSet {x | K0.κ t x Set.univ = 1} := fun t =>
    (Kernel.measurable_coe (K0.κ t) MeasurableSet.univ) (measurableSet_singleton 1)
  let κ' : ℝ≥0 → Kernel X X := fun t => Kernel.piecewise (hs t) (K0.κ t) Kernel.id
  have hmk : ∀ t x, κ' t x Set.univ = 1 := by
    intro t x
    by_cases hx : x ∈ {x | K0.κ t x Set.univ = 1}
    · simp only [κ', Kernel.piecewise_apply, hx, ite_true]; exact hx
    · simp only [κ', Kernel.piecewise_apply, hx, ite_false]; simp
  have hae : ∀ t, ∀ᵐ x ∂S.μ, κ' t x = K0.κ t x := fun t => by
    filter_upwards [ncKernelRepInf_univ_ae S t] with x hx
    have hx' : K0.κ t x Set.univ = 1 := hx
    simp [κ', Kernel.piecewise_apply, hx']
  refine ⟨⟨κ', fun t x => (hmk t x).le, ?_⟩, hmk⟩
  intro t g hg hb hL
  filter_upwards [K0.rep t g hg hb hL, hae t] with x h1 h2
  rw [h1, h2]

end MarkovTriple.Stochastic.R23
