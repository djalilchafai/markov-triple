import Mathlib
import MarkovTriple.Stochastic.R24.Bridge
import MarkovTriple.Stochastic.R23.Markov

/-!
# Round 25 (E), part 4: total mass of the Feller kernels: a.e. one, lower semicontinuous, and what closes the gap

For a `StandardTriple` `S` (S11 conservativity) with `IsFellerC0`:
* `fellerKernelInf_univ_ae`: `κ_t(x, X) = 1` for `μ`-a.e. `x` (R23 argument for the R24 kernels);
* `fellerKernelInf_univ_lsc`: `x ↦ κ_t(x, X)` is lower semicontinuous (a supremum of the continuous `Q_t f`, `0 ≤ f ≤ 1`);
* hence the deficit set `{κ_t(·, X) < 1}` is an `F_σ` `μ`-null set;  a.e. equality does NOT give pointwise equality
  from lower semicontinuity (the exceptional set is closed-ish, not open);
* `fellerKernelInf_univ_eq_one_of_continuous`: under the extra hypothesis that `x ↦ κ_t(x, X)` is continuous, mass one holds
  at every point; then `fellerMarkovProcessBridgeInf_of_continuous`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R25

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R23

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

section AE

variable (S : StandardTriple X) [IsFiniteMeasureOnCompacts S.μ] [S.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 S.toDiffusionTriple)

/-- **S11 + `C_0`-Feller gives mass one a.e.** (the R23 argument, for the exact R24 kernels). -/
theorem fellerKernelInf_univ_ae (t : ℝ≥0) :
    ∀ᵐ x ∂S.μ, fellerKernelInf hF t x Set.univ = 1 := by
  set T := S.toDiffusionTriple with hT
  obtain ⟨v, hv, hv0⟩ := T.exists_nonneg_exhaustion
  obtain ⟨hv1, hv2, hv3⟩ := hv
  have hv : IsExhaustion T.μ T.A₀ v := ⟨hv1, hv2, hv3⟩
  have hcons := S.conservative v hv (fun n => Filter.Eventually.of_forall (hv0 n)) t
  have hvm : ∀ n, Measurable (v n) := fun n => T.measurable _ (hv1 n)
  have hvb : ∀ n, ∃ C, ∀ x, |v n x| ≤ C := fun n => T.bounded _ (hv1 n)
  have hvL : ∀ n, MemLp (v n) 2 T.μ := fun n => T.memLp _ (hv1 n) 2 (by norm_num) (by norm_num)
  have hle1 : ∀ᵐ x ∂T.μ, ∀ n, v n x ≤ 1 := by
    have h1 : ∀ᵐ x ∂T.μ, ∀ n, v n x ≤ v (n + 1) x := ae_all_iff.2 hv2
    filter_upwards [h1, hv3] with x h1 h2 n
    exact (monotone_nat_of_le_succ h1).ge_of_tendsto h2 n
  have hκ1 : ∀ᵐ x ∂T.μ, ∀ n, ∀ᵐ y ∂(fellerKernelInf hF t x), v n y ≤ 1 := by
    have hnull : ∀ n, (T.μ.bind (fellerKernelInf hF t)) {y | ¬ v n y ≤ 1} = 0 := by
      intro n
      refine le_antisymm ?_ bot_le
      refine (fellerKernelInf_bind_le hF t _).trans ?_
      have := hle1
      rw [ae_all_iff] at this
      exact le_of_eq (by simpa [ae_iff] using this n)
    have hm : ∀ n, MeasurableSet {y | ¬ v n y ≤ 1} := fun n =>
      (measurableSet_le (hvm n) measurable_const).compl
    have : ∀ n, ∀ᵐ x ∂T.μ, fellerKernelInf hF t x {y | ¬ v n y ≤ 1} = 0 := fun n => by
      have h0 := hnull n
      rw [Measure.bind_apply (hm n) (fellerKernelInf hF t).aemeasurable] at h0
      exact (lintegral_eq_zero_iff ((fellerKernelInf hF t).measurable_coe (hm n))).1 h0
    filter_upwards [ae_all_iff.2 this] with x hx n
    exact hx n
  have hrep : ∀ᵐ x ∂T.μ, ∀ n, (T.semigroup t (T.cls ⟨v n, hv1 n⟩) : X → ℝ) x
      = ∫ y, v n y ∂(fellerKernelInf hF t x) := by
    refine ae_all_iff.2 fun n => ?_
    have e : T.cls ⟨v n, hv1 n⟩ = (hvL n).toLp (v n) := by
      refine Lp.ext ?_
      filter_upwards [DiffusionTriple.coeFn_cls T ⟨v n, hv1 n⟩, (hvL n).coeFn_toLp] with x h1 h2
      rw [h1, h2]
    rw [e]
    exact fellerKernelInf_rep hF t (v n) (hvm n) (hvb n) (hvL n)
  filter_upwards [hcons, hrep, hκ1] with x h1 h2 h3
  have hfin : IsFiniteMeasure (fellerKernelInf hF t x) :=
    ⟨lt_of_le_of_lt (fellerKernelInf_subMarkov hF t x) ENNReal.one_lt_top⟩
  have hreal : (fellerKernelInf hF t x).real Set.univ ≤ 1 := by
    have := fellerKernelInf_subMarkov hF t x
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top this
  have hge : ∀ n, (T.semigroup t (T.cls ⟨v n, hv1 n⟩) : X → ℝ) x ≤
      (fellerKernelInf hF t x).real Set.univ := by
    intro n
    rw [h2 n]
    have hi : Integrable (v n) (fellerKernelInf hF t x) := by
      obtain ⟨C, hC⟩ := hvb n
      exact Integrable.of_bound (hvm n).aestronglyMeasurable C
        (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
    calc ∫ y, v n y ∂(fellerKernelInf hF t x) ≤ ∫ y, (1 : ℝ) ∂(fellerKernelInf hF t x) :=
          integral_mono_ae hi (integrable_const _) (h3 n)
      _ = (fellerKernelInf hF t x).real Set.univ := by simp
  have h4 : 1 ≤ (fellerKernelInf hF t x).real Set.univ := le_of_tendsto h1 (Filter.Eventually.of_forall hge)
  have h5 : (fellerKernelInf hF t x).real Set.univ = 1 := le_antisymm hreal h4
  rw [Measure.real] at h5
  exact (ENNReal.toReal_eq_one_iff _).1 h5

end AE

section LSC

variable {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

/-- the total mass is the supremum of `Q_t f (x)` over `f ∈ C_c`, `0 ≤ f ≤ 1`. -/
theorem fellerKernelInf_univ_eq_iSup (t : ℝ≥0) (x : X) :
    fellerKernelInf hF t x Set.univ =
      ⨆ f : {f : C_c(X, ℝ) // (∀ y, 0 ≤ f y) ∧ ∀ y, f y ≤ 1}, ENNReal.ofReal (Qop hF t f.1 x) := by
  refine le_antisymm ?_ (iSup_le fun f => ?_)
  · rw [fellerKernelInf_apply, MeasurableSet.univ.measure_eq_iSup_isCompact]
    refine iSup₂_le fun K _ => iSup_le fun hK => ?_
    obtain ⟨f, hf1, hf2, -, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ
      (Set.subset_univ K)
    let f' : C_c(X, ℝ) := ⟨f, hasCompactSupport_def.mpr hf2⟩
    have h1 := RealRMK.rieszMeasure_le_of_eq_one (lam hF t x) (f := f') (fun y => (hf3 y).1) hK
      (fun y hy => show f y = 1 by simpa using hf1 hy)
    refine h1.trans ?_
    exact le_iSup (fun g : {f : C_c(X, ℝ) // (∀ y, 0 ≤ f y) ∧ ∀ y, f y ≤ 1} =>
      ENNReal.ofReal (Qop hF t g.1 x)) ⟨f', fun y => (hf3 y).1, fun y => (hf3 y).2⟩
  · have hfin : IsFiniteMeasure (fellerKernelInf hF t x) := inferInstance
    obtain ⟨f, h0, h1⟩ := f
    have hi : Integrable f (fellerKernelInf hF t x) := f.continuous.integrable_of_hasCompactSupport
      f.hasCompactSupport
    rw [← integral_fellerKernelInf hF t x f]
    have : ∫ y, f y ∂(fellerKernelInf hF t x) ≤ ∫ y, (1 : ℝ) ∂(fellerKernelInf hF t x) :=
      integral_mono hi (integrable_const _) h1
    refine (ENNReal.ofReal_le_ofReal this).trans ?_
    simp [Measure.real]

/-- **Lower semicontinuity of the total mass** (the wrong direction for passing from a.e. to every point). -/
theorem fellerKernelInf_univ_lsc (t : ℝ≥0) :
    LowerSemicontinuous fun x => fellerKernelInf hF t x Set.univ := by
  have : (fun x => fellerKernelInf hF t x Set.univ) = fun x =>
      ⨆ f : {f : C_c(X, ℝ) // (∀ y, 0 ≤ f y) ∧ ∀ y, f y ≤ 1}, ENNReal.ofReal (Qop hF t f.1 x) :=
    funext (fellerKernelInf_univ_eq_iSup hF t)
  rw [this]
  exact lowerSemicontinuous_iSup fun f =>
    (ENNReal.continuous_ofReal.comp (Qop hF t f.1).continuous).lowerSemicontinuous

theorem fellerKernelInf_deficit_closed (t : ℝ≥0) (c : ℝ) :
    IsClosed {x | fellerKernelInf hF t x Set.univ ≤ ENNReal.ofReal c} :=
  (fellerKernelInf_univ_lsc hF t).isClosed_preimage _

end LSC

section Deficit

variable (S : StandardTriple X) [IsFiniteMeasureOnCompacts S.μ] [S.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 S.toDiffusionTriple)

/-- The exceptional set `{κ_t(·, X) < 1}` is an `F_σ` `μ`-null set (so its complement is a dense `G_δ`); S11 alone
does not obviously make it empty; no proof or counterexample that it is non-empty is given here (open). -/
theorem fellerKernelInf_deficit_null_Fsigma (t : ℝ≥0) :
    ∃ F : ℕ → Set X, (∀ n, IsClosed (F n)) ∧ (∀ n, S.μ (F n) = 0) ∧
      {x | fellerKernelInf hF t x Set.univ < 1} = ⋃ n, F n := by
  refine ⟨fun n : ℕ => {x | fellerKernelInf hF t x Set.univ ≤ ENNReal.ofReal (1 - 1 / ((n : ℝ) + 1))},
    fun n => fellerKernelInf_deficit_closed hF t _, fun n => ?_, ?_⟩
  · have hae := fellerKernelInf_univ_ae S hF t
    refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hae)
    intro h1
    have hx' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1 - 1 / ((n : ℝ) + 1)) := h1 ▸ hx
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by
      have : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith)] at hx'
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  · ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    have hle : fellerKernelInf hF t x Set.univ ≤ 1 := fellerKernelInf_subMarkov hF t x
    constructor
    · intro hlt
      have hr : (fellerKernelInf hF t x Set.univ).toReal < 1 := by
        have := ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt
        simpa using this
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hr)
      refine ⟨n, ?_⟩
      rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hle)]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    · rintro ⟨n, hn⟩
      refine lt_of_le_of_lt hn ?_
      rw [← ENNReal.ofReal_one]
      refine (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 ?_
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith

/-- **The extra hypothesis that works**: if the total mass `x ↦ κ_t(x, X)` is continuous (the semigroup maps the
constant `1` to a continuous function), S11 + Feller gives mass one at EVERY point. -/
theorem fellerKernelInf_univ_eq_one_of_continuous (t : ℝ≥0)
    (hc : Continuous fun x => (fellerKernelInf hF t x Set.univ).toReal) (x : X) :
    fellerKernelInf hF t x Set.univ = 1 := by
  have hae : (fun x => (fellerKernelInf hF t x Set.univ).toReal) =ᵐ[S.μ] fun _ => (1 : ℝ) := by
    filter_upwards [fellerKernelInf_univ_ae S hF t] with y hy
    simp [hy]
  have := (hc.ae_eq_iff_eq S.μ continuous_const).1 hae
  have hx := congrFun this x
  exact (ENNReal.toReal_eq_one_iff _).1 hx

/-- **A `MarkovProcessBridge` for a conservative `C_0`-Feller triple with continuous mass function.** -/
noncomputable def fellerMarkovProcessBridgeInf_of_continuous
    (hc : ∀ t : ℝ≥0, Continuous fun x => (fellerKernelInf hF t x Set.univ).toReal) :
    MarkovProcessBridge S.toDiffusionTriple :=
  fellerMarkovProcessBridgeInf hF (fun t x => fellerKernelInf_univ_eq_one_of_continuous S hF t (hc t) x)

end Deficit

end MarkovTriple.Stochastic.R25
