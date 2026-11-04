import Mathlib
import MarkovTriple.Stochastic.RieszKernel

/-!
# Round 23 (S): Riesz-Markov kernel from an a.e.-linear family on a compact space

Abstract compact lemma: `Y` compact metrizable, `m` any measure, `F : C(Y,ℝ) → Y → ℝ` a family of measurable
functions which is a.e.-additive, a.e.-homogeneous, a.e.-positive, with `F 1 ≤ 1` a.e.  Then there is a sub-Markov
kernel `κ` with `F f = (y ↦ ∫ f dκ y)` `m`-a.e. for every `f`.  This is the R15 proof
(`exists_kernel_of_posContraction`, `RieszKernel.lean`) with the `L²`-continuity of `f ↦ P[f]` replaced by the
sup-norm bound `|F f| ≤ ‖f‖` (`abs_le_norm_of_aeLinear`), so that it applies to families defined only through
monotone limits (infinite `μ`).  See `STATEMENTS_R23_S.md`.
-/

open MeasureTheory ProbabilityTheory Topology Filter
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R23

open MarkovTriple.Stochastic

variable {Y : Type*} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y]

omit [T2Space Y] [SecondCountableTopology Y] [BorelSpace Y] [MeasurableSpace Y] in
/-- sup-norm bound of an a.e.-linear positive sub-Markov family. -/
lemma abs_le_norm_of_aeLinear {Z : Type*} [MeasurableSpace Z] {m : Measure Z}
    (F : C(Y, ℝ) → Z → ℝ)
    (hadd : ∀ f g, F (f + g) =ᵐ[m] F f + F g) (hsmul : ∀ (c : ℝ) f, F (c • f) =ᵐ[m] c • F f)
    (hpos : ∀ f, 0 ≤ f → 0 ≤ᵐ[m] F f) (hone : F 1 ≤ᵐ[m] 1) (f : C(Y, ℝ)) :
    ∀ᵐ z ∂m, |F f z| ≤ ‖f‖ := by
  have hA : 0 ≤ ‖f‖ • (1 : C(Y, ℝ)) + (-1 : ℝ) • f := by
    intro x
    have := ContinuousMap.norm_coe_le_norm f x
    rw [Real.norm_eq_abs] at this
    show (0 : ℝ) ≤ ‖f‖ • (1 : ℝ) + (-1 : ℝ) • f x
    simp only [smul_eq_mul]
    linarith [le_abs_self (f x)]
  have hB : 0 ≤ ‖f‖ • (1 : C(Y, ℝ)) + f := by
    intro x
    have := ContinuousMap.norm_coe_le_norm f x
    rw [Real.norm_eq_abs] at this
    show (0 : ℝ) ≤ ‖f‖ • (1 : ℝ) + f x
    simp only [smul_eq_mul]
    linarith [neg_abs_le (f x)]
  filter_upwards [hpos _ hA, hpos _ hB, hone, hadd (‖f‖ • (1 : C(Y, ℝ))) ((-1 : ℝ) • f),
    hadd (‖f‖ • (1 : C(Y, ℝ))) f, hsmul ‖f‖ (1 : C(Y, ℝ)), hsmul (-1 : ℝ) f]
    with z h1 h2 h3 h4 h5 h6 h7
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Pi.one_apply] at h1 h2 h3 h4 h5 h6 h7
  have hc : 0 ≤ ‖f‖ := norm_nonneg f
  have : ‖f‖ * F 1 z ≤ ‖f‖ := by
    calc ‖f‖ * F 1 z ≤ ‖f‖ * 1 := by gcongr
      _ = ‖f‖ := mul_one _
  rw [h4, h6, h7] at h1
  rw [h5, h6] at h2
  rw [abs_le]
  constructor <;> nlinarith

/-- **Riesz-Markov kernel from an a.e.-linear positive sub-Markov family on a compact space.** -/
theorem exists_kernel_of_aeLinear (m : Measure Y) (F : C(Y, ℝ) → Y → ℝ)
    (hFm : ∀ f, Measurable (F f))
    (hadd : ∀ f g, F (f + g) =ᵐ[m] F f + F g) (hsmul : ∀ (c : ℝ) f, F (c • f) =ᵐ[m] c • F f)
    (hpos : ∀ f, 0 ≤ f → 0 ≤ᵐ[m] F f) (hone : F 1 ≤ᵐ[m] 1) :
    ∃ κ : Kernel Y Y, (∀ y, κ y Set.univ ≤ 1) ∧
      ∀ f : C(Y, ℝ), F f =ᵐ[m] fun y => ∫ z, f z ∂(κ y) := by
  classical
  have hB := abs_le_norm_of_aeLinear F hadd hsmul hpos hone
  -- a countable dense additive subgroup `V ∋ 1`
  obtain ⟨D0, hD0c, hD0d⟩ := TopologicalSpace.exists_countable_dense C(Y, ℝ)
  set S : Set C(Y, ℝ) := insert 1 D0 with hS
  have hSc : S.Countable := hD0c.insert 1
  have : Countable S := hSc.to_subtype
  let V : Submodule ℤ C(Y, ℝ) := Submodule.span ℤ (Set.range ((↑) : S → C(Y, ℝ)))
  have hVS : S ⊆ (V : Set C(Y, ℝ)) := fun a ha => Submodule.subset_span ⟨⟨a, ha⟩, rfl⟩
  let Vg : AddSubgroup C(Y, ℝ) := V.toAddSubgroup
  have hVdense : Dense (Vg : Set C(Y, ℝ)) :=
    hD0d.mono (fun a ha => hVS (Set.mem_insert_of_mem _ ha))
  have h1V : (1 : C(Y, ℝ)) ∈ Vg := hVS (Set.mem_insert _ _)
  have : Countable V := inferInstance
  have : Countable Vg := inferInstanceAs (Countable V)
  have hgood : ∀ᵐ x ∂m, (∀ v w : Vg, F ((v : C(Y, ℝ)) + (w : C(Y, ℝ))) x = F v x + F w x) ∧
      (∀ v : Vg, |F v x| ≤ ‖(v : C(Y, ℝ))‖) ∧ (∀ v : Vg, 0 ≤ (v : C(Y, ℝ)) → 0 ≤ F v x) := by
    have e1 : ∀ᵐ x ∂m, ∀ p : Vg × Vg,
        F ((p.1 : C(Y, ℝ)) + (p.2 : C(Y, ℝ))) x = F p.1 x + F p.2 x :=
      ae_all_iff.2 fun p => by
        filter_upwards [hadd (p.1 : C(Y, ℝ)) (p.2 : C(Y, ℝ))] with x h
        simpa using h
    have e2 : ∀ᵐ x ∂m, ∀ v : Vg, |F v x| ≤ ‖(v : C(Y, ℝ))‖ := ae_all_iff.2 fun v => hB _
    have e3 : ∀ᵐ x ∂m, ∀ v : Vg, 0 ≤ (v : C(Y, ℝ)) → 0 ≤ F v x :=
      ae_all_iff.2 fun v => by
        by_cases hv : 0 ≤ (v : C(Y, ℝ))
        · filter_upwards [hpos _ hv] with x hx _ using hx
        · exact Filter.Eventually.of_forall fun x h => absurd h hv
    filter_upwards [e1, e2, e3] with x a b c
    exact ⟨fun v w => a (v, w), b, c⟩
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hgood)
  have hgoodN : ∀ x, x ∉ N → (∀ v w : Vg, F ((v : C(Y, ℝ)) + (w : C(Y, ℝ))) x = F v x + F w x) ∧
      (∀ v : Vg, |F v x| ≤ ‖(v : C(Y, ℝ))‖) ∧ (∀ v : Vg, 0 ≤ (v : C(Y, ℝ)) → 0 ≤ F v x) := by
    intro x hx
    by_contra hcon
    exact hx (hNsub hcon)
  have hL : ∀ x : Y, ∃ L : C(Y, ℝ) →L[ℝ] ℝ, x ∉ N → (∀ v : Vg, L v = F v x) ∧
      (∀ f : C(Y, ℝ), 0 ≤ f → 0 ≤ L f) := by
    intro x
    by_cases hx : x ∈ N
    · exact ⟨0, fun h => absurd hx h⟩
    · obtain ⟨hA, hB', hC⟩ := hgoodN x hx
      let Λ : Vg →+ ℝ := AddMonoidHom.mk' (fun v : Vg => F v x) (fun v w => hA v w)
      obtain ⟨L, hL1, hL2, -⟩ := exists_posFunctional Vg hVdense h1V Λ (fun v => hB' v)
        (fun v hv => hC v hv)
      exact ⟨L, fun _ => ⟨hL1, hL2⟩⟩
  choose Lx hLx using hL
  have hM : ∀ x : Y, ∃ μx : Measure Y, IsFiniteMeasure μx ∧
      (x ∉ N → ∀ f : C(Y, ℝ), ∫ y, f y ∂μx = Lx x f) ∧ (x ∈ N → μx = 0) := by
    intro x
    by_cases hx : x ∈ N
    · exact ⟨0, inferInstance, fun h => absurd hx h, fun _ => rfl⟩
    · obtain ⟨μx, hm, hint⟩ := exists_measure_of_pos (Lx x) ((hLx x hx).2)
      exact ⟨μx, hm, fun _ => hint, fun h => absurd h hx⟩
  choose κ' hκfin hκint hκzero using hM
  have : ∀ x, IsFiniteMeasure (κ' x) := hκfin
  have hseq : ∀ f : C(Y, ℝ), ∃ v : ℕ → Vg, Tendsto (fun n => (v n : C(Y, ℝ))) atTop (𝓝 f) := by
    intro f
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 (hVdense f)
    exact ⟨fun n => ⟨u n, hu n⟩, hlim⟩
  have hmeas_int : ∀ f : C(Y, ℝ), Measurable fun x => ∫ y, f y ∂(κ' x) := by
    intro f
    obtain ⟨v, hv⟩ := hseq f
    have hg : ∀ n, Measurable fun x => if x ∈ N then (0 : ℝ) else F (v n) x := fun n =>
      Measurable.ite hNm measurable_const (hFm _)
    refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun x => ?_)
    by_cases hx : x ∈ N
    · simp only [hx, ite_true, hκzero x hx, integral_zero_measure]
      exact tendsto_const_nhds
    · simp only [hx, ite_false, hκint x hx f]
      have h2 : Tendsto (fun n => Lx x (v n : C(Y, ℝ))) atTop (𝓝 (Lx x f)) :=
        ((Lx x).continuous.tendsto f).comp hv
      refine h2.congr fun n => ?_
      exact (hLx x hx).1 (v n)
  have hκmeas : Measurable κ' := measurable_of_integrals hmeas_int
  refine ⟨{ toFun := κ', measurable' := hκmeas }, ?_, ?_⟩
  · intro x
    show κ' x Set.univ ≤ 1
    by_cases hx : x ∈ N
    · rw [hκzero x hx]; simp
    · have h1 := hκint x hx 1
      have h2 : Lx x (1 : C(Y, ℝ)) = F (1 : C(Y, ℝ)) x := (hLx x hx).1 ⟨1, h1V⟩
      have h3 : |F (1 : C(Y, ℝ)) x| ≤ ‖(1 : C(Y, ℝ))‖ := (hgoodN x hx).2.1 ⟨1, h1V⟩
      have h4 : (κ' x).real Set.univ ≤ 1 := by
        have : (κ' x).real Set.univ = Lx x (1 : C(Y, ℝ)) := by
          rw [← h1]; simp
        rw [this, h2]
        exact (le_abs_self _).trans (h3.trans norm_one_le_one)
      calc κ' x Set.univ = ENNReal.ofReal ((κ' x).real Set.univ) := by
            rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
        _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal h4
        _ = 1 := ENNReal.ofReal_one
  · intro f
    obtain ⟨v, hv⟩ := hseq f
    have hdiff : ∀ n, ∀ᵐ x ∂m, |F (v n : C(Y, ℝ)) x - F f x| ≤ ‖(v n : C(Y, ℝ)) - f‖ := by
      intro n
      filter_upwards [hB ((v n : C(Y, ℝ)) - f), hadd ((v n : C(Y, ℝ)) - f) f] with x h1 h2
      rw [sub_add_cancel] at h2
      simp only [Pi.add_apply] at h2
      rw [h2]
      simpa using h1
    have hall : ∀ᵐ x ∂m, ∀ n, |F (v n : C(Y, ℝ)) x - F f x| ≤ ‖(v n : C(Y, ℝ)) - f‖ :=
      ae_all_iff.2 hdiff
    have hNc : ∀ᵐ x ∂m, x ∉ N := by
      rw [ae_iff]; simpa using hN0
    have hn0 : Tendsto (fun n => ‖(v n : C(Y, ℝ)) - f‖) atTop (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.1 hv
    filter_upwards [hall, hNc] with x h1 h3
    show F f x = ∫ y, f y ∂(κ' x)
    rw [hκint x h3 f]
    have h4 : Tendsto (fun n => Lx x (v n : C(Y, ℝ))) atTop (𝓝 (Lx x f)) :=
      ((Lx x).continuous.tendsto f).comp hv
    have h5 : Tendsto (fun n => F (v n : C(Y, ℝ)) x) atTop (𝓝 (Lx x f)) :=
      h4.congr fun n => (hLx x h3).1 (v n)
    have h6 : Tendsto (fun n => F (v n : C(Y, ℝ)) x) atTop (𝓝 (F f x)) := by
      rw [tendsto_iff_dist_tendsto_zero]
      exact squeeze_zero (fun n => dist_nonneg) (fun n => by
        rw [Real.dist_eq]; exact h1 n) hn0
    exact tendsto_nhds_unique h6 h5

end MarkovTriple.Stochastic.R23
