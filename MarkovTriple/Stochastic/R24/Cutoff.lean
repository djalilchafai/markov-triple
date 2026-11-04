import Mathlib
import MarkovTriple.Stochastic.R24.Operator

/-!
# Round 24 (C), part 2: continuous cut-offs, `C_c`-determined measurability and uniqueness

Locally compact, second countable `X` with a fixed compact exhaustion `K_n`; `χ_n ∈ C_c(X)`, `0 ≤ χ_n ≤ 1`,
`χ_n = 1` on `K_n`.  Used to reduce statements about bounded continuous functions to `C_c(X)`:

* `tendsto_integral_cutMul`: `∫ χ_n g dm → ∫ g dm` for finite `m`, bounded continuous `g`;
* `measurable_of_integrals_cc`: a measure-valued map of finite measures is measurable as soon as `y ↦ ∫ f dκ_y` is
  measurable for each `f ∈ C_c`;
* `ext_of_integral_cc`: finite Borel measures are determined by their integrals on `C_c`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- a fixed compact exhaustion -/
noncomputable def cexh (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X]
    [SecondCountableTopology X] : CompactExhaustion X := CompactExhaustion.choice X

omit [MeasurableSpace X] [BorelSpace X] in
lemma exists_cutoff (n : ℕ) :
    ∃ f : C_c(X, ℝ), (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧ ∀ x ∈ cexh X n, f x = 1 := by
  obtain ⟨f, hf1, hf2, -, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    ((cexh X).isCompact n) (isOpen_interior (s := cexh X (n + 1))) ((cexh X).subset_interior_succ n)
  exact ⟨⟨f, hasCompactSupport_def.mpr hf2⟩, hf3, fun x hx => by simpa using hf1 hx⟩

/-- the `n`-th cut-off -/
noncomputable def cutoff (X : Type*) [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
    [SecondCountableTopology X] (n : ℕ) : C_c(X, ℝ) := Classical.choose (exists_cutoff (X := X) n)

omit [MeasurableSpace X] [BorelSpace X] in
lemma cutoff_mem (n : ℕ) (x : X) : 0 ≤ cutoff X n x ∧ cutoff X n x ≤ 1 :=
  (Classical.choose_spec (exists_cutoff (X := X) n)).1 x

omit [MeasurableSpace X] [BorelSpace X] in
lemma cutoff_eq_one (n : ℕ) {x : X} (hx : x ∈ cexh X n) : cutoff X n x = 1 :=
  (Classical.choose_spec (exists_cutoff (X := X) n)).2 x hx

omit [MeasurableSpace X] [BorelSpace X] in
lemma cutoff_eventually_one (x : X) : ∀ᶠ n in atTop, cutoff X n x = 1 := by
  obtain ⟨N, hN⟩ := (cexh X).exists_mem x
  filter_upwards [eventually_ge_atTop N] with n hn
  exact cutoff_eq_one n ((cexh X).subset hn hN)

omit [MeasurableSpace X] [BorelSpace X] in
lemma cutoff_eventually_one_of_isCompact {C : Set X} (hC : IsCompact C) :
    ∀ᶠ n in atTop, ∀ x ∈ C, cutoff X n x = 1 := by
  obtain ⟨N, hN⟩ := (cexh X).exists_superset_of_isCompact hC
  filter_upwards [eventually_ge_atTop N] with n hn x hx
  exact cutoff_eq_one n ((cexh X).subset hn (hN hx))

/-- `χ_n · g ∈ C_c` -/
noncomputable def cutMul (n : ℕ) (g : C(X, ℝ)) : C_c(X, ℝ) :=
  ⟨⟨fun x => cutoff X n x * g x, (cutoff X n).continuous.mul g.continuous⟩,
    (cutoff X n).hasCompactSupport.mul_right⟩

omit [MeasurableSpace X] [BorelSpace X] in
@[simp] lemma cutMul_apply (n : ℕ) (g : C(X, ℝ)) (x : X) : cutMul n g x = cutoff X n x * g x := rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma tendsto_cutMul (g : C(X, ℝ)) (x : X) : Tendsto (fun n => cutMul n g x) atTop (𝓝 (g x)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [cutoff_eventually_one x] with n hn
  simp [hn]

/-- `∫ χ_n g dm → ∫ g dm` for bounded continuous `g` and finite `m`. -/
lemma tendsto_integral_cutMul (m : Measure X) [IsFiniteMeasure m] (g : C(X, ℝ)) {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) :
    Tendsto (fun n => ∫ x, cutMul n g x ∂m) atTop (𝓝 (∫ x, g x ∂m)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ => C) (fun n => ?_) (integrable_const _)
    (fun n => Filter.Eventually.of_forall fun x => ?_)
    (Filter.Eventually.of_forall fun x => tendsto_cutMul g x)
  · exact (cutMul n g).continuous.aestronglyMeasurable
  · rw [Real.norm_eq_abs, cutMul_apply, abs_mul]
    have h1 : |cutoff X n x| ≤ 1 := by
      rw [abs_of_nonneg (cutoff_mem n x).1]; exact (cutoff_mem n x).2
    calc |cutoff X n x| * |g x| ≤ 1 * C := mul_le_mul h1 (hC x) (abs_nonneg _) zero_le_one
      _ = C := one_mul _

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] [BorelSpace X] [TopologicalSpace X] in
lemma abs_integral_le_of_bound (m : Measure X) [IsFiniteMeasure m] {g : X → ℝ} {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) : |∫ x, g x ∂m| ≤ |C| * m.real Set.univ := by
  have h1 : ‖∫ y, g y ∂m‖ ≤ |C| * m.real Set.univ :=
    norm_integral_le_of_norm_le_const (C := |C|)
      (Filter.Eventually.of_forall fun y => by
        simpa [Real.norm_eq_abs] using (hC y).trans (le_abs_self C))
  simpa using h1

/-- **Measurability from `C_c`**: finite-measure valued maps are measurable once all `C_c` integrals are. -/
lemma measurable_of_integrals_cc {Y : Type*} [MeasurableSpace Y] {κ : Y → Measure X}
    [∀ y, IsFiniteMeasure (κ y)]
    (h : ∀ f : C_c(X, ℝ), Measurable fun y => ∫ z, f z ∂(κ y)) : Measurable κ := by
  have hb : ∀ g : C(X, ℝ), (∀ x, |g x| ≤ 1) → Measurable fun y => ∫ z, g z ∂(κ y) := by
    intro g hg
    refine measurable_of_tendsto_metrizable (fun n => h (cutMul n g)) (tendsto_pi_nhds.2 fun y => ?_)
    exact tendsto_integral_cutMul (κ y) g hg
  have hclosed : ∀ K : Set X, IsClosed K → Measurable fun y => κ y K := by
    intro K hK
    let ap : ℕ → C(X, ℝ) := fun n =>
      ⟨fun z => ((hK.apprSeq n z : ℝ≥0) : ℝ),
        (NNReal.continuous_coe.comp (hK.apprSeq n).continuous)⟩
    have hb1 : ∀ n z, |ap n z| ≤ 1 := fun n z => by
      simp only [ap, ContinuousMap.coe_mk, NNReal.abs_eq]
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hK n z
    have hlim : ∀ y, Tendsto (fun n => ∫ z, ap n z ∂(κ y)) atTop (𝓝 ((κ y).real K)) := by
      intro y
      have := tendsto_integral_of_dominated_convergence (μ := κ y) (fun _ => (1 : ℝ))
        (F := fun n z => ap n z) (f := K.indicator (fun _ => (1 : ℝ)))
        (fun n => (ap n).continuous.aestronglyMeasurable)
        (integrable_const _)
        (fun n => Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hb1 n z)
        (Filter.Eventually.of_forall fun z => by
          have key := NNReal.tendsto_coe.2
            (tendsto_pi_nhds.1 (HasOuterApproxClosed.tendsto_apprSeq hK) z)
          by_cases hz : z ∈ K
          · simpa [hz, ap] using key
          · simpa [hz, ap] using key)
      simpa [integral_indicator hK.measurableSet, Measure.real] using this
    have hm : Measurable fun y => (κ y).real K :=
      measurable_of_tendsto_metrizable (fun n => hb (ap n) (hb1 n)) (tendsto_pi_nhds.2 hlim)
    have : (fun y => κ y K) = fun y => ENNReal.ofReal ((κ y).real K) := by
      funext y
      rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    rw [this]
    exact ENNReal.measurable_ofReal.comp hm
  refine Measurable.measure_of_isPiSystem (S := {s : Set X | IsClosed s}) ?_ isPiSystem_isClosed
    (fun s hs => hclosed s hs) (hclosed _ isClosed_univ)
  exact BorelSpace.measurable_eq.trans borel_eq_generateFrom_isClosed

/-- Finite Borel measures on a locally compact second countable Hausdorff space are determined by their
integrals against `C_c`. -/
lemma ext_of_integral_cc {m n : Measure X} [IsFiniteMeasure m] [IsFiniteMeasure n]
    (h : ∀ f : C_c(X, ℝ), ∫ x, f x ∂m = ∫ x, f x ∂n) : m = n :=
  Measure.ext_of_integral_eq_on_compactlySupported h

end MarkovTriple.Stochastic.R24
