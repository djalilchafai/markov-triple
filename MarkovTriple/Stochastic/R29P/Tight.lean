import Mathlib
import MarkovTriple.Stochastic.R27.Mass

/-!
# Round 29 (P), part 1: pointwise mass one for Feller + S11 is equivalent to local tightness

Statements: `STATEMENTS_R29_P.md` (P1-P4).  `m_t(x₀) = κ_t(x₀, X) = 1` holds iff no mass escapes to infinity for the starting points `y → x₀`
(for `μ`-almost every `y`, equivalently for every `y`).  So a deficit point is exactly a point near which the Feller kernels lose
mass at infinity; in particular a deficit point needs `X` non-compact.  This does NOT decide whether a deficit point exists.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R29P

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R23
  MarkovTriple.Stochastic.R25

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

section Real

variable {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

include hF in
/-- real-valued core of P1 -/
theorem tight_real_of_univ_eq_one (t : ℝ≥0) (x₀ : X) (h : fellerKernelInf hF t x₀ Set.univ = 1)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ K : Set X, IsCompact K ∧ ∃ U ∈ 𝓝 x₀, ∀ y ∈ U, 1 - δ ≤ (fellerKernelInf hF t y K).toReal := by
  -- a compact set `K₀` carrying almost all the mass of `κ_t(x₀, ·)`
  have hfin : ∀ y, fellerKernelInf hF t y Set.univ ≠ ∞ := fun y =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (fellerKernelInf_subMarkov hF t y)
  have hlt : ENNReal.ofReal (1 - δ / 2) < fellerKernelInf hF t x₀ Set.univ := by
    rw [h, ← ENNReal.ofReal_one]
    exact (ENNReal.ofReal_lt_ofReal_iff one_pos).2 (by linarith)
  rw [fellerKernelInf_apply, MeasurableSet.univ.measure_eq_iSup_isCompact] at hlt
  simp only [lt_iSup_iff] at hlt
  obtain ⟨K₀, -, hK₀, hK₀lt⟩ := hlt
  rw [← fellerKernelInf_apply] at hK₀lt
  obtain ⟨f, hf1, hf2, -, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK₀ isOpen_univ
    (Set.subset_univ K₀)
  let f' : C_c(X, ℝ) := ⟨f, hasCompactSupport_def.mpr hf2⟩
  have hint : ∀ y, Integrable f' (fellerKernelInf hF t y) := fun y =>
    f'.continuous.integrable_of_hasCompactSupport f'.hasCompactSupport
  -- `Q_t f (x₀) ≥ κ_t(x₀, K₀) > 1 - δ/2`
  have hK₀meas : MeasurableSet K₀ := hK₀.isClosed.measurableSet
  have hlow : (fellerKernelInf hF t x₀ K₀).toReal ≤ Qop hF t f' x₀ := by
    rw [← integral_fellerKernelInf hF t x₀ f']
    have h1 : ∫ y, K₀.indicator (fun _ => (1 : ℝ)) y ∂(fellerKernelInf hF t x₀) ≤
        ∫ y, f' y ∂(fellerKernelInf hF t x₀) := by
      refine integral_mono (integrable_const _ |>.indicator hK₀meas) (hint x₀) fun y => ?_
      by_cases hy : y ∈ K₀
      · simp [hy, hf1 hy, f']
      · simp only [hy, not_false_eq_true, Set.indicator_of_notMem]
        exact (hf3 y).1
    refine le_trans (le_of_eq ?_) h1
    rw [integral_indicator_const _ hK₀meas]
    simp [Measure.real]
  have hK₀real : 1 - δ / 2 < (fellerKernelInf hF t x₀ K₀).toReal := by
    have := ENNReal.toReal_strict_mono (ne_top_of_le_ne_top (hfin x₀)
      (measure_mono (Set.subset_univ K₀))) hK₀lt
    rwa [ENNReal.toReal_ofReal (by linarith)] at this
  -- continuity of `Q_t f` near `x₀`
  have hcont := (Qop hF t f').continuous.continuousAt (x := x₀)
  have hev : ∀ᶠ y in 𝓝 x₀, 1 - δ < Qop hF t f' y := by
    have : (1 - δ) < Qop hF t f' x₀ := by linarith
    exact hcont.eventually (lt_mem_nhds this)
  refine ⟨tsupport f, hf2, _, hev, fun y hy => ?_⟩
  have hsm : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have h1 : Qop hF t f' y ≤ (fellerKernelInf hF t y (tsupport f)).toReal := by
    rw [← integral_fellerKernelInf hF t y f']
    have : ∫ z, f' z ∂(fellerKernelInf hF t y) ≤
        ∫ z, (tsupport f).indicator (fun _ => (1 : ℝ)) z ∂(fellerKernelInf hF t y) := by
      refine integral_mono (hint y) (integrable_const _ |>.indicator hsm) fun z => ?_
      by_cases hz : z ∈ tsupport f
      · simp [hz, (hf3 z).2, f']
      · have : f z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp [hz, this, f']
    refine this.trans (le_of_eq ?_)
    rw [integral_indicator_const _ hsm]
    simp [Measure.real]
  have hy' : 1 - δ < Qop hF t f' y := hy
  linarith

end Real

section Tight

variable (S : StandardTriple X) [IsFiniteMeasureOnCompacts S.μ] [S.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 S.toDiffusionTriple)

include hF in
/-- real-valued core of P2: a.e.-local tightness at `x₀` bounds the mass at `x₀` from below. -/
theorem le_univ_of_tight_real (t : ℝ≥0) (x₀ : X) {δ : ℝ} {K : Set X} (hK : IsCompact K) {U : Set X}
    (hU : U ∈ 𝓝 x₀) (hae : ∀ᵐ y ∂S.μ, y ∈ U → 1 - δ ≤ (fellerKernelInf hF t y K).toReal) :
    1 - δ ≤ (fellerKernelInf hF t x₀ Set.univ).toReal := by
  obtain ⟨f, hf1, hf2, -, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ
    (Set.subset_univ K)
  let f' : C_c(X, ℝ) := ⟨f, hasCompactSupport_def.mpr hf2⟩
  have hint : ∀ y, Integrable f' (fellerKernelInf hF t y) := fun y =>
    f'.continuous.integrable_of_hasCompactSupport f'.hasCompactSupport
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  -- `Q_t f (y) ≥ κ_t(y, K)` for every `y`
  have hge : ∀ y, (fellerKernelInf hF t y K).toReal ≤ Qop hF t f' y := by
    intro y
    rw [← integral_fellerKernelInf hF t y f']
    have h1 : ∫ z, K.indicator (fun _ => (1 : ℝ)) z ∂(fellerKernelInf hF t y) ≤
        ∫ z, f' z ∂(fellerKernelInf hF t y) := by
      refine integral_mono (integrable_const _ |>.indicator hKm) (hint y) fun z => ?_
      by_cases hz : z ∈ K
      · simp [hz, hf1 hz, f']
      · simp only [hz, not_false_eq_true, Set.indicator_of_notMem]
        exact (hf3 z).1
    refine le_trans (le_of_eq ?_) h1
    rw [integral_indicator_const _ hKm]
    simp [Measure.real]
  -- the good points accumulate at `x₀` (open positivity of `μ`)
  have hmem : x₀ ∈ closure {y | 1 - δ ≤ Qop hF t f' y} := by
    rw [mem_closure_iff]
    intro V hV hxV
    have hW : IsOpen (V ∩ interior U) := hV.inter isOpen_interior
    have hxW : x₀ ∈ V ∩ interior U := ⟨hxV, mem_interior_iff_mem_nhds.2 hU⟩
    have hpos : 0 < S.μ (V ∩ interior U) := hW.measure_pos S.μ ⟨x₀, hxW⟩
    by_contra hne
    refine hpos.ne' (measure_mono_null (fun y hy => ?_) (ae_iff.1 hae))
    simp only [Set.mem_ofPred_eq, not_imp, not_le]
    refine ⟨interior_subset hy.2, ?_⟩
    by_contra hle
    exact hne ⟨y, hy.1, by
      simpa using (le_of_not_gt hle).trans (hge y)⟩
  have hcl : IsClosed {y | 1 - δ ≤ Qop hF t f' y} :=
    isClosed_le continuous_const (Qop hF t f').continuous
  have h2 : 1 - δ ≤ Qop hF t f' x₀ := hcl.closure_subset_iff.2 (fun _ h => h) hmem
  refine h2.trans ?_
  rw [← integral_fellerKernelInf hF t x₀ f']
  have : ∫ z, f' z ∂(fellerKernelInf hF t x₀) ≤ ∫ z, (1 : ℝ) ∂(fellerKernelInf hF t x₀) :=
    integral_mono (hint x₀) (integrable_const _) fun z => (hf3 z).2
  refine this.trans (le_of_eq ?_)
  simp [Measure.real]

end Tight

section Frozen

lemma exists_delta {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ENNReal.ofReal δ ≤ ε := by
  refine ⟨(min ε 1).toReal, ?_, ?_, ?_⟩
  · exact ENNReal.toReal_pos (lt_min hε one_pos).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))
  · have := ENNReal.toReal_mono ENNReal.one_ne_top (min_le_right ε 1)
    simpa using this
  · rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
    exact min_le_left _ _

lemma sub_ofReal_eq {δ : ℝ} (hδ0 : 0 ≤ δ) : (1 : ℝ≥0∞) - ENNReal.ofReal δ = ENNReal.ofReal (1 - δ) := by
  rw [ENNReal.ofReal_sub 1 hδ0]
  simp

variable {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

include hF in
/-- **P1** (no S11): mass one at `x₀` gives local tightness at `x₀`, for every nearby starting point. -/
theorem fellerKernelInf_tight_of_univ_eq_one (t : ℝ≥0) (x₀ : X)
    (h : fellerKernelInf hF t x₀ Set.univ = 1) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ K : Set X, IsCompact K ∧ ∃ U ∈ 𝓝 x₀, ∀ y ∈ U, 1 - ε ≤ fellerKernelInf hF t y K := by
  obtain ⟨δ, hδ, hδ1, hδε⟩ := exists_delta hε
  obtain ⟨K, hK, U, hU, hy⟩ := tight_real_of_univ_eq_one hF t x₀ h hδ hδ1
  refine ⟨K, hK, U, hU, fun y hyU => ?_⟩
  have hfin : fellerKernelInf hF t y K ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    ((measure_mono (Set.subset_univ K)).trans (fellerKernelInf_subMarkov hF t y))
  calc 1 - ε ≤ 1 - ENNReal.ofReal δ := tsub_le_tsub_left hδε 1
    _ = ENNReal.ofReal (1 - δ) := sub_ofReal_eq hδ.le
    _ ≤ _ := ENNReal.ofReal_le_of_le_toReal (hy y hyU)

variable (S : StandardTriple X) [IsFiniteMeasureOnCompacts S.μ] [S.μ.IsOpenPosMeasure]
  (hS : IsFellerC0 S.toDiffusionTriple)

include hS in
/-- **P2** (S11 not needed here, only open positivity): a.e.-local tightness at `x₀` gives mass one at `x₀`. -/
theorem fellerKernelInf_univ_eq_one_of_tight (t : ℝ≥0) (x₀ : X)
    (htight : ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∃ U ∈ 𝓝 x₀,
      ∀ᵐ y ∂S.μ, y ∈ U → 1 - ε ≤ fellerKernelInf hS t y K) :
    fellerKernelInf hS t x₀ Set.univ = 1 := by
  have hle := fellerKernelInf_subMarkov hS t x₀
  have hfin : fellerKernelInf hS t x₀ Set.univ ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hle
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have hr : (fellerKernelInf hS t x₀ Set.univ).toReal < 1 := by
    simpa using ENNReal.toReal_strict_mono ENNReal.one_ne_top hlt
  have hnn : 0 ≤ (fellerKernelInf hS t x₀ Set.univ).toReal := ENNReal.toReal_nonneg
  set δ := (1 - (fellerKernelInf hS t x₀ Set.univ).toReal) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hδ1 : δ ≤ 1 := by rw [hδdef]; linarith
  obtain ⟨K, hK, U, hU, hae⟩ := htight (ENNReal.ofReal δ) (ENNReal.ofReal_pos.2 hδ)
  have hae' : ∀ᵐ y ∂S.μ, y ∈ U → 1 - δ ≤ (fellerKernelInf hS t y K).toReal := by
    filter_upwards [hae] with y hy hyU
    have hfin' : fellerKernelInf hS t y K ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
      ((measure_mono (Set.subset_univ K)).trans (fellerKernelInf_subMarkov hS t y))
    have := hy hyU
    rw [sub_ofReal_eq hδ.le] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hfin').1 this
  have := le_univ_of_tight_real S hS t x₀ hK hU hae'
  rw [hδdef] at this
  linarith

include hS in
/-- **P3**: mass one at `x₀` iff the Feller kernels are tight near `x₀` (almost every starting point). -/
theorem fellerKernelInf_univ_eq_one_iff_tight (t : ℝ≥0) (x₀ : X) :
    fellerKernelInf hS t x₀ Set.univ = 1 ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ K : Set X, IsCompact K ∧ ∃ U ∈ 𝓝 x₀,
        ∀ᵐ y ∂S.μ, y ∈ U → 1 - ε ≤ fellerKernelInf hS t y K := by
  refine ⟨fun h ε hε => ?_, fellerKernelInf_univ_eq_one_of_tight S hS t x₀⟩
  obtain ⟨K, hK, U, hU, hy⟩ := fellerKernelInf_tight_of_univ_eq_one hS t x₀ h ε hε
  exact ⟨K, hK, U, hU, Filter.Eventually.of_forall hy⟩

include hS in
/-- **P4a**: on a compact space the mass is one at every point. -/
theorem fellerKernelInf_univ_eq_one_of_compactSpace [CompactSpace X] (t : ℝ≥0) (x : X) :
    fellerKernelInf hS t x Set.univ = 1 := by
  refine fellerKernelInf_univ_eq_one_of_tight S hS t x fun ε hε => ⟨Set.univ, isCompact_univ, Set.univ,
    Filter.univ_mem, ?_⟩
  filter_upwards [fellerKernelInf_univ_ae S hS t] with y hy _
  rw [hy]
  exact tsub_le_self

include hS in
/-- **P4b**: a point with a mass deficit forces `X` to be non-compact. -/
theorem fellerKernelInf_deficit_noncompact (t : ℝ≥0) (x : X)
    (h : fellerKernelInf hS t x Set.univ ≠ 1) : ¬ CompactSpace X := fun _ =>
  h (fellerKernelInf_univ_eq_one_of_compactSpace S hS t x)

end Frozen

end MarkovTriple.Stochastic.R29P
