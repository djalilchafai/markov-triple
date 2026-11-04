import Mathlib
import MarkovTriple.Stochastic.R24.Feller

/-!
# Round 24 (C), part 4: extending the representation from `C_c` to `C_0 ∩ L²`, continuity of `x ↦ κ_s(x, h)`

* `fellerKernelInf_rep_C0`: for `h ∈ C_0(X) ∩ L²(μ)`, `P_s [h] = (x ↦ ∫ h dκ_s(x,·))` a.e.  (cut-offs `χ_n h → h` in `L²`;
  `P_s` is `L²`-continuous; `∫ χ_n h dκ_s(x) → ∫ h dκ_s(x)` for every `x`.)
* `continuous_integral_fellerKernelInf`: for `h ∈ C_0(X)`, `x ↦ ∫ h dκ_s(x,·)` is continuous: it is the uniform limit of
  `x ↦ Q_s(χ_n h)(x)` (since `κ_s(x, ·)` has mass `≤ 1` and `h` vanishes at infinity).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R23

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

omit [T.μ.IsOpenPosMeasure] in
/-- `ccL2 (χ_n h) → [h]` in `L²` for `h ∈ L²` continuous. -/
lemma tendsto_ccL2_cutMul (h : C(X, ℝ)) (hL : MemLp h 2 T.μ) :
    Tendsto (fun n => ccL2 T (cutMul n h)) atTop (𝓝 (hL.toLp h)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h0 := R23.tendsto_eLpNorm_compl (μ := T.μ) (cexh X) hL
  have h1 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h0
  simp only [ENNReal.toReal_zero] at h1
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h1
  simp only [Function.comp, Lp.norm_def]
  refine ENNReal.toReal_mono ?_ ?_
  · exact (hL.indicator (R23.measurableSet_K (cexh X) n).compl).eLpNorm_lt_top.ne
  · refine eLpNorm_mono_ae (Lp.aestronglyMeasurable _) ?_
    filter_upwards [Lp.coeFn_sub (ccL2 T (cutMul n h)) (hL.toLp h), coeFn_ccL2 (T := T) (cutMul n h),
      hL.coeFn_toLp] with x h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3]
    by_cases hx : x ∈ cexh X n
    · have : cutoff X n x = 1 := cutoff_eq_one n hx
      simp [this, hx]
    · have hx' : x ∈ (cexh X n)ᶜ := hx
      have hc := cutoff_mem n x
      rw [Set.indicator_of_mem hx']
      simp only [cutMul_apply, Real.norm_eq_abs]
      have : cutoff X n x * h x - h x = (cutoff X n x - 1) * h x := by ring
      rw [this, abs_mul]
      have : |cutoff X n x - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hc.1, hc.2]
      calc |cutoff X n x - 1| * |h x| ≤ 1 * |h x| := mul_le_mul_of_nonneg_right this (abs_nonneg _)
        _ = |h x| := one_mul _

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
lemma bounded_C0 (h : C₀(X, ℝ)) : ∃ C, ∀ x, |h x| ≤ C :=
  ⟨‖h.toBCF‖, fun x => by simpa [Real.norm_eq_abs] using h.toBCF.norm_coe_le_norm x⟩

/-- **Representation on `C_0 ∩ L²`**: `P_s [h] = (x ↦ ∫ h dκ_s(x,·))` a.e. -/
theorem fellerKernelInf_rep_C0 (s : ℝ≥0) (h : C₀(X, ℝ)) (hL : MemLp h 2 T.μ) :
    (T.semigroup s (hL.toLp h) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, h y ∂(fellerKernelInf hF s x) := by
  obtain ⟨C, hC⟩ := bounded_C0 h
  let hc : C(X, ℝ) := h.toContinuousMap
  have hL' : MemLp hc 2 T.μ := hL
  have hlim := tendsto_ccL2_cutMul hc hL'
  have hP : Tendsto (fun n => T.semigroup s (ccL2 T (cutMul n hc))) atTop
      (𝓝 (T.semigroup s (hL'.toLp hc))) := ((T.semigroup s).continuous.tendsto _).comp hlim
  have hm := tendstoInMeasure_of_tendsto_Lp (p := 2) hP
  obtain ⟨ns, hns, hae⟩ := hm.exists_seq_tendsto_ae
  have hpt : ∀ x, Tendsto (fun n => ∫ y, cutMul n hc y ∂(fellerKernelInf hF s x)) atTop
      (𝓝 (∫ y, h y ∂(fellerKernelInf hF s x))) := fun x =>
    tendsto_integral_cutMul (fellerKernelInf hF s x) hc (C := C) hC
  have hrep : ∀ n, (T.semigroup s (ccL2 T (cutMul n hc)) : X → ℝ) =ᵐ[T.μ]
      fun x => ∫ y, cutMul n hc y ∂(fellerKernelInf hF s x) := fun n => by
    filter_upwards [Qop_ae hF s (cutMul n hc)] with x hx
    rw [hx, integral_fellerKernelInf]
  have hall : ∀ᵐ x ∂T.μ, ∀ n, (T.semigroup s (ccL2 T (cutMul n hc)) : X → ℝ) x
      = ∫ y, cutMul n hc y ∂(fellerKernelInf hF s x) := ae_all_iff.2 hrep
  filter_upwards [hae, hall] with x h1 h2
  have h3 : Tendsto (fun i => (T.semigroup s (ccL2 T (cutMul (ns i) hc)) : X → ℝ) x) atTop
      (𝓝 (∫ y, h y ∂(fellerKernelInf hF s x))) := by
    simp_rw [h2]
    exact (hpt x).comp hns.tendsto_atTop
  exact tendsto_nhds_unique h1 h3

/-- **Continuity**: for `h ∈ C_0(X)`, `x ↦ ∫ h dκ_s(x,·)` is continuous. -/
theorem continuous_integral_fellerKernelInf (s : ℝ≥0) (h : C₀(X, ℝ)) :
    Continuous fun x => ∫ y, h y ∂(fellerKernelInf hF s x) := by
  obtain ⟨C, hC⟩ := bounded_C0 h
  let hc : C(X, ℝ) := h.toContinuousMap
  have hcont : ∀ n, Continuous fun x => ∫ y, cutMul n hc y ∂(fellerKernelInf hF s x) := fun n => by
    simp_rw [integral_fellerKernelInf]
    exact (Qop hF s (cutMul n hc)).continuous
  refine TendstoUniformly.continuous (F := fun n x => ∫ y, cutMul n hc y ∂(fellerKernelInf hF s x))
    (p := atTop) ?_ (Filter.Eventually.of_forall hcont).frequently
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  have hz : Tendsto h (cocompact X) (𝓝 0) := h.zero_at_infty'
  have hev : ∀ᶠ y in cocompact X, |h y| < ε / 2 := by
    have := (Metric.tendsto_nhds.1 hz) (ε / 2) (by positivity)
    filter_upwards [this] with y hy
    simpa [Real.dist_eq] using hy
  obtain ⟨K, hK, hKsub⟩ := mem_cocompact.1 hev
  filter_upwards [cutoff_eventually_one_of_isCompact hK] with n hn x
  have hpt : ∀ y, |h y - cutMul n hc y| ≤ ε / 2 := by
    intro y
    by_cases hy : y ∈ K
    · rw [show cutMul n hc y = h y by rw [cutMul_apply, hn y hy, one_mul]; rfl]
      simp only [sub_self, abs_zero]; positivity
    · have h1 : |h y| < ε / 2 := hKsub (by simpa using hy)
      have hc' := cutoff_mem n y
      have : h y - cutMul n hc y = (1 - cutoff X n y) * h y := by
        simp only [cutMul_apply, hc]; simp; ring
      rw [this, abs_mul]
      have h2 : |1 - cutoff X n y| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hc'.1, hc'.2]
      calc |1 - cutoff X n y| * |h y| ≤ 1 * |h y| := mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
        _ ≤ ε / 2 := by rw [one_mul]; exact h1.le
  have hint1 : Integrable (fun y => h y) (fellerKernelInf hF s x) :=
    Integrable.of_bound h.continuous.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  have hint2 : Integrable (fun y => cutMul n hc y) (fellerKernelInf hF s x) :=
    (cutMul n hc).continuous.integrable_of_hasCompactSupport (cutMul n hc).hasCompactSupport
  have hdiff : ∫ y, h y ∂(fellerKernelInf hF s x) - ∫ y, cutMul n hc y ∂(fellerKernelInf hF s x)
      = ∫ y, (h y - cutMul n hc y) ∂(fellerKernelInf hF s x) := (integral_sub hint1 hint2).symm
  rw [Real.dist_eq, hdiff]
  have hb := abs_integral_le_of_bound (fellerKernelInf hF s x) (g := fun y => h y - cutMul n hc y)
    (C := ε / 2) hpt
  have hmass : (fellerKernelInf hF s x).real Set.univ ≤ 1 := by
    have := fellerKernelInf_subMarkov hF s x
    simpa [Measure.real] using ENNReal.toReal_mono ENNReal.one_ne_top this
  have hε2 : |ε / 2| = ε / 2 := abs_of_pos (by positivity)
  rw [hε2] at hb
  have : ε / 2 * (fellerKernelInf hF s x).real Set.univ ≤ ε / 2 * 1 := by
    gcongr
  linarith

end MarkovTriple.Stochastic.R24
