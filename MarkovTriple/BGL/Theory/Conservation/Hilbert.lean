import Mathlib
import MarkovTriple.BGL.Analysis.Hilbert.Existence
import MarkovTriple.BGL.Analysis.Hilbert.Generator

/-!
# Hilbert-space lemmas for the mass-conservation theorem (BGL Thm 3.2.7 / 3.3.23)

For the Friedrichs semigroup `P_t` of a `FormData S`:
* `generator_symm`: the generator is symmetric on its domain;
* `semigroup_tendsto_fixed`: for every `u`, `P_t u` converges (as `t → ∞`) to a vector fixed by
  every `P_s` (elementary proof: `t ↦ ‖P_t u‖²` is nonincreasing and
  `‖P_t u − P_s u‖² = φ(t) + φ(s) − 2 φ((t+s)/2)`, `φ(t) = ‖P_t u‖²`);
* `fixed_mem_kernel`: a `P`-fixed vector lies in `𝒟(G)` with `G w = 0`.
-/

open MeasureTheory Filter Topology
open scoped NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.Hilbert.FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- The generator is symmetric. -/
theorem generator_symm {v w : H} (hv : v ∈ S.generator.domain) (hw : w ∈ S.generator.domain) :
    inner ℝ (S.generator ⟨v, hv⟩) w = inner ℝ v (S.generator ⟨w, hw⟩) := by
  have hv' := (S.generator_apply_eq_iff hv _).1 rfl
  have hw' := (S.generator_apply_eq_iff hw _).1 rfl
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp S.R_isSelfAdjoint
    (v - S.generator ⟨v, hv⟩) (w - S.generator ⟨w, hw⟩)
  change inner ℝ (S.R (v - S.generator ⟨v, hv⟩)) (w - S.generator ⟨w, hw⟩) =
    inner ℝ (v - S.generator ⟨v, hv⟩) (S.R (w - S.generator ⟨w, hw⟩)) at hs
  rw [hv', hw', inner_sub_left, inner_sub_right] at hs
  linear_combination hs

lemma semigroup_inner_comm (s t : ℝ≥0) (u : H) :
    inner ℝ (S.semigroup s u) (S.semigroup t u) = inner ℝ (S.semigroup (s + t) u) u := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (S.semigroup_isSelfAdjoint s)
    u (S.semigroup t u)
  change inner ℝ (S.semigroup s u) (S.semigroup t u) = inner ℝ u (S.semigroup s (S.semigroup t u))
    at hs
  rw [hs, S.semigroup_add, mul_apply_eq_comp]
  exact real_inner_comm _ _

/-- `φ(t) = ‖P_t u‖²`. -/
lemma sq_norm_semigroup (t : ℝ≥0) (u : H) :
    ‖S.semigroup t u‖ ^ 2 = inner ℝ (S.semigroup (t + t) u) u := by
  rw [← real_inner_self_eq_norm_sq, S.semigroup_inner_comm]

lemma norm_semigroup_antitone (u : H) : Antitone fun t : ℝ≥0 => ‖S.semigroup t u‖ := by
  intro s t hst
  obtain ⟨d, rfl⟩ : ∃ d, t = s + d := ⟨t - s, by rw [add_tsub_cancel_of_le hst]⟩
  have : S.semigroup (s + d) u = S.semigroup d (S.semigroup s u) := by
    rw [add_comm, S.semigroup_add]; rfl
  show ‖S.semigroup (s + d) u‖ ≤ ‖S.semigroup s u‖
  rw [this]
  exact ((S.semigroup d).le_opNorm _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (S.norm_semigroup_le d))

/-- For every `u`, `t ↦ P_t u` is Cauchy as `t → ∞`. -/
theorem cauchySeq_semigroup (u : H) : CauchySeq fun t : ℝ≥0 => S.semigroup t u := by
  set φ : ℝ≥0 → ℝ := fun t => ‖S.semigroup t u‖ ^ 2 with hφ
  have hφa : Antitone φ := fun s t hst =>
    pow_le_pow_left₀ (norm_nonneg _) (S.norm_semigroup_antitone u hst) 2
  have hbdd : BddBelow (Set.range φ) := ⟨0, by rintro _ ⟨t, rfl⟩; positivity⟩
  have hlim := tendsto_atTop_ciInf hφa hbdd
  set m := ⨅ t, φ t with hm
  have hge : ∀ t, m ≤ φ t := fun t => ciInf_le hbdd t
  rw [Metric.cauchySeq_iff]
  intro ε hε
  have hε2 : 0 < ε ^ 2 / 2 := by positivity
  obtain ⟨T0, hT0⟩ : ∃ T0, φ T0 < m + ε ^ 2 / 2 := by
    by_contra hcon
    push Not at hcon
    have : m + ε ^ 2 / 2 ≤ m := le_ciInf (fun t => by
      have := hcon t; linarith)
    linarith
  refine ⟨T0, fun s hs t ht => ?_⟩
  have hh : T0 ≤ (s + t) / 2 :=
    (le_div_iff₀ (by norm_num)).2 (by rw [mul_two]; exact add_le_add hs ht)
  have hhh : (s + t) / 2 + (s + t) / 2 = s + t := add_halves _
  have e1 : inner ℝ (S.semigroup s u) (S.semigroup t u) = φ ((s + t) / 2) := by
    rw [S.semigroup_inner_comm, hφ]
    show _ = ‖S.semigroup ((s + t) / 2) u‖ ^ 2
    rw [S.sq_norm_semigroup, hhh]
  have hsq : ‖S.semigroup s u - S.semigroup t u‖ ^ 2 < ε ^ 2 := by
    rw [norm_sub_sq_real, e1]
    have a1 : φ s < m + ε ^ 2 / 2 := lt_of_le_of_lt (hφa hs) hT0
    have a2 : φ t < m + ε ^ 2 / 2 := lt_of_le_of_lt (hφa ht) hT0
    have a3 := hge ((s + t) / 2)
    simp only [hφ] at a1 a2 a3
    linarith
  rw [dist_eq_norm]
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- **Convergence of `P_t u` as `t → ∞`** to a vector fixed by every `P_s`. -/
theorem exists_fixed_limit (u : H) :
    ∃ w : H, Tendsto (fun t : ℝ≥0 => S.semigroup t u) atTop (𝓝 w) ∧ ∀ s, S.semigroup s w = w := by
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete (S.cauchySeq_semigroup u)
  refine ⟨w, hw, fun s => ?_⟩
  have h1 : Tendsto (fun t : ℝ≥0 => S.semigroup s (S.semigroup t u)) atTop (𝓝 (S.semigroup s w)) :=
    ((S.semigroup s).continuous.tendsto w).comp hw
  have h2 : Tendsto (fun t : ℝ≥0 => S.semigroup (s + t) u) atTop (𝓝 w) :=
    hw.comp (tendsto_atTop_mono (fun t => le_add_self) tendsto_id)
  have e : (fun t : ℝ≥0 => S.semigroup s (S.semigroup t u)) = fun t => S.semigroup (s + t) u := by
    funext t; rw [S.semigroup_add]; rfl
  rw [e] at h1
  exact tendsto_nhds_unique h1 h2

/-- A `P`-fixed vector lies in `𝒟(G)` and `G w = 0`. -/
theorem fixed_mem_kernel {w : H} (hw : ∀ s, S.semigroup s w = w) :
    ∃ h : w ∈ S.generator.domain, S.generator ⟨w, h⟩ = 0 := by
  rw [S.tendsto_generator_iff]
  refine tendsto_const_nhds.congr (fun t => ?_)
  simp [hw t]

end MarkovTriple.Hilbert.FormData
