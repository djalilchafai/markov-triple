import Mathlib
import MarkovTriple.BGL.Frozen.DiffusionTriple
import MarkovTriple.BGL.Semigroup.Mass

/-!
# Round 32 (B2), part 1: positivity detection for `L²` functions (B1)

BGL's F2 (positivity detection) only tests elements of the extended algebra `𝒜`.  For the `L²`-class `P_s(√Γ(P_{t-s} f))`, which has
no `𝒜`-representative, we need the following replacement, valid for every `DiffusionTriple`: if `u ∈ L²` and `∫ g u ≥ 0` for every
`0 ≤ g ∈ 𝒜₀`, then `u ≥ 0` a.e.  Proof: `𝒜₀` is dense in `L²` (D2); for `g ∈ 𝒜₀`, `φ_ε(g) = √(g²+ε²) - ε ∈ 𝒜₀` (D2 `comp_mem`) is `≥ 0`
and tends to `|g|` (`ε → 0`, dominated convergence), so `∫ |g| u ≥ 0`; then approximate `u⁻` in `L²` by `g`, `|g| → u⁻`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Stochastic.R32B2

open MarkovTriple.BGL

/-- `φ_ε(y) = √(y²+ε²) - ε` -/
noncomputable def phiE (ε : ℝ) (y : ℝ) : ℝ := Real.sqrt (y ^ 2 + ε ^ 2) - ε

lemma phiE_smooth {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (phiE ε) := by
  unfold phiE
  refine ContDiff.sub ?_ contDiff_const
  refine ContDiff.sqrt (by fun_prop) (fun y => ?_)
  positivity

lemma phiE_zero {ε : ℝ} (hε : 0 < ε) : phiE ε 0 = 0 := by
  simp [phiE, Real.sqrt_sq hε.le]

lemma phiE_nonneg (ε y : ℝ) : 0 ≤ phiE ε y := by
  unfold phiE
  have : ε ≤ Real.sqrt (y ^ 2 + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg y])
  linarith

lemma phiE_le {ε : ℝ} (_hε : 0 < ε) (y : ℝ) : phiE ε y ≤ |y| := by
  unfold phiE
  have : Real.sqrt (y ^ 2 + ε ^ 2) ≤ |y| + ε := by
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_abs y, abs_nonneg y]
  linarith

lemma phiE_tendsto (y : ℝ) : Tendsto (fun n : ℕ => phiE (1 / ((n : ℝ) + 1)) y) atTop (𝓝 |y|) := by
  have hc : Continuous fun ε : ℝ => Real.sqrt (y ^ 2 + ε ^ 2) - ε := by fun_prop
  have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have h1 : Tendsto (fun ε : ℝ => Real.sqrt (y ^ 2 + ε ^ 2) - ε) (𝓝 0) (𝓝 |y|) := by
    simpa [Real.sqrt_sq_eq_abs] using hc.tendsto 0
  exact h1.comp h0

/-- for `g ∈ 𝒜₀`: `∫ |g| u ≥ 0` -/
lemma abs_integral_nonneg {E : Type*} [MeasurableSpace E] (D : DiffusionTriple E) {u : E → ℝ}
    (hu : MemLp u 2 D.μ) (h : ∀ g ∈ D.A₀, 0 ≤ᵐ[D.μ] g → 0 ≤ ∫ x, g x * u x ∂D.μ)
    {g : E → ℝ} (hg : g ∈ D.A₀) : 0 ≤ ∫ x, |g x| * u x ∂D.μ := by
  have hgL : MemLp g 2 D.μ := D.memLp g hg 2 (by norm_num) (by simp)
  have hint : Integrable (fun x => |g x| * u x) D.μ := by
    have := hgL.norm.integrable_mul hu
    refine this.congr (Eventually.of_forall fun x => ?_)
    simp
  refine ge_of_tendsto (x := (atTop : Filter ℕ)) (f := fun n : ℕ => ∫ x, phiE (1 / ((n : ℝ) + 1)) (g x) * u x ∂D.μ) ?_ ?_
  · refine tendsto_integral_of_dominated_convergence (fun x => |g x| * |u x|) ?_ ?_ ?_ ?_
    · intro n
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hm : Measurable (fun x => phiE (1 / ((n : ℝ) + 1)) (g x)) :=
        (phiE_smooth hn).continuous.measurable.comp (D.measurable g hg)
      exact (hm.aestronglyMeasurable.mul hu.aestronglyMeasurable)
    · exact (hgL.norm.integrable_mul hu.norm).congr (Eventually.of_forall fun x => by simp)
    · intro n
      refine Eventually.of_forall fun x => ?_
      have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (phiE_nonneg _ _)]
      exact mul_le_mul_of_nonneg_right (phiE_le hn _) (abs_nonneg _)
    · exact Eventually.of_forall fun x => (phiE_tendsto (g x)).mul_const _
  · refine Eventually.of_forall fun n => ?_
    have hn : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hmem : (fun x => phiE (1 / ((n : ℝ) + 1)) (g x)) ∈ D.A₀ :=
      D.comp_mem 1 (fun v => phiE (1 / ((n : ℝ) + 1)) (v 0))
        ((phiE_smooth hn).comp (contDiff_apply ℝ ℝ 0)) (phiE_zero hn) (fun _ => g) (fun _ => hg)
    exact h _ hmem (Eventually.of_forall fun x => phiE_nonneg _ _)

/-- **B1 (frozen statement).** positivity detection in `L²` -/
theorem pos_detect_L2 {E : Type*} [MeasurableSpace E] (D : DiffusionTriple E) {u : E → ℝ}
    (hu : MemLp u 2 D.μ) (h : ∀ g ∈ D.A₀, 0 ≤ᵐ[D.μ] g → 0 ≤ ∫ x, g x * u x ∂D.μ) :
    0 ≤ᵐ[D.μ] u := by
  set v : E → ℝ := fun x => max (-u x) 0 with hv
  have hvL : MemLp v 2 D.μ := hu.neg.pos_part
  have hv0 : ∀ x, 0 ≤ v x := fun x => le_max_right _ _
  have hvu : ∀ x, u x * v x = -(v x) ^ 2 := by
    intro x
    simp only [hv]
    rcases le_total 0 (u x) with h1 | h1
    · have : max (-u x) 0 = 0 := max_eq_right (by linarith)
      rw [this]; ring
    · have : max (-u x) 0 = -u x := max_eq_left (by linarith)
      rw [this]; ring
  set U : Lp ℝ 2 D.μ := hu.toLp u with hU
  set V : Lp ℝ 2 D.μ := hvL.toLp v with hV
  have hUV : inner ℝ U V = -‖V‖ ^ 2 := by
    rw [L2_inner_eq]
    have e : ∫ x, U x * V x ∂D.μ = ∫ x, -(v x) ^ 2 ∂D.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hu.coeFn_toLp, hvL.coeFn_toLp] with x h1 h2
      rw [h1, h2, hvu]
    have e2 : ‖V‖ ^ 2 = ∫ x, (v x) ^ 2 ∂D.μ := by
      rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
      refine integral_congr_ae ?_
      filter_upwards [hvL.coeFn_toLp] with x h2
      rw [h2]; ring
    rw [e, e2, integral_neg]
  have key : ∀ δ : ℝ, 0 < δ → ‖V‖ ^ 2 ≤ ‖U‖ * δ := by
    intro δ hδ
    obtain ⟨w, ⟨g, hg, hwg⟩, hw⟩ := Metric.mem_closure_iff.1 ((D.dense 2 ⟨by norm_num⟩ (by simp)) V) δ hδ
    have hgL : MemLp g 2 D.μ := D.memLp g hg 2 (by norm_num) (by simp)
    set W : Lp ℝ 2 D.μ := (hgL.norm).toLp (fun x => ‖g x‖) with hW
    have h1 : 0 ≤ inner ℝ U W := by
      rw [L2_inner_eq]
      have e : ∫ x, U x * W x ∂D.μ = ∫ x, |g x| * u x ∂D.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hu.coeFn_toLp, (hgL.norm).coeFn_toLp] with x h1 h2
        rw [h1, h2, Real.norm_eq_abs, mul_comm]
      rw [e]
      exact abs_integral_nonneg D hu h hg
    have h2 : inner ℝ U W = inner ℝ U V + inner ℝ U (W - V) := by
      rw [← inner_add_right]; simp
    have h3 : inner ℝ U (W - V) ≤ ‖U‖ * ‖W - V‖ := real_inner_le_norm _ _
    have h4 : ‖W - V‖ ≤ ‖w - V‖ := by
      refine Lp.norm_le_norm_of_ae_le ?_
      filter_upwards [Lp.coeFn_sub W V, Lp.coeFn_sub w V, (hgL.norm).coeFn_toLp, hvL.coeFn_toLp, hwg] with x a b c d e
      rw [a, b]
      simp only [Pi.sub_apply, Real.norm_eq_abs]
      rw [c, d, e, Real.norm_eq_abs]
      have := abs_abs_sub_abs_le_abs_sub (g x) (v x)
      rwa [abs_of_nonneg (hv0 x)] at this
    rw [dist_comm, dist_eq_norm] at hw
    have hU0 := norm_nonneg U
    nlinarith [mul_le_mul_of_nonneg_left (h4.trans hw.le) hU0]
  have hV0 : ‖V‖ ^ 2 ≤ 0 := by
    by_contra hlt
    push Not at hlt
    have hpos : 0 < ‖U‖ + 1 := by positivity
    have := key (‖V‖ ^ 2 / (2 * (‖U‖ + 1))) (by positivity)
    have h5 : ‖U‖ * (‖V‖ ^ 2 / (2 * (‖U‖ + 1))) < ‖V‖ ^ 2 := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg U]
    linarith
  have hV1 : V = 0 := by
    have : ‖V‖ = 0 := by nlinarith [norm_nonneg V]
    exact norm_eq_zero.1 this
  have hv00 : v =ᵐ[D.μ] 0 := by
    filter_upwards [hvL.coeFn_toLp, Lp.coeFn_zero ℝ 2 D.μ] with x h1 h2
    have : V x = 0 := by rw [hV1]; exact h2
    rw [← h1]; simpa using this
  filter_upwards [hv00] with x hx
  simp only [hv, Pi.zero_apply] at hx ⊢
  by_contra hlt
  push Not at hlt
  have : max (-u x) 0 = -u x := max_eq_left (by linarith)
  rw [this] at hx
  linarith

end MarkovTriple.Stochastic.R32B2
