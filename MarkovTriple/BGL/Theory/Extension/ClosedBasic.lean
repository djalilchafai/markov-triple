import Mathlib
import MarkovTriple.BGL.Theory.Extension.Main

/-!
# `Γ` on `𝒟(ℰ)` (BGL Prop. 3.1.5 / (3.1.10) extension; the input of Props 3.3.5 (ii), 3.3.6 (ii))

Generic machinery (bounded bilinear maps defined on `𝒜₀` extend along Cauchy sequences), the `L¹`
Cauchy–Schwarz inequality, and `FullTriple.gammaE : 𝒟(ℰ) × 𝒟(ℰ) → L¹(μ)`, the `L¹`-limit of `Γ(a_k, b_k)` along any
form-convergent sequences of test functions.  All statements are documented in `Extension/STATEMENTS_R14.md` (S1).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

section Generic

/-- **`L¹` Cauchy–Schwarz.**  If `c² ≤ a b` a.e. with `a, b ≥ 0` integrable, then `c` is integrable (when
a.e.-strongly measurable) and `∫|c| ≤ √(∫a) √(∫b)`. -/
lemma int_abs_le_sqrt {E : Type*} [MeasurableSpace E] {μ : Measure E} {a b c : E → ℝ}
    (ha : Integrable a μ) (hb : Integrable b μ) (hc : AEStronglyMeasurable c μ)
    (ha0 : 0 ≤ᵐ[μ] a) (hb0 : 0 ≤ᵐ[μ] b) (h : ∀ᵐ x ∂μ, c x ^ 2 ≤ a x * b x) :
    Integrable c μ ∧ ∫ x, |c x| ∂μ ≤ √(∫ x, a x ∂μ) * √(∫ x, b x ∂μ) := by
  have key : ∀ t : ℝ, 0 < t → ∀ᵐ x ∂μ, |c x| ≤ (t * a x + b x / t) / 2 := by
    intro t ht
    filter_upwards [h, ha0, hb0] with x h1 h2 h3
    have := FullTriple.two_abs_le (c := c x) h2 h3 ht h1
    linarith
  have hint : ∀ t : ℝ, 0 < t → Integrable (fun x => (t * a x + b x / t) / 2) μ := fun t ht =>
    ((ha.const_mul t).add (hb.div_const t)).div_const 2
  have hI : Integrable c μ := by
    refine (hint 1 one_pos).mono' hc ?_
    filter_upwards [key 1 one_pos] with x hx
    simpa using hx
  have hA : 0 ≤ ∫ x, a x ∂μ := integral_nonneg_of_ae ha0
  have hB : 0 ≤ ∫ x, b x ∂μ := integral_nonneg_of_ae hb0
  refine ⟨hI, ?_⟩
  have hδ : ∀ δ : ℝ, 0 < δ → ∫ x, |c x| ∂μ ≤ √(∫ x, a x ∂μ + δ) * √(∫ x, b x ∂μ + δ) := by
    intro δ hδ
    set A := ∫ x, a x ∂μ
    set B := ∫ x, b x ∂μ
    have hAδ : 0 < A + δ := by linarith
    have hBδ : 0 < B + δ := by linarith
    set t : ℝ := √(B + δ) / √(A + δ) with ht
    have pA : 0 < √(A + δ) := Real.sqrt_pos.2 hAδ
    have pB : 0 < √(B + δ) := Real.sqrt_pos.2 hBδ
    have htpos : 0 < t := by positivity
    have h1 : ∫ x, |c x| ∂μ ≤ ∫ x, (t * a x + b x / t) / 2 ∂μ :=
      integral_mono_ae hI.abs (hint t htpos) (key t htpos)
    have h2 : ∫ x, (t * a x + b x / t) / 2 ∂μ = (t * A + B / t) / 2 := by
      rw [integral_div, integral_add (ha.const_mul t) (hb.div_const t), integral_const_mul,
        integral_div]
    have sA := Real.sq_sqrt hAδ.le
    have sB := Real.sq_sqrt hBδ.le
    have h3 : (t * A + B / t) / 2 ≤ √(A + δ) * √(B + δ) := by
      have e : t * (A + δ) + (B + δ) / t = 2 * (√(A + δ) * √(B + δ)) := by
        rw [ht]; field_simp; rw [sA, sB]; ring
      have : t * A + B / t ≤ t * (A + δ) + (B + δ) / t := by
        have h0 : 0 ≤ t * δ + δ / t := by positivity
        have h4 : (B + δ) / t = B / t + δ / t := add_div _ _ _
        have h5 : t * (A + δ) = t * A + t * δ := mul_add _ _ _
        linarith
      linarith
    linarith [h1, h2.le, h3]
  have hlim : Tendsto (fun δ : ℝ => √(∫ x, a x ∂μ + δ) * √(∫ x, b x ∂μ + δ)) (𝓝[>] 0)
      (𝓝 (√(∫ x, a x ∂μ) * √(∫ x, b x ∂μ))) := by
    have : Continuous (fun δ : ℝ => √(∫ x, a x ∂μ + δ) * √(∫ x, b x ∂μ + δ)) := by fun_prop
    have := this.tendsto 0
    simp only [add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto hlim (eventually_nhdsWithin_of_forall fun δ hδ' => hδ δ hδ')

section Bil

variable {X Y K1 K2 Z : Type*} [AddCommGroup X] [AddCommGroup Y]
  [NormedAddCommGroup K1] [NormedAddCommGroup K2] [NormedAddCommGroup Z]

/-- the basic difference estimate for a bounded bilinear map. -/
lemma bil_dist (j1 : X →+ K1) (j2 : Y →+ K2) (Φ : X → Y → Z) (C : ℝ)
    (hL : ∀ x x' y, Φ (x - x') y = Φ x y - Φ x' y) (hR : ∀ x y y', Φ x (y - y') = Φ x y - Φ x y')
    (hb : ∀ x y, ‖Φ x y‖ ≤ C * ‖j1 x‖ * ‖j2 y‖) (x x' : X) (y y' : Y) :
    dist (Φ x y) (Φ x' y') ≤ C * ‖j1 (x - x')‖ * ‖j2 y‖ + C * ‖j1 x'‖ * ‖j2 (y - y')‖ := by
  have e : Φ x y - Φ x' y' = Φ (x - x') y + Φ x' (y - y') := by
    rw [hL, hR]; abel
  rw [dist_eq_norm, e]
  exact (norm_add_le _ _).trans (add_le_add (hb _ _) (hb _ _))

variable [CompleteSpace Z]

omit [CompleteSpace Z] in
/-- bounded bilinear maps send pairs of convergent sequences to Cauchy sequences. -/
lemma bil_cauchy (j1 : X →+ K1) (j2 : Y →+ K2) (Φ : X → Y → Z) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ x x' y, Φ (x - x') y = Φ x y - Φ x' y) (hR : ∀ x y y', Φ x (y - y') = Φ x y - Φ x y')
    (hb : ∀ x y, ‖Φ x y‖ ≤ C * ‖j1 x‖ * ‖j2 y‖) {x : ℕ → X} {y : ℕ → Y} {u : K1} {v : K2}
    (hx : Tendsto (fun k => j1 (x k)) atTop (𝓝 u)) (hy : Tendsto (fun k => j2 (y k)) atTop (𝓝 v)) :
    CauchySeq (fun k => Φ (x k) (y k)) := by
  obtain ⟨R1, hR1⟩ := hx.norm.bddAbove_range
  obtain ⟨R2, hR2⟩ := hy.norm.bddAbove_range
  have b1 : ∀ k, ‖j1 (x k)‖ ≤ R1 := fun k => hR1 ⟨k, rfl⟩
  have b2 : ∀ k, ‖j2 (y k)‖ ≤ R2 := fun k => hR2 ⟨k, rfl⟩
  rw [cauchySeq_iff_tendsto_dist_atTop_0]
  have c1 := cauchySeq_iff_tendsto_dist_atTop_0.1 hx.cauchySeq
  have c2 := cauchySeq_iff_tendsto_dist_atTop_0.1 hy.cauchySeq
  have lim : Tendsto (fun p : ℕ × ℕ => C * R2 * dist (j1 (x p.1)) (j1 (x p.2)) +
      C * R1 * dist (j2 (y p.1)) (j2 (y p.2))) atTop (𝓝 0) := by
    have := (c1.const_mul (C * R2)).add (c2.const_mul (C * R1))
    simpa using this
  refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) lim
  refine (bil_dist j1 j2 Φ C hL hR hb (x p.1) (x p.2) (y p.1) (y p.2)).trans ?_
  rw [map_sub, map_sub, ← dist_eq_norm, ← dist_eq_norm]
  have h1 : C * dist (j1 (x p.1)) (j1 (x p.2)) * ‖j2 (y p.1)‖ ≤
      C * R2 * dist (j1 (x p.1)) (j1 (x p.2)) := by
    have := mul_le_mul_of_nonneg_left (b2 p.1)
      (mul_nonneg hC (dist_nonneg (x := j1 (x p.1)) (y := j1 (x p.2))))
    nlinarith [this]
  have h2 : C * ‖j1 (x p.2)‖ * dist (j2 (y p.1)) (j2 (y p.2)) ≤
      C * R1 * dist (j2 (y p.1)) (j2 (y p.2)) := by
    have := mul_le_mul_of_nonneg_right (b1 p.2)
      (mul_nonneg hC (dist_nonneg (x := j2 (y p.1)) (y := j2 (y p.2))))
    nlinarith [this]
  linarith

omit [CompleteSpace Z] in
/-- two pairs of sequences with the same limits have asymptotically equal images. -/
lemma bil_unique (j1 : X →+ K1) (j2 : Y →+ K2) (Φ : X → Y → Z) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ x x' y, Φ (x - x') y = Φ x y - Φ x' y) (hR : ∀ x y y', Φ x (y - y') = Φ x y - Φ x y')
    (hb : ∀ x y, ‖Φ x y‖ ≤ C * ‖j1 x‖ * ‖j2 y‖) {x x' : ℕ → X} {y y' : ℕ → Y} {u : K1} {v : K2}
    (hx : Tendsto (fun k => j1 (x k)) atTop (𝓝 u)) (hy : Tendsto (fun k => j2 (y k)) atTop (𝓝 v))
    (hx' : Tendsto (fun k => j1 (x' k)) atTop (𝓝 u))
    (hy' : Tendsto (fun k => j2 (y' k)) atTop (𝓝 v)) :
    Tendsto (fun k => dist (Φ (x k) (y k)) (Φ (x' k) (y' k))) atTop (𝓝 0) := by
  obtain ⟨R1, hR1⟩ := hx'.norm.bddAbove_range
  obtain ⟨R2, hR2⟩ := hy.norm.bddAbove_range
  have b1 : ∀ k, ‖j1 (x' k)‖ ≤ R1 := fun k => hR1 ⟨k, rfl⟩
  have b2 : ∀ k, ‖j2 (y k)‖ ≤ R2 := fun k => hR2 ⟨k, rfl⟩
  have d1 : Tendsto (fun k => dist (j1 (x k)) (j1 (x' k))) atTop (𝓝 0) := by
    have := tendsto_iff_dist_tendsto_zero.1 hx
    have h' := tendsto_iff_dist_tendsto_zero.1 hx'
    refine squeeze_zero (fun k => dist_nonneg) (fun k => dist_triangle_right _ _ u) ?_
    simpa using this.add h'
  have d2 : Tendsto (fun k => dist (j2 (y k)) (j2 (y' k))) atTop (𝓝 0) := by
    have := tendsto_iff_dist_tendsto_zero.1 hy
    have h' := tendsto_iff_dist_tendsto_zero.1 hy'
    refine squeeze_zero (fun k => dist_nonneg) (fun k => dist_triangle_right _ _ v) ?_
    simpa using this.add h'
  have lim : Tendsto (fun k => C * R2 * dist (j1 (x k)) (j1 (x' k)) +
      C * R1 * dist (j2 (y k)) (j2 (y' k))) atTop (𝓝 0) := by
    have := (d1.const_mul (C * R2)).add (d2.const_mul (C * R1))
    simpa using this
  refine squeeze_zero (fun k => dist_nonneg) (fun k => ?_) lim
  refine (bil_dist j1 j2 Φ C hL hR hb (x k) (x' k) (y k) (y' k)).trans ?_
  rw [map_sub, map_sub, ← dist_eq_norm, ← dist_eq_norm]
  have h1 : C * dist (j1 (x k)) (j1 (x' k)) * ‖j2 (y k)‖ ≤
      C * R2 * dist (j1 (x k)) (j1 (x' k)) := by
    have := mul_le_mul_of_nonneg_left (b2 k)
      (mul_nonneg hC (dist_nonneg (x := j1 (x k)) (y := j1 (x' k))))
    nlinarith [this]
  have h2 : C * ‖j1 (x' k)‖ * dist (j2 (y k)) (j2 (y' k)) ≤
      C * R1 * dist (j2 (y k)) (j2 (y' k)) := by
    have := mul_le_mul_of_nonneg_right (b1 k)
      (mul_nonneg hC (dist_nonneg (x := j2 (y k)) (y := j2 (y' k))))
    nlinarith [this]
  linarith

/-- **Extension lemma.**  If there is at least one pair of approximating sequences, the images converge
to a limit `γ` that does not depend on the sequences. -/
lemma bil_spec (j1 : X →+ K1) (j2 : Y →+ K2) (Φ : X → Y → Z) {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ x x' y, Φ (x - x') y = Φ x y - Φ x' y) (hR : ∀ x y y', Φ x (y - y') = Φ x y - Φ x y')
    (hb : ∀ x y, ‖Φ x y‖ ≤ C * ‖j1 x‖ * ‖j2 y‖) {u : K1} {v : K2}
    (hex : ∃ (x : ℕ → X) (y : ℕ → Y), Tendsto (fun k => j1 (x k)) atTop (𝓝 u) ∧
      Tendsto (fun k => j2 (y k)) atTop (𝓝 v)) :
    ∃ γ : Z, ∀ (x : ℕ → X) (y : ℕ → Y), Tendsto (fun k => j1 (x k)) atTop (𝓝 u) →
      Tendsto (fun k => j2 (y k)) atTop (𝓝 v) → Tendsto (fun k => Φ (x k) (y k)) atTop (𝓝 γ) := by
  obtain ⟨x0, y0, hx0, hy0⟩ := hex
  obtain ⟨γ, hγ⟩ := cauchySeq_tendsto_of_complete (bil_cauchy j1 j2 Φ hC hL hR hb hx0 hy0)
  refine ⟨γ, fun x y hx hy => ?_⟩
  have := bil_unique j1 j2 Φ hC hL hR hb hx hy hx0 hy0
  refine tendsto_iff_dist_tendsto_zero.2 ?_
  refine squeeze_zero (fun k => dist_nonneg) (fun k => dist_triangle _ (Φ (x0 k) (y0 k)) _) ?_
  simpa using this.add (tendsto_iff_dist_tendsto_zero.1 hγ)

end Bil

end Generic

end MarkovTriple.BGL
