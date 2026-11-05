import Mathlib
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Semigroup.Characterization
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Markov
import MarkovTriple.BGL.Semigroup.Conservative
import MarkovTriple.BGL.Theory.Conservation.Mass
import MarkovTriple.Stochastic.R30.Duhamel

/-!
# Round 32 (A2), part 1: comparison principle `L f ≤ λ f + ε ⇒ P_t f ≤ e^{λt} f + ε (e^{λt}-1)/λ`

See `STATEMENTS_R32_A2.md`.  For `f ∈ 𝒜₀` the curve `s ↦ P_s [f]` is differentiable on `(0,∞)` with derivative `P_s [L f]`
(`hasDerivAt_semigroup` of the Friedrichs semigroup); pairing with `η ≥ 0` and using positivity and the sub-Markov bound gives a scalar
differential inequality, integrated by a Gronwall (monotonicity) argument.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.Stochastic.R32A2

open MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (D : DiffusionTriple E)

/-- the derivative of `s ↦ P_s [f]` for `f ∈ 𝒜₀` -/
lemma hasDerivAt_semigroup_cls (f : D.A₀) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r : ℝ => D.semigroup r.toNNReal (D.cls f))
      (D.semigroup s.toNNReal (D.Lcls f)) s := by
  set S := DiffusionTriple.formData D with hS
  have hFd : D.cls f ∈ D.generator.domain := D.cls_mem_generator_domain f
  set g0 : Lp ℝ 2 D.μ := D.cls f - D.generator ⟨D.cls f, hFd⟩ with hg0
  have hR : S.R g0 = D.cls f := (S.generator_apply_eq_iff hFd _).1 rfl
  have h1 := S.hasDerivAt_semigroup (t := s) hs g0
  rw [hR] at h1
  have e : g0 - D.cls f = -D.Lcls f := by
    rw [hg0, D.generator_cls f hFd]; abel
  rw [e, map_neg, neg_neg] at h1
  exact h1

omit [MeasurableSpace E] in
lemma inner_le_of_ae_le [MeasurableSpace E] {μ : Measure E} [IsFiniteMeasure μ] (a η : Lp ℝ 2 μ)
    (hη : 0 ≤ᵐ[μ] (η : E → ℝ)) {κ : ℝ}
    (h : (a : E → ℝ) ≤ᵐ[μ] fun _ => κ) : inner ℝ a η ≤ κ * ∫ x, η x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  have hηi : Integrable (fun x => (η : E → ℝ) x) μ := (Lp.memLp η).integrable (by norm_num)
  rw [← integral_const_mul]
  refine integral_mono_ae ?_ (hηi.const_mul κ) ?_
  · exact (L2.integrable_inner a η)
  · filter_upwards [h, hη] with x h1 h2
    simp only [RCLike.inner_apply, conj_trivial, Pi.zero_apply] at *
    nlinarith

/-- scalar Gronwall step: for `η ≥ 0` -/
lemma pair_comparison [IsFiniteMeasure D.μ] (f : D.A₀) {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε)
    (hL : ∀ᵐ x ∂D.μ, D.L f.1 x ≤ lam * f.1 x + ε) (η : Lp ℝ 2 D.μ) (hη : 0 ≤ᵐ[D.μ] (η : E → ℝ))
    (t : ℝ≥0) :
    inner ℝ (D.semigroup t (D.cls f)) η ≤
      Real.exp (lam * t) * inner ℝ (D.cls f) η +
        ε * ((Real.exp (lam * t) - 1) / lam) * ∫ x, η x ∂D.μ := by
  set w := D.cls f with hw
  set m : ℝ := ∫ x, η x ∂D.μ with hm
  -- sub-Markov bound
  have hA : ∀ s : ℝ≥0, (D.semigroup s (D.Lcls f - lam • w) : E → ℝ) ≤ᵐ[D.μ] fun _ => ε := by
    intro s
    refine DiffusionTriple.semigroup_le_const D s _ hε ?_
    filter_upwards [DiffusionTriple.coeFn_Lcls D f, DiffusionTriple.coeFn_cls D f,
      Lp.coeFn_sub (D.Lcls f) (lam • w), Lp.coeFn_smul lam w, hL] with x h1 h2 h3 h4 h5
    rw [h3, Pi.sub_apply, h4, Pi.smul_apply, h1, hw, h2, smul_eq_mul]
    linarith
  have hB : ∀ s : ℝ≥0, inner ℝ (D.semigroup s (D.Lcls f)) η ≤
      lam * inner ℝ (D.semigroup s w) η + ε * m := by
    intro s
    have h1 := inner_le_of_ae_le (μ := D.μ) _ η hη (hA s)
    rw [map_sub, map_smul, inner_sub_left, inner_smul_left] at h1
    simp only [conj_trivial] at h1
    linarith
  set Φ : ℝ → ℝ := fun s => inner ℝ (D.semigroup s.toNNReal w) η with hΦ
  have hΦc : Continuous Φ :=
    ((DiffusionTriple.formData D).continuous_semigroup_apply w |>.comp continuous_real_toNNReal).inner
      continuous_const
  have hΦd : ∀ s : ℝ, 0 < s → HasDerivAt Φ (inner ℝ (D.semigroup s.toNNReal (D.Lcls f)) η) s := by
    intro s hs
    have := (hasDerivAt_semigroup_cls D f hs).inner ℝ (hasDerivAt_const s η)
    simpa using this
  set Ψ : ℝ → ℝ := fun s => Real.exp (-lam * s) * (Φ s + ε * m / lam) with hΨ
  have hΨd : ∀ s : ℝ, 0 < s → HasDerivAt Ψ (Real.exp (-lam * s) *
      (inner ℝ (D.semigroup s.toNNReal (D.Lcls f)) η - lam * Φ s - ε * m)) s := by
    intro s hs
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-lam * s)) (Real.exp (-lam * s) * (-lam)) s := by
      have := ((hasDerivAt_id s).const_mul (-lam)).exp
      simpa using this
    have h2 := h1.mul ((hΦd s hs).add_const (ε * m / lam))
    refine h2.congr_deriv ?_
    field_simp
    ring
  have hanti : AntitoneOn Ψ (Set.Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · exact (by fun_prop : Continuous Ψ).continuousOn
    · intro s hs
      rw [interior_Ici] at hs
      exact (hΨd s hs).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Ici] at hs
      rw [(hΨd s hs).deriv]
      refine mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le ?_
      have := hB s.toNNReal
      have e : Φ s = inner ℝ (D.semigroup s.toNNReal w) η := rfl
      linarith
  have key := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 (NNReal.coe_nonneg t))
    (NNReal.coe_nonneg t)
  have e0 : D.semigroup 0 w = w := by
    have : D.semigroup 0 = 1 := (DiffusionTriple.formData D).semigroup_zero
    rw [this]; rfl
  simp only [hΨ, hΦ, Real.toNNReal_coe, Real.toNNReal_zero, e0, mul_zero, Real.exp_zero, one_mul] at key
  have hexp : Real.exp (-lam * (t : ℝ)) * Real.exp (lam * t) = 1 := by
    rw [← Real.exp_add]; simp
  have hpos := Real.exp_pos (lam * (t : ℝ))
  -- multiply `key` by `exp (lam t)`
  have key2 := mul_le_mul_of_nonneg_left key hpos.le
  have e1 : Real.exp (lam * t) * (Real.exp (-lam * t) *
      (inner ℝ (D.semigroup t w) η + ε * m / lam)) = inner ℝ (D.semigroup t w) η + ε * m / lam := by
    rw [← mul_assoc, mul_comm (Real.exp (lam * t)), hexp, one_mul]
  rw [e1] at key2
  have : ε * ((Real.exp (lam * t) - 1) / lam) * m = Real.exp (lam * t) * (ε * m / lam) - ε * m / lam := by
    field_simp
  rw [this]
  linarith

/-- **Comparison principle**: `L f ≤ λ f + ε` a.e. (`f ∈ 𝒜₀`) implies `P_t f ≤ e^{λ t} f + ε (e^{λ t} - 1)/λ` a.e. -/
theorem semigroup_comparison [IsFiniteMeasure D.μ] (f : D.A₀) {lam ε : ℝ}
    (hlam : 0 < lam) (hε : 0 < ε) (hL : ∀ᵐ x ∂D.μ, D.L f.1 x ≤ lam * f.1 x + ε) (t : ℝ≥0) :
    (D.semigroup t (D.cls f) : E → ℝ) ≤ᵐ[D.μ]
      fun x => Real.exp (lam * t) * f.1 x + ε * ((Real.exp (lam * t) - 1) / lam) := by
  set κ : ℝ := ε * ((Real.exp (lam * t) - 1) / lam) with hκ
  set v : Lp ℝ 2 D.μ := D.semigroup t (D.cls f) - Real.exp (lam * t) • D.cls f with hv
  have hvae : (v : E → ℝ) =ᵐ[D.μ] fun x => (D.semigroup t (D.cls f) : E → ℝ) x -
      Real.exp (lam * t) * f.1 x := by
    filter_upwards [Lp.coeFn_sub (D.semigroup t (D.cls f)) (Real.exp (lam * t) • D.cls f),
      Lp.coeFn_smul (Real.exp (lam * t)) (D.cls f), DiffusionTriple.coeFn_cls D f] with x h1 h2 h3
    rw [hv, h1, Pi.sub_apply, h2, Pi.smul_apply, h3, smul_eq_mul]
  -- `∫ v η ≤ κ ∫ η` for `η ≥ 0`
  have hpair : ∀ η : Lp ℝ 2 D.μ, 0 ≤ᵐ[D.μ] (η : E → ℝ) → inner ℝ v η ≤ κ * ∫ x, η x ∂D.μ := by
    intro η hη
    have := pair_comparison D f hlam hε hL η hη t
    rw [hv, inner_sub_left, inner_smul_left]
    simp only [conj_trivial]
    rw [hκ]
    linarith
  -- the set `B = {v > κ}` is null
  have hmeas : MeasurableSet {x | κ < (v : E → ℝ) x} :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable v).measurable
  have hB0 : D.μ {x | κ < (v : E → ℝ) x} = 0 := by
    set B := {x | κ < (v : E → ℝ) x} with hBdef
    have hfin : D.μ B ≠ ∞ := measure_ne_top _ _
    set η : Lp ℝ 2 D.μ := indicatorConstLp 2 hmeas hfin (1 : ℝ) with hη
    have hηae : (η : E → ℝ) =ᵐ[D.μ] B.indicator fun _ => (1 : ℝ) := indicatorConstLp_coeFn
    have hη0 : 0 ≤ᵐ[D.μ] (η : E → ℝ) := by
      filter_upwards [hηae] with x hx
      rw [hx]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
    have h1 := hpair η hη0
    have hint : ∫ x, η x ∂D.μ = (D.μ B).toReal := by
      rw [integral_congr_ae hηae, integral_indicator_const _ hmeas]
      simp [Measure.real]
    have hinn : inner ℝ v η = ∫ x in B, (v : E → ℝ) x ∂D.μ := by
      rw [MeasureTheory.L2.inner_def, ← integral_indicator hmeas]
      refine integral_congr_ae ?_
      filter_upwards [hηae] with x hx
      rw [hx]
      by_cases hxB : x ∈ B <;> simp [hxB]
    rw [hinn, hint] at h1
    have hvi : IntegrableOn (fun x => (v : E → ℝ) x) B D.μ :=
      ((Lp.memLp v).integrable (by norm_num)).integrableOn
    have h2 : ∫ x in B, ((v : E → ℝ) x - κ) ∂D.μ ≤ 0 := by
      rw [integral_sub hvi (integrable_const _)]
      simp only [integral_const, Measure.real, Measure.restrict_apply_univ, smul_eq_mul]
      linarith
    by_contra hne
    have hpos : 0 < D.μ B := pos_iff_ne_zero.2 hne
    have : 0 < ∫ x in B, ((v : E → ℝ) x - κ) ∂D.μ := by
      refine setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_ |>.2 ?_
      · filter_upwards [ae_restrict_mem hmeas] with x hx
        exact sub_nonneg.2 (le_of_lt hx)
      · exact hvi.sub (integrableOn_const (by simp [hfin]))
      · have hsub : B ⊆ Function.support fun x => (v : E → ℝ) x - κ := fun x hx =>
          (sub_pos.2 hx).ne'
        calc (0 : ℝ≥0∞) < D.μ B := hpos
          _ = D.μ.restrict B B := (Measure.restrict_apply_self _ _).symm
          _ ≤ D.μ.restrict B (Function.support fun x => (v : E → ℝ) x - κ) := measure_mono hsub
          _ = _ := Measure.restrict_apply' hmeas
    linarith
  have hae : ∀ᵐ x ∂D.μ, (v : E → ℝ) x ≤ κ := by
    rw [ae_iff]; simpa [not_le] using hB0
  filter_upwards [hae, hvae] with x h1 h2
  rw [h2] at h1
  linarith

end MarkovTriple.Stochastic.R32A2
