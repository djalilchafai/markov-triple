import Mathlib
import MarkovTriple.BGL.Theory.Extension.Gamma2Ident
import MarkovTriple.BGL.Theory.Extension.GammaELin
import MarkovTriple.BGL.Theory.Compact.Smooth

/-!
# Symmetric integration by parts against a bounded element of `𝒟(ℰ)` (BGL Lemma 3.3.21, "by density", p. 164)

`ibp_bdd`: `G ∈ 𝒜 ∩ 𝒟(ℰ)` with `L G ∈ L¹`, `k ∈ 𝒜 ∩ 𝒟(ℰ)` essentially bounded: `∫ Γ(G,k) = -∫ k L G`.
Proof (our justification of the book's "extended by density"): `a_j → k` in `𝒟(ℰ)` with `a_j ∈ 𝒜₀`, truncate
`χ(a_j) ∈ 𝒜₀` with `χ` smooth, compactly supported and equal to the identity on a neighbourhood of `[-M,M]`;
F7 for `χ(a_j)`; limit by dominated convergence along an a.e.-convergent subsequence.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

/-- smooth compactly supported truncation, the identity on `[-M, M]`. -/
noncomputable def chiT (M y : ℝ) : ℝ := y * Real.smoothTransition (2 - y ^ 2 / M ^ 2)

lemma chiT_smooth (M : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (chiT M) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_id.pow 2).div_const _)))

lemma chiT_zero (M : ℝ) : chiT M 0 = 0 := by simp [chiT]

lemma chiT_cs {M : ℝ} (hM : 0 < M) : HasCompactSupport (chiT M) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -(2 * M)) (b := 2 * M)) fun y hy => ?_
  have this : 2 * M < |y| ∨ y < -(2 * M) ∨ 2 * M < y := by
    by_contra h
    push Not at h
    exact hy ⟨by linarith [h.2.1, h.1, abs_nonneg y, neg_abs_le y], by linarith [h.2.2]⟩
  have h2 : 4 * M ^ 2 ≤ y ^ 2 := by
    rcases this with h | h | h
    · nlinarith [sq_abs y, abs_nonneg y]
    · nlinarith
    · nlinarith
  have hM2 : 0 < M ^ 2 := by positivity
  have : 4 ≤ y ^ 2 / M ^ 2 := by rw [le_div_iff₀ hM2]; linarith
  unfold chiT
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero]

lemma chiT_eq {M : ℝ} (hM : 0 < M) {y : ℝ} (hy : |y| ≤ M) : chiT M y = y := by
  unfold chiT
  rw [Real.smoothTransition.one_of_one_le, mul_one]
  have hM2 : 0 < M ^ 2 := by positivity
  have : y ^ 2 / M ^ 2 ≤ 1 := by
    rw [div_le_one hM2]; nlinarith [sq_abs y, abs_nonneg y]
  linarith

lemma chiT_eventuallyEq {M : ℝ} (hM : 0 < M) {y : ℝ} (hy : |y| < M) : chiT M =ᶠ[𝓝 y] id := by
  have : {z : ℝ | |z| < M} ∈ 𝓝 y := (isOpen_lt continuous_abs continuous_const).mem_nhds hy
  filter_upwards [this] with z hz using chiT_eq hM hz.le


namespace FullTriple

variable {E : Type*} [MeasurableSpace E] (T : FullTriple E)

lemma memLp_A₀ (a : T.A₀) : MemLp a.1 2 T.μ :=
  (Lp.memLp (T.toDiffusionTriple.cls a)).ae_eq (DiffusionTriple.coeFn_cls T.toDiffusionTriple a)

variable {T}

theorem ibp_bdd {Gf k : E → ℝ} (hG : Gf ∈ T.A) (hG2 : MemLp Gf 2 T.μ)
    (hQG : hG2.toLp Gf ∈ T.formDomain) (hLG : Integrable (T.L Gf) T.μ)
    (hk : k ∈ T.A) (hk2 : MemLp k 2 T.μ) (hQk : hk2.toLp k ∈ T.formDomain)
    {M : ℝ} (hM : ∀ᵐ x ∂T.μ, |k x| ≤ M) :
    Integrable (G T Gf k) T.μ ∧ ∫ x, G T Gf k x ∂T.μ = -∫ x, k x * T.L Gf x ∂T.μ := by
  set uu : T.formDomain := ⟨hG2.toLp Gf, hQG⟩ with huu
  set vv : T.formDomain := ⟨hk2.toLp k, hQk⟩ with hvv
  have hΓ := gammaE_eq_ΓA hG hG2 hQG hk hk2 hQk
  refine ⟨(L1.integrable_coeFn _).congr hΓ, ?_⟩
  rw [← integral_congr_ae hΓ]
  set γ := gammaE T uu vv with hγ
  obtain ⟨a, ha⟩ := exists_formConv vv
  set S := (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm with hS
  have hL1 : Tendsto (fun j => gammaE T uu (T.toDiffusionTriple.clsQ (a j))) atTop (𝓝 γ) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have e : ∀ j, gammaE T uu (T.toDiffusionTriple.clsQ (a j)) - γ =
        gammaE T uu (T.toDiffusionTriple.clsQ (a j) - vv) := by
      intro j
      have := gammaE_lin_right (T := T) (u := uu) (v := vv) (v' := T.toDiffusionTriple.clsQ (a j) - vv)
        (w := T.toDiffusionTriple.clsQ (a j)) 1 (by simp)
      rw [this]; simp [hγ]
    have hn : Tendsto (fun j => ‖S (T.toDiffusionTriple.clsQ (a j) - vv)‖) atTop (𝓝 0) := by
      have := tendsto_iff_norm_sub_tendsto_zero.1 ha
      refine this.congr (fun j => ?_)
      have h3 : S (T.toDiffusionTriple.clsQ (a j) - vv) = S (T.toDiffusionTriple.clsQ (a j)) - S vv :=
        map_sub S _ _
      have h4 : S (T.toDiffusionTriple.clsQ (a j)) = jE T (a j) := symm_clsQ _
      show ‖jE T (a j) - S vv‖ = ‖S (T.toDiffusionTriple.clsQ (a j) - vv)‖
      rw [h3, h4]
    have h2 := hn.const_mul ‖S uu‖
    rw [mul_zero] at h2
    refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) h2
    rw [e]; exact gammaE_bound _ _
  obtain ⟨φ, hφ, hae⟩ := Lp_ae_subseq (FormConv.cls ha)
  set b : ℕ → T.A₀ := fun n => a (φ n) with hb
  have hbmeas : ∀ n, Measurable (b n).1 := fun n => T.A_measurable _ (T.A₀_le _ (b n).2)
  have hbk : ∀ᵐ x ∂T.μ, Tendsto (fun n => (b n).1 x) atTop (𝓝 (k x)) := by
    filter_upwards [hae, ae_all_iff.2 (fun n => DiffusionTriple.coeFn_cls T.toDiffusionTriple (b n)),
      hk2.coeFn_toLp] with x h1 h2 h3
    have : (fun n => (b n).1 x) = fun n => (T.toDiffusionTriple.cls (a (φ n)) : E → ℝ) x := by
      funext n; exact (h2 n).symm
    rw [this]; simpa [hvv, h3] using h1
  -- the truncation
  set M' : ℝ := |M| + 1 with hM'
  have hM'0 : 0 < M' := by positivity
  set χ := chiT M' with hχ
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := chiT_smooth M'
  have hχ1 : ContDiff ℝ (⊤ : ℕ∞) (deriv χ) := (contDiff_infty_iff_deriv.1 hχs).2
  obtain ⟨K0, K1, K2, hK0, hK1, hK2, hb0, hb1, hb2⟩ := Compact.smooth_bounds hχs (chiT_cs hM'0)
  have hχk : ∀ᵐ x ∂T.μ, χ (k x) = k x ∧ deriv χ (k x) = 1 := by
    filter_upwards [hM] with x hx
    have hlt : |k x| < M' := by rw [hM']; linarith [le_abs_self M]
    refine ⟨chiT_eq hM'0 hlt.le, ?_⟩
    rw [(chiT_eventuallyEq hM'0 hlt).deriv_eq]; simp
  have hφA : ∀ n, (fun x => χ ((b n).1 x)) ∈ T.A₀ := by
    intro n
    have := T.toDiffusionTriple.comp_mem 1 (fun z => χ (z 0))
      (hχs.comp (contDiff_apply ℝ ℝ 0)) (by simpa using chiT_zero M') ![(b n).1]
      (by intro i; fin_cases i; simpa using (b n).2)
    simpa using this
  -- F7
  have hF7 : ∀ n, ∫ x, G T Gf (fun y => χ ((b n).1 y)) x ∂T.μ =
      -∫ x, χ ((b n).1 x) * T.L Gf x ∂T.μ := fun n => (T.ibp_A Gf hG _ (hφA n)).1
  -- left limit
  have hLHS : Tendsto (fun n => ∫ x, G T Gf (fun y => χ ((b n).1 y)) x ∂T.μ) atTop
      (𝓝 (∫ x, (γ : E → ℝ) x ∂T.μ)) := by
    set γn : ℕ → Lp ℝ 1 T.μ := fun n => gammaE T uu (T.toDiffusionTriple.clsQ (b n)) with hγn
    have hγc : Tendsto γn atTop (𝓝 γ) := hL1.comp hφ.tendsto_atTop
    have hid : ∀ n, G T Gf (fun y => χ ((b n).1 y)) =ᵐ[T.μ]
        fun x => deriv χ ((b n).1 x) * (γn n : E → ℝ) x := by
      intro n
      have h1 := ΓA_comp_left T hχs (T.A₀_le _ (b n).2) hG
      have h2 := gammaE_clsQ_eq hG hG2 hQG (b n)
      filter_upwards [h1, h2] with x e1 e2
      have c1 := congrFun (G_comm (T := T) Gf (fun y => χ ((b n).1 y))) x
      have c2 := congrFun (G_comm (T := T) (b n).1 Gf) x
      have e1' : G T (fun y => χ ((b n).1 y)) Gf x =
          deriv χ ((b n).1 x) * G T (b n).1 Gf x := e1
      rw [c1, e1', c2]
      show _ = _ * (gammaE T uu _ : E → ℝ) x
      rw [e2]
    have iγn : ∀ n, Integrable (fun x => deriv χ ((b n).1 x) * (γn n : E → ℝ) x) T.μ := fun n =>
      (L1.integrable_coeFn (γn n)).bdd_mul (c := K1)
        ((hχ1.continuous.measurable.comp (hbmeas n)).aestronglyMeasurable)
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb1 _)
    have iγ : Integrable (fun x => (γ : E → ℝ) x) T.μ := L1.integrable_coeFn γ
    have t1 : Tendsto (fun n => ∫ x, deriv χ ((b n).1 x) * ((γn n : E → ℝ) x - (γ : E → ℝ) x) ∂T.μ)
        atTop (𝓝 0) := by
      have hnorm : Tendsto (fun n => ‖γn n - γ‖) atTop (𝓝 0) := by
        simpa using tendsto_iff_norm_sub_tendsto_zero.1 hγc
      have h2 := hnorm.const_mul K1
      rw [mul_zero] at h2
      refine squeeze_zero_norm (fun n => ?_) h2
      have e : ‖γn n - γ‖ = ∫ x, |(γn n : E → ℝ) x - (γ : E → ℝ) x| ∂T.μ := by
        rw [L1.norm_eq_integral_norm]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_sub (γn n) γ] with x hx
        rw [hx]; simp
      rw [e, ← integral_const_mul]
      refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
        (Eventually.of_forall fun x => norm_nonneg _)
        (((L1.integrable_coeFn (γn n)).sub iγ).abs.const_mul K1) (Eventually.of_forall fun x => ?_))
      dsimp only
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb1 _) (abs_nonneg _)
    have t2 : Tendsto (fun n => ∫ x, deriv χ ((b n).1 x) * (γ : E → ℝ) x ∂T.μ) atTop
        (𝓝 (∫ x, (γ : E → ℝ) x ∂T.μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun x => K1 * |(γ : E → ℝ) x|)
        (fun n => ((hχ1.continuous.measurable.comp (hbmeas n)).aestronglyMeasurable.mul
          iγ.aestronglyMeasurable)) (iγ.abs.const_mul K1)
        (fun n => Eventually.of_forall fun x => ?_) ?_
      · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hb1 _) (abs_nonneg _)
      · filter_upwards [hbk, hχk] with x h1 h2
        have := ((hχ1.continuous.tendsto _).comp h1).mul_const ((γ : E → ℝ) x)
        rw [h2.2, one_mul] at this
        exact this
    have := t1.add t2
    rw [zero_add] at this
    refine this.congr (fun n => ?_)
    have iγm : Integrable (fun x => deriv χ ((b n).1 x) * (γ : E → ℝ) x) T.μ :=
      iγ.bdd_mul (c := K1) ((hχ1.continuous.measurable.comp (hbmeas n)).aestronglyMeasurable)
        (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb1 _)
    have iA : Integrable (fun x => deriv χ ((b n).1 x) * ((γn n : E → ℝ) x - (γ : E → ℝ) x)) T.μ :=
      ((iγn n).sub iγm).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
    rw [← integral_add iA iγm, integral_congr_ae (hid n)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  have hRHS : Tendsto (fun n => -∫ x, χ ((b n).1 x) * T.L Gf x ∂T.μ) atTop
      (𝓝 (-∫ x, k x * T.L Gf x ∂T.μ)) := by
    refine Tendsto.neg ?_
    refine tendsto_integral_of_dominated_convergence (fun x => K0 * |T.L Gf x|)
      (fun n => ((hχs.continuous.measurable.comp (hbmeas n)).aestronglyMeasurable.mul
        hLG.aestronglyMeasurable)) (hLG.abs.const_mul K0)
      (fun n => Eventually.of_forall fun x => ?_) ?_
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb0 _) (abs_nonneg _)
    · filter_upwards [hbk, hχk] with x h1 h2
      have := ((hχs.continuous.tendsto _).comp h1).mul_const (T.L Gf x)
      rw [h2.1] at this
      exact this
  refine tendsto_nhds_unique hLHS ?_
  exact hRHS.congr (fun n => (hF7 n).symm)

end FullTriple

end MarkovTriple.BGL
