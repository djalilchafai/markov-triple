import Mathlib
import MarkovTriple.Stochastic.R32B2.Detect
import MarkovTriple.Stochastic.R31U.Reverse

/-!
# Round 32 (B2), part 2: weak monotonicity `∫ h Γ(P_t f) ≤ ∫ P_s h Γ(P_{t-s} f)`

From the `ε`-form `strong_mono` (R31U) we get the square-root form `∫ h √Γ(P_t f) ≤ ∫ P_s h √Γ(P_{t-s} f)` (`ε → 0`), then `L²` positivity
detection (B1) gives `√Γ(P_t f) ≤ P_s(√Γ(P_{t-s} f))` a.e., Jensen (`jensen_sq`, `P_s` sub-Markov) gives `Γ(P_t f) ≤ P_s(Γ(P_{t-s} f))`, and
the symmetry of `P_s` gives the weak form.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Stochastic.R32B2

open MarkovTriple.BGL MarkovTriple.BGL.FullTriple MarkovTriple.Stochastic.R31U

variable {E : Type*} [MeasurableSpace E] {T : FullTriple E} [IsFiniteMeasure T.μ]

lemma psiS_ge {ε r : ℝ} (hε : 0 < ε) (hr : 0 ≤ r) : Real.sqrt r - ε ≤ psiS ε r := by
  rw [psiS_eq hε (by nlinarith [sq_nonneg ε])]
  have := Real.sqrt_le_sqrt (show r ≤ r + ε ^ 2 by nlinarith [sq_nonneg ε])
  linarith

lemma Pt_bdd_nn (hCD : T.CD 0 ∞) (f : T.A₀) (t : ℝ≥0) : Bdd T (T.Pt t f) := by
  simpa using Pt_bdd hCD f (t : ℝ)

omit [IsFiniteMeasure T.μ] in
lemma bdd_G_meas {gg : E → ℝ} (hg : Bdd T gg) : Measurable (G T gg gg) :=
  T.A_measurable _ (G_mem hg.memA hg.memA)

omit [IsFiniteMeasure T.μ] in
lemma bdd_G_bound {gg : E → ℝ} (hg : Bdd T gg) : ∃ B : ℝ, ∀ᵐ x ∂T.μ, G T gg gg x ≤ B := by
  obtain ⟨-, K, B, -, h, -⟩ := hg
  exact ⟨B, h⟩

omit [IsFiniteMeasure T.μ] in
lemma int_mul_sqrtG {gg : E → ℝ} (hg : Bdd T gg) {h : E → ℝ} (hh : h ∈ T.A₀) :
    Integrable (fun x => h x * Real.sqrt (G T gg gg x)) T.μ := by
  obtain ⟨B, hB⟩ := bdd_G_bound hg
  have hi : Integrable h T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple hh
  refine Integrable.mono' (hi.norm.mul_const (Real.sqrt |B|))
    ((T.toDiffusionTriple.measurable h hh).mul (bdd_G_meas hg).sqrt).aestronglyMeasurable ?_
  filter_upwards [hB] with x hx
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hx.trans (le_abs_self _))) (abs_nonneg _)

lemma int_mul_sqrtG' {gg kk : E → ℝ} (hg : Bdd T gg) (hk : Bdd T kk) :
    Integrable (fun x => kk x * Real.sqrt (G T gg gg x)) T.μ := by
  obtain ⟨B, hB⟩ := bdd_G_bound hg
  obtain ⟨K, -, hK, -, -⟩ := hk.2
  refine intB ((T.A_measurable _ hk.memA).mul (bdd_G_meas hg).sqrt) (C := K * Real.sqrt |B|) ?_
  filter_upwards [hB, hK] with x hx hy
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact mul_le_mul hy (Real.sqrt_le_sqrt (hx.trans (le_abs_self _))) (Real.sqrt_nonneg _)
    ((abs_nonneg _).trans hy)

omit [IsFiniteMeasure T.μ] in
lemma int_mul_G {gg : E → ℝ} (hg : Bdd T gg) {h : E → ℝ} (hh : h ∈ T.A₀) :
    Integrable (fun x => h x * G T gg gg x) T.μ :=
  DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal _ (G_mem hg.memA hg.memA) h hh)

/-- the square-root form of the weak monotonicity -/
lemma sqrt_form (hCD : T.CD 0 ∞) (f h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) (t : ℝ≥0) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) :
    ∫ x, h.1 x * Real.sqrt (G T (T.Pt t f) (T.Pt t f) x) ∂T.μ ≤
      ∫ x, T.Pt s.toNNReal h x * Real.sqrt (G T (T.Pt ((t : ℝ) - s).toNNReal f)
        (T.Pt ((t : ℝ) - s).toNNReal f) x) ∂T.μ := by
  have hBt : Bdd T (T.Pt t f) := Pt_bdd_nn hCD f t
  have hBg : Bdd T (T.Pt ((t : ℝ) - s).toNNReal f) := Pt_bdd hCD f ((t : ℝ) - s)
  have hBk : Bdd T (T.Pt s.toNNReal h) := Pt_bdd hCD h s
  have hk0 : 0 ≤ᵐ[T.μ] T.Pt s.toNNReal h := T.Pt_nonneg _ h hh
  have hΓt0 : 0 ≤ᵐ[T.μ] G T (T.Pt t f) (T.Pt t f) := T.ΓA_nonneg _ hBt.memA
  have hΓg0 : 0 ≤ᵐ[T.μ] G T (T.Pt ((t : ℝ) - s).toNNReal f) (T.Pt ((t : ℝ) - s).toNNReal f) :=
    T.ΓA_nonneg _ hBg.memA
  have hH : Integrable h.1 T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple h.2
  set I1 := ∫ x, h.1 x * Real.sqrt (G T (T.Pt t f) (T.Pt t f) x) ∂T.μ with hI1
  set I2 := ∫ x, T.Pt s.toNNReal h x * Real.sqrt (G T (T.Pt ((t : ℝ) - s).toNNReal f)
        (T.Pt ((t : ℝ) - s).toNNReal f) x) ∂T.μ with hI2
  set H := ∫ x, h.1 x ∂T.μ with hHd
  have hH0 : 0 ≤ H := integral_nonneg_of_ae hh
  have hε : ∀ ε : ℝ, 0 < ε → I1 - ε * H ≤ I2 := by
    intro ε hε
    have hB : T.strongPhi ε f h t 0 = ∫ x, h.1 x * psiS ε (G T (T.Pt t f) (T.Pt t f) x) ∂T.μ := by
      unfold FullTriple.strongPhi
      refine integral_congr_ae ?_
      filter_upwards [T.Pt_zero h] with x hx
      simp only [Real.toNNReal_zero, sub_zero, Real.toNNReal_coe, hx]
    have hmono : T.strongPhi ε f h t 0 ≤ T.strongPhi ε f h t s :=
      strong_mono hCD hε f h hh t ⟨le_rfl, t.2⟩ ⟨hs.1.le, hs.2.le⟩ hs.1.le
    obtain ⟨i1, -, -⟩ := (T.strongInterpolation hCD).hasDerivAt ε hε f h hh t s hs
    have iA : Integrable (fun x => h.1 x * psiS ε (G T (T.Pt t f) (T.Pt t f) x)) T.μ :=
      DiffusionTriple.integrable_of_mem T.toDiffusionTriple
        (T.ideal _ (T.comp_mem_A (psiS_smooth hε) (G_mem hBt.memA hBt.memA)) h.1 h.2)
    have step1 : I1 - ε * H ≤ ∫ x, h.1 x * psiS ε (G T (T.Pt t f) (T.Pt t f) x) ∂T.μ := by
      have e : I1 - ε * H = ∫ x, (h.1 x * Real.sqrt (G T (T.Pt t f) (T.Pt t f) x) - ε * h.1 x) ∂T.μ := by
        rw [integral_sub (int_mul_sqrtG hBt h.2) (hH.const_mul ε), integral_const_mul]
      rw [e]
      refine integral_mono_ae ((int_mul_sqrtG hBt h.2).sub (hH.const_mul ε)) iA ?_
      filter_upwards [hh, hΓt0] with x h1 h2
      have := psiS_ge hε h2
      nlinarith [mul_le_mul_of_nonneg_left this h1]
    have step3 : T.strongPhi ε f h t s ≤ I2 := by
      refine integral_mono_ae i1 (int_mul_sqrtG' hBg hBk) ?_
      filter_upwards [hk0, hΓg0] with x h1 h2
      exact mul_le_mul_of_nonneg_left (psiS_le_sqrt hε h2) h1
    linarith
  by_contra hlt
  push Not at hlt
  have hpos : 0 < (I1 - I2) / (2 * (H + 1)) := by
    have : 0 < I1 - I2 := by linarith
    positivity
  have := hε _ hpos
  have h5 : (I1 - I2) / (2 * (H + 1)) * H < I1 - I2 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

omit [IsFiniteMeasure T.μ] in
/-- symmetry of the semigroup on `L²` classes -/
lemma selfadj_int (D : DiffusionTriple E) (r : ℝ≥0) (a b : Lp ℝ 2 D.μ) :
    ∫ x, (D.semigroup r a : Lp ℝ 2 D.μ) x * b x ∂D.μ =
      ∫ x, a x * (D.semigroup r b : Lp ℝ 2 D.μ) x ∂D.μ := by
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (D.semigroup_isSelfAdjoint r) a b
  rwa [L2_inner_eq, L2_inner_eq] at hs

/-- symmetry for a test function `h`: `∫ h · P_s v = ∫ P_s h · v` -/
lemma selfadj_test (T : FullTriple E) (s : ℝ≥0) (h : T.A₀) (v : Lp ℝ 2 T.μ) :
    ∫ x, h.1 x * (T.toDiffusionTriple.semigroup s v : Lp ℝ 2 T.μ) x ∂T.μ =
      ∫ x, T.Pt s h x * v x ∂T.μ := by
  have := selfadj_int T.toDiffusionTriple s (T.toDiffusionTriple.cls h) v
  have e1 : ∫ x, h.1 x * (T.toDiffusionTriple.semigroup s v : Lp ℝ 2 T.μ) x ∂T.μ =
      ∫ x, (T.toDiffusionTriple.cls h : Lp ℝ 2 T.μ) x * (T.toDiffusionTriple.semigroup s v : Lp ℝ 2 T.μ) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple h] with x hx
    rw [hx]
  have e2 : ∫ x, (T.toDiffusionTriple.semigroup s (T.toDiffusionTriple.cls h) : Lp ℝ 2 T.μ) x * v x ∂T.μ =
      ∫ x, T.Pt s h x * v x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_ae s h] with x hx
    rw [hx]
  rw [e1, ← this, e2]

/-- the weak monotonicity (Γ-form) -/
theorem weak_mono (hCD : T.CD 0 ∞) (f h : T.A₀) (hh : 0 ≤ᵐ[T.μ] h.1) (t : ℝ≥0) {s : ℝ}
    (hs : s ∈ Ioo (0 : ℝ) (t : ℝ)) :
    ∫ x, h.1 x * G T (T.Pt t f) (T.Pt t f) x ∂T.μ ≤
      ∫ x, T.Pt s.toNNReal h x * G T (T.Pt ((t : ℝ) - s).toNNReal f)
        (T.Pt ((t : ℝ) - s).toNNReal f) x ∂T.μ := by
  set gg := T.Pt ((t : ℝ) - s).toNNReal f with hgg
  set tt := T.Pt t f with htt
  have hBt : Bdd T tt := Pt_bdd_nn hCD f t
  have hBg : Bdd T gg := Pt_bdd hCD f ((t : ℝ) - s)
  obtain ⟨Bt, hBt'⟩ := bdd_G_bound hBt
  obtain ⟨Bg, hBg'⟩ := bdd_G_bound hBg
  have hΓt0 : 0 ≤ᵐ[T.μ] G T tt tt := T.ΓA_nonneg _ hBt.memA
  have hΓg0 : 0 ≤ᵐ[T.μ] G T gg gg := T.ΓA_nonneg _ hBg.memA
  -- `L²` classes of `√Γ g`, `Γ g`
  have hvg : MemLp (fun x => Real.sqrt (G T gg gg x)) 2 T.μ :=
    MemLp.of_bound (bdd_G_meas hBg).sqrt.aestronglyMeasurable (Real.sqrt |Bg|) (by
      filter_upwards [hBg'] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hx.trans (le_abs_self _)))
  have hΓgL : MemLp (G T gg gg) 2 T.μ :=
    MemLp.of_bound (bdd_G_meas hBg).aestronglyMeasurable |Bg| (by
      filter_upwards [hBg', hΓg0] with x hx h0
      rw [Real.norm_eq_abs, abs_of_nonneg h0]
      exact hx.trans (le_abs_self _))
  have hvt : MemLp (fun x => Real.sqrt (G T tt tt x)) 2 T.μ :=
    MemLp.of_bound (bdd_G_meas hBt).sqrt.aestronglyMeasurable (Real.sqrt |Bt|) (by
      filter_upwards [hBt'] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact Real.sqrt_le_sqrt (hx.trans (le_abs_self _)))
  set Vg : Lp ℝ 2 T.μ := hvg.toLp _ with hVg
  set Gg : Lp ℝ 2 T.μ := hΓgL.toLp _ with hGg
  set P := T.toDiffusionTriple.semigroup s.toNNReal with hP
  set Pw : Lp ℝ 2 T.μ := P Vg with hPw
  have hVg0 : 0 ≤ᵐ[T.μ] (Vg : E → ℝ) := by
    filter_upwards [hvg.coeFn_toLp] with x hx
    rw [hx]; exact Real.sqrt_nonneg _
  -- step 1: `√Γ t ≤ P_s √Γ g`
  have hstep1 : ∀ᵐ x ∂T.μ, Real.sqrt (G T tt tt x) ≤ Pw x := by
    have hu : MemLp (fun x => Pw x - Real.sqrt (G T tt tt x)) 2 T.μ := (Lp.memLp Pw).sub hvt
    have := pos_detect_L2 T.toDiffusionTriple hu (fun g hg hg0 => by
      set g' : T.A₀ := ⟨g, hg⟩
      have hgL : MemLp g 2 T.μ := T.toDiffusionTriple.memLp g hg 2 (by norm_num) (by simp)
      have e1 : ∫ x, g x * Pw x ∂T.μ = ∫ x, T.Pt s.toNNReal g' x * Real.sqrt (G T gg gg x) ∂T.μ := by
        rw [hPw, selfadj_test T s.toNNReal g' Vg]
        refine integral_congr_ae ?_
        filter_upwards [hvg.coeFn_toLp] with x hx
        rw [hx]
      have i1 : Integrable (fun x => g x * Pw x) T.μ := hgL.integrable_mul (Lp.memLp Pw)
      have i2 : Integrable (fun x => g x * Real.sqrt (G T tt tt x)) T.μ := int_mul_sqrtG hBt hg
      have e2 : ∫ x, g x * (Pw x - Real.sqrt (G T tt tt x)) ∂T.μ =
          ∫ x, g x * Pw x ∂T.μ - ∫ x, g x * Real.sqrt (G T tt tt x) ∂T.μ := by
        rw [← integral_sub i1 i2]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      rw [e2, e1]
      have := sqrt_form hCD f g' hg0 t hs
      linarith)
    filter_upwards [this] with x hx
    simp only [Pi.zero_apply] at hx
    linarith
  -- step 2: Jensen
  have hJ := jensen_sq P (fun u hu => T.toDiffusionTriple.semigroup_nonneg _ hu)
    (fun u hu => T.toDiffusionTriple.semigroup_le_one _ u hu) Vg Gg hVg0 (by
      filter_upwards [hvg.coeFn_toLp, hΓgL.coeFn_toLp, hΓg0] with x h1 h2 h3
      rw [h2, h1, Real.sq_sqrt h3])
  have hstep2 : ∀ᵐ x ∂T.μ, G T tt tt x ≤ (P Gg : Lp ℝ 2 T.μ) x := by
    filter_upwards [hstep1, hJ, hΓt0] with x h1 h2 h3
    have h4 : G T tt tt x = Real.sqrt (G T tt tt x) ^ 2 := (Real.sq_sqrt h3).symm
    have h5 : Real.sqrt (G T tt tt x) ^ 2 ≤ Pw x ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rw [h4]
    exact h5.trans h2
  -- step 3
  have hgL : MemLp h.1 2 T.μ := T.toDiffusionTriple.memLp h.1 h.2 2 (by norm_num) (by simp)
  have i3 : Integrable (fun x => h.1 x * (P Gg : Lp ℝ 2 T.μ) x) T.μ :=
    hgL.integrable_mul (Lp.memLp _)
  calc ∫ x, h.1 x * G T tt tt x ∂T.μ ≤ ∫ x, h.1 x * (P Gg : Lp ℝ 2 T.μ) x ∂T.μ := by
        refine integral_mono_ae (int_mul_G hBt h.2) i3 ?_
        filter_upwards [hh, hstep2] with x h1 h2
        exact mul_le_mul_of_nonneg_left h2 h1
    _ = ∫ x, T.Pt s.toNNReal h x * Gg x ∂T.μ := selfadj_test T s.toNNReal h Gg
    _ = ∫ x, T.Pt s.toNNReal h x * G T gg gg x ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hΓgL.coeFn_toLp] with x hx
        rw [hx]

end MarkovTriple.Stochastic.R32B2
