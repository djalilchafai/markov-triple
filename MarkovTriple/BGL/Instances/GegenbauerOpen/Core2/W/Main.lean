import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Core2.W.Pair

/-!
# R31-W: `Core2` fails for the Gegenbauer operator `L_2` on `C_c^∞(-1,1)` (FullTriple-free statement)

See `STATEMENTS_R31_W.md`: `not_core2L_of_pair`, `deficiency_pair_two`, `not_core2L_two`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.Core2W

open MarkovTriple.BGL.Instances.GegenbauerOpen
open MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Q
open MarkovTriple.BGL.Instances.GegenbauerOpen.R24

/-- **W2**: a deficiency pair refutes `Core2L lam`, for every real `lam`. -/
theorem not_core2L_of_pair (lam : ℝ) (w h : ℝ → ℝ)
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1))
    (hwL : ∀ x ∈ Ioo (-1 : ℝ) 1, Core2Q.gL lam w x = w x)
    (hh2 : MemLp h 2 (muL lam)) (hg2 : MemLp (fun x => w x - Core2Q.gL lam h x) 2 (muL lam))
    (hne : ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0) : ¬ Core2L lam := by
  intro hC
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hne
  set g : ℝ → ℝ := fun x => w x - gL lam h x with hg
  -- the pair vanishes on `(1-L) b`
  have hb : ∀ b ∈ goA₀,
      ∫ x, (b x - gL lam b x) * g x ∂muL lam +
        ∫ x, (gL lam b x - gL lam (gL lam b) x) * h x ∂muL lam = 0 := by
    intro b hb0
    have hc : (fun x => b x - gL lam b x) ∈ goA₀ := sub_mem hb0 (gL_mem lam hb0)
    have hK : IsCompact (tsupport b) := goA₀_cs hb0
    have hsub : tsupport (fun x => b x - gL lam b x) ⊆ tsupport b := by
      refine closure_minimal (fun x hx => ?_) (isClosed_tsupport _)
      by_contra hxn
      apply hx
      show b x - gL lam b x = 0
      rw [image_eq_zero_of_notMem_tsupport hxn, gL_zero_off lam hxn]; ring
    obtain ⟨w₁, hw₁, hwa, hI⟩ := key lam hw hh hc hK hb0.2 hsub
    have e : (fun x => gL lam b x - gL lam (gL lam b) x) = gL lam (fun x => b x - gL lam b x) :=
      (gL_sub lam hb0 (gL_mem lam hb0)).symm
    have e' : ∀ x, gL lam b x - gL lam (gL lam b) x = gL lam (fun x => b x - gL lam b x) x :=
      fun x => congrFun e x
    simp_rw [e']
    show ∫ x, (b x - gL lam b x) * (w x - gL lam h x) ∂muL lam + _ = 0
    rw [hI]
    have i1 : Integrable (fun x => b x * w₁ x) (muL lam) :=
      integrable_muL_goA₀ lam (goA₀.mul_mem hb0 hw₁)
    have i2 : Integrable (fun x => gL lam b x * w₁ x) (muL lam) :=
      integrable_muL_goA₀ lam (goA₀.mul_mem (gL_mem lam hb0) hw₁)
    have e1 : ∫ x, (b x - gL lam b x) * w₁ x ∂muL lam =
        ∫ x, b x * w₁ x ∂muL lam - ∫ x, gL lam b x * w₁ x ∂muL lam := by
      rw [← integral_sub i1 i2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      ring
    have e2 : ∫ x, b x * gL lam w₁ x ∂muL lam = ∫ x, b x * w₁ x ∂muL lam := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show b x * gL lam w₁ x = b x * w₁ x
      by_cases hx : x ∈ tsupport b
      · have h1 : gL lam w₁ x = gL lam w x := (gL_eq_of_eventuallyEq lam (hwa x hx)).symm
        have h2 : w x = w₁ x := (hwa x hx).eq_of_nhds
        rw [h1, hwL x (hb0.2 hx), h2]
      · rw [image_eq_zero_of_notMem_tsupport hx]; ring
    rw [e1, ← sym_A₀L lam hb0 hw₁, e2]; ring
  -- the test function
  obtain ⟨a, ha, hta⟩ := exists_test lam hw hx₀ hx₀ne
  obtain ⟨b, hbA, h1, h2⟩ := hC a ha
  obtain ⟨w₁, hw₁, hwa, hI⟩ := key lam hw hh ha (goA₀_cs ha) ha.2 subset_rfl
  have hPa : ∫ x, a x * g x ∂muL lam + ∫ x, gL lam a x * h x ∂muL lam = 0 := by
    set u : ℕ → ℝ → ℝ := fun n x => (b n x - gL lam (b n) x) - a x with hu
    set v : ℕ → ℝ → ℝ := fun n x => (gL lam (b n) x - gL lam (gL lam (b n)) x) - gL lam a x with hv
    have huA : ∀ n, u n ∈ goA₀ := fun n =>
      sub_mem (sub_mem (hbA n) (gL_mem lam (hbA n))) ha
    have hvA : ∀ n, v n ∈ goA₀ := fun n =>
      sub_mem (sub_mem (gL_mem lam (hbA n)) (gL_mem lam (gL_mem lam (hbA n)))) (gL_mem lam ha)
    have hmu : ∀ n, MemLp (u n) 2 (muL lam) := fun n => memLp_muL_goA₀ lam (huA n)
    have hmv : ∀ n, MemLp (v n) 2 (muL lam) := fun n => memLp_muL_goA₀ lam (hvA n)
    have hma : MemLp a 2 (muL lam) := memLp_muL_goA₀ lam ha
    have hmLa : MemLp (gL lam a) 2 (muL lam) := memLp_muL_goA₀ lam (gL_mem lam ha)
    have hexp : ∀ n, ∫ x, a x * g x ∂muL lam + ∫ x, gL lam a x * h x ∂muL lam =
        -(∫ x, u n x * g x ∂muL lam + ∫ x, v n x * h x ∂muL lam) := by
      intro n
      have hz := hb (b n) (hbA n)
      have i1 : Integrable (fun x => u n x * g x) (muL lam) := (hmu n).integrable_mul hg2
      have i2 : Integrable (fun x => a x * g x) (muL lam) := hma.integrable_mul hg2
      have i3 : Integrable (fun x => v n x * h x) (muL lam) := (hmv n).integrable_mul hh2
      have i4 : Integrable (fun x => gL lam a x * h x) (muL lam) := hmLa.integrable_mul hh2
      have e1 : ∫ x, (b n x - gL lam (b n) x) * g x ∂muL lam =
          ∫ x, u n x * g x ∂muL lam + ∫ x, a x * g x ∂muL lam := by
        rw [← integral_add i1 i2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hu]; ring
      have e2 : ∫ x, (gL lam (b n) x - gL lam (gL lam (b n)) x) * h x ∂muL lam =
          ∫ x, v n x * h x ∂muL lam + ∫ x, gL lam a x * h x ∂muL lam := by
        rw [← integral_add i3 i4]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [hv]; ring
      rw [e1, e2] at hz
      linarith
    have hbound : ∀ n, |∫ x, a x * g x ∂muL lam + ∫ x, gL lam a x * h x ∂muL lam| ≤
        (eLpNorm (u n) 2 (muL lam)).toReal * (eLpNorm g 2 (muL lam)).toReal +
        (eLpNorm (v n) 2 (muL lam)).toReal * (eLpNorm h 2 (muL lam)).toReal := by
      intro n
      rw [hexp n, abs_neg]
      calc |∫ x, u n x * g x ∂muL lam + ∫ x, v n x * h x ∂muL lam|
          ≤ |∫ x, u n x * g x ∂muL lam| + |∫ x, v n x * h x ∂muL lam| := abs_add_le _ _
        _ ≤ _ := add_le_add (abs_integral_mul_le (hmu n) hg2) (abs_integral_mul_le (hmv n) hh2)
    have ht : Tendsto (fun n => (eLpNorm (u n) 2 (muL lam)).toReal * (eLpNorm g 2 (muL lam)).toReal +
        (eLpNorm (v n) 2 (muL lam)).toReal * (eLpNorm h 2 (muL lam)).toReal) atTop (𝓝 0) := by
      have t1 : Tendsto (fun n => (eLpNorm (u n) 2 (muL lam)).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
        simpa [hu, Function.comp_def] using this
      have t2 : Tendsto (fun n => (eLpNorm (v n) 2 (muL lam)).toReal) atTop (𝓝 0) := by
        have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h2
        simpa [hv, Function.comp_def] using this
      simpa using (t1.mul_const (eLpNorm g 2 (muL lam)).toReal).add
        (t2.mul_const (eLpNorm h 2 (muL lam)).toReal)
    have := ge_of_tendsto' ht hbound
    exact abs_nonpos_iff.1 this
  exact hta w₁ hw₁ hwa (by rw [← hI]; exact hPa)


/-- `L²(muL lam)` membership from a weighted bound. -/
lemma memLp_muL {lam : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo (-1 : ℝ) 1)) (C : ℝ)
    (hb : ∀ x ∈ Ioo (-1 : ℝ) 1, f x ^ 2 * gρ lam x ≤ C) : MemLp f 2 (muL lam) := by
  have hm : AEStronglyMeasurable f (muL lam) :=
    (hf.aestronglyMeasurable measurableSet_Ioo).mono_ac (withDensity_absolutelyContinuous _ _)
  rw [memLp_two_iff_integrable_sq hm]
  unfold muL
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gρ' lam).ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have : IsFiniteMeasure (volume.restrict (Ioo (-1 : ℝ) 1)) := ⟨by simp⟩
  have hm2 : AEStronglyMeasurable (fun x : ℝ => (ENNReal.ofReal (gρ lam x)).toReal • f x ^ 2)
      (volume.restrict (Ioo (-1 : ℝ) 1)) := by
    have hd : Measurable (fun x : ℝ => (ENNReal.ofReal (gρ lam x)).toReal) :=
      (measurable_gρ' lam).ennreal_ofReal.ennreal_toReal
    have := hd.aestronglyMeasurable.mul ((hf.aestronglyMeasurable (μ := volume) measurableSet_Ioo).pow 2)
    exact this.congr (Filter.Eventually.of_forall fun x => rfl)
  refine (integrable_const C).mono' hm2 ?_
  refine (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun x hx => ?_)
  have hd : 0 ≤ gρ lam x := (gρ_pos lam hx).le
  rw [Real.norm_eq_abs, smul_eq_mul, ENNReal.toReal_ofReal hd,
    abs_of_nonneg (mul_nonneg hd (sq_nonneg _))]
  have := hb x hx
  linarith

/-- **W3**: the deficiency pair for `lam = 2`. -/
theorem deficiency_pair_two : ∃ w h : ℝ → ℝ,
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1) ∧
    (∀ x ∈ Ioo (-1 : ℝ) 1, Core2Q.gL 2 w x = w x) ∧
    MemLp h 2 (muL 2) ∧ MemLp (fun x => w x - Core2Q.gL 2 h x) 2 (muL 2) ∧
      ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0 := by
  refine ⟨wf, hf (-Lam / 2), wf_smooth, hf_smooth _, fun x hx => wf_L hx, ?_, ?_,
    ⟨0, ⟨by norm_num, by norm_num⟩, ?_⟩⟩
  · exact memLp_muL (hf_smooth _).continuousOn _ fun x hx => h_bound _ hx
  · refine memLp_muL ?_ _ fun x hx => g_bound hx
    have h1 : ContinuousOn wf (Ioo (-1 : ℝ) 1) := wf_smooth.continuousOn
    have h2 : ContinuousOn (gL 2 (hf (-Lam / 2))) (Ioo (-1 : ℝ) 1) := by
      have : ContinuousOn (fun x : ℝ => -Lam / 2 * ((1 - x ^ 2) ^ (-(1 / 2) : ℝ) * (3 - 2 / (1 - x ^ 2))))
          (Ioo (-1 : ℝ) 1) := by
        refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
        · exact ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl (one_sub_sq_pos' hx).ne'
        · exact continuousOn_const.sub (continuousOn_const.div (by fun_prop)
            fun x hx => (one_sub_sq_pos' hx).ne')
      exact this.congr fun x hx => hf_L _ hx
    exact h1.sub h2
  · rw [wf_zero]; norm_num

/-- **W4 (main)**: `Core2` fails for `L_2` on `C_c^∞(-1,1)` (graph-core property in `L²((1-x²)^{3/2} dx)`). -/
theorem not_core2L_two : ¬ Core2L 2 := by
  obtain ⟨w, h, hw, hh, hwL, hh2, hg2, hne⟩ := deficiency_pair_two
  exact not_core2L_of_pair 2 w h hw hh hwL hh2 hg2 hne

end MarkovTriple.BGL.Instances.GegenbauerOpen.Core2W
