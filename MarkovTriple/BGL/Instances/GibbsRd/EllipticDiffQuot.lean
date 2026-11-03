import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticDefs

/-!
# Difference quotients (R16, elliptic half; Evans §5.8.2 Thm 3, Gilbarg–Trudinger Lemma 7.23/7.24)

Statements Q1, Q2 of `STATEMENTS_R16_Elliptic.md`:
* `dq i h f x = (f(x + h eᵢ) − f(x))/h`;
* `dq_ibp`: `∫ dq_h f · φ = − ∫ f · dq_{−h} φ` (translation invariance of Lebesgue measure);
* `dq_tendsto`: for `φ ∈ C_c^∞`, `∫ f · dq_{−hₙ} φ → ∫ f ∂ᵢφ` (dominated convergence);
* `weak_subseq`: weak sequential compactness of bounded sequences in a separable Hilbert space (Banach–Alaoglu);
* `weakDeriv_of_bounded_dq` (**Q2**): if `f ∈ L²(ℝ^d)` and `‖dq_{hₙ} f‖₂ ≤ C` along `hₙ → 0`, then `f` has a weak
  derivative `∂ᵢ f ∈ L²` (Evans Thm 3 (ii)).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- the difference quotient in direction `eᵢ` -/
noncomputable def dq (i : Fin d) (h : ℝ) (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  (f (x + h • Pi.single i 1) - f x) / h

/-- **Q1** integration by parts for difference quotients. -/
theorem dq_ibp {f φ : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) (hφ : Continuous φ)
    (hs : HasCompactSupport φ) (i : Fin d) (h : ℝ) :
    ∫ x, dq i h f x * φ x = - ∫ x, f x * dq i (-h) φ x := by
  set v : Fin d → ℝ := h • Pi.single i 1 with hv
  have hφv : Continuous (fun y => φ (y - v)) := hφ.comp (continuous_id.sub continuous_const)
  have hsv : HasCompactSupport (fun y => φ (y - v)) := hs.comp_homeomorph (Homeomorph.subRight v)
  have I1 : Integrable (fun y => f y * φ (y - v)) := integrable_mul_cs hf hφv hsv
  have I2 : Integrable (fun y => f y * φ y) := integrable_mul_cs hf hφ hs
  have I3 : Integrable (fun x => f (x + v) * φ x) := by
    have := I1.comp_add_right v
    simpa using this
  have E1 : ∫ x, f (x + v) * φ x = ∫ y, f y * φ (y - v) := by
    have := integral_add_right_eq_self (μ := (volume : Measure (Fin d → ℝ))) (fun y => f y * φ (y - v)) v
    simpa using this
  have lhs : ∫ x, dq i h f x * φ x = h⁻¹ * ((∫ y, f y * φ (y - v)) - ∫ y, f y * φ y) := by
    rw [← E1, ← integral_sub I3 I2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dq, ← hv]; ring
  have rhs : ∫ x, f x * dq i (-h) φ x = - (h⁻¹ * ((∫ y, f y * φ (y - v)) - ∫ y, f y * φ y)) := by
    rw [← integral_sub I1 I2, ← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [dq, neg_smul, ← hv, sub_eq_add_neg, div_neg]
    ring
  rw [lhs, rhs]; ring

/-- the difference quotient of an `L²` function is `L²` -/
theorem memLp_dq {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) (i : Fin d) (h : ℝ) :
    MemLp (dq i h f) 2 volume := by
  have h1 : MemLp (fun x => f (x + h • Pi.single i 1)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume _)
  have := (h1.sub hf).const_mul h⁻¹
  refine this.ae_eq (Eventually.of_forall fun x => ?_)
  simp [dq, div_eq_inv_mul]

lemma norm_single_le (i : Fin d) : ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro j
  by_cases h : j = i
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

/-- pointwise convergence of difference quotients of a `C¹` function -/
lemma dq_pointwise {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) (i : Fin d) (x : Fin d → ℝ) {u : ℕ → ℝ}
    (hu0 : ∀ n, u n ≠ 0) (hlim : Tendsto u atTop (𝓝 0)) :
    Tendsto (fun n => dq i (u n) φ x) atTop (𝓝 (pderiv φ i x)) := by
  have hline : HasDerivAt (fun t : ℝ => x + t • (Pi.single i (1 : ℝ) : Fin d → ℝ)) (Pi.single i 1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single i (1 : ℝ) : Fin d → ℝ)).const_add x
  have hg : HasDerivAt (fun t : ℝ => φ (x + t • (Pi.single i (1 : ℝ) : Fin d → ℝ))) (pderiv φ i x) 0 := by
    have h1 : HasFDerivAt φ (fderiv ℝ φ (x + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin d → ℝ)))
        (x + (0 : ℝ) • (Pi.single i (1 : ℝ) : Fin d → ℝ)) := (hφ.differentiableAt _).hasFDerivAt
    have := h1.comp_hasDerivAt (0 : ℝ) hline
    simp only [zero_smul, add_zero] at this
    exact this
  have hs := hg.tendsto_slope_zero
  have hu : Tendsto u atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hlim, Eventually.of_forall fun n => hu0 n⟩
  refine (hs.comp hu).congr (fun n => ?_)
  simp [dq, Function.comp, div_eq_inv_mul]

/-- **Q1'** `∫ f · dq_{−hₙ} φ → ∫ f ∂ᵢφ` for `φ ∈ C_c^∞` and `f` locally integrable. -/
theorem dq_tendsto {f φ : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) (hφ : Sm φ)
    (hs : HasCompactSupport φ) (i : Fin d) {h : ℕ → ℝ} (hh0 : ∀ n, h n ≠ 0) (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, f x * dq i (-(h n)) φ x) atTop (𝓝 (∫ x, f x * pderiv φ i x)) := by
  set K : Set (Fin d → ℝ) := Metric.cthickening 1 (tsupport φ) with hK
  have hKc : IsCompact K := hs.cthickening
  obtain ⟨M, hM⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hs.fderiv (𝕜 := ℝ))
  have hbd : ∀ (u : ℝ) (x : Fin d → ℝ), |u| ≤ 1 → u ≠ 0 → ‖dq i u φ x‖ ≤ M := by
    intro u x hu hu0
    have mv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := φ) (s := Set.univ) (C := M)
      (fun y _ => hφ.differentiableAt y) (fun y _ => hM y) convex_univ (Set.mem_univ x)
      (Set.mem_univ (x + u • (Pi.single i (1 : ℝ) : Fin d → ℝ)))
    have hn : ‖(x + u • (Pi.single i (1 : ℝ) : Fin d → ℝ)) - x‖ ≤ |u| := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (norm_single_le i)
    have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x)
    calc ‖dq i u φ x‖ = ‖φ (x + u • (Pi.single i (1 : ℝ) : Fin d → ℝ)) - φ x‖ / |u| := by
          simp [dq, norm_div]
      _ ≤ (M * |u|) / |u| := by
          gcongr
          exact mv.trans (mul_le_mul_of_nonneg_left hn hM0)
      _ = M := by field_simp
  have hsupp : ∀ (u : ℝ) (x : Fin d → ℝ), |u| ≤ 1 → x ∉ K → dq i u φ x = 0 := by
    intro u x hu hx
    have h1 : φ x = 0 := by
      by_contra hne
      exact hx (Metric.self_subset_cthickening _ (subset_tsupport _ hne))
    have h2 : φ (x + u • (Pi.single i (1 : ℝ) : Fin d → ℝ)) = 0 := by
      by_contra hne
      refine hx (Metric.mem_cthickening_of_dist_le x (x + u • (Pi.single i (1 : ℝ) : Fin d → ℝ)) 1
        (tsupport φ) (subset_tsupport _ hne) ?_)
      rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
      exact (mul_le_of_le_one_right (abs_nonneg _) (norm_single_le i)).trans hu
    simp [dq, h1, h2]
  have hfK : IntegrableOn f K := hf.integrableOn_isCompact hKc
  have hcont : ∀ u : ℝ, Continuous (dq i u φ) := fun u => by unfold dq; fun_prop
  have hev : ∀ᶠ n in atTop, |h n| ≤ 1 := by
    have := hlim.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with n hn
    simpa using hn
  refine tendsto_integral_filter_of_dominated_convergence (fun x => K.indicator (fun x => ‖f x‖ * M) x)
    (Eventually.of_forall fun n => hf.aestronglyMeasurable.mul (hcont _).aestronglyMeasurable) ?_ ?_ ?_
  · filter_upwards [hev] with n hn
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx, norm_mul]
      exact mul_le_mul_of_nonneg_left (hbd _ x (by simpa using hn) (neg_ne_zero.2 (hh0 n))) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hx, hsupp _ x (by simpa using hn) hx]; simp
  · exact (integrable_indicator_iff hKc.measurableSet).2 (hfK.norm.mul_const M)
  · refine Eventually.of_forall fun x => ?_
    exact (dq_pointwise hφ i x (u := fun n => -(h n)) (fun n => neg_ne_zero.2 (hh0 n))
      (by simpa using hlim.neg)).const_mul (f x)

/-- **Weak sequential compactness of bounded sequences** in a separable Hilbert space
(sequential Banach–Alaoglu + Riesz). -/
theorem weak_subseq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (G : ℕ → H) (C : ℝ) (hG : ∀ n, ‖G n‖ ≤ C) :
    ∃ (g : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ y : H, Tendsto (fun n => inner ℝ (G (φ n)) y) atTop (𝓝 (inner ℝ g y)) := by
  let a : ℕ → WeakDual ℝ H := fun n => WeakDual.toStrongDual.symm (InnerProductSpace.toDual ℝ H (G n))
  have hmem : ∀ n, a n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) C := by
    intro n
    simpa [a] using hG n
  obtain ⟨b, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall ℝ H 0 C hmem
  refine ⟨(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual b), φ, hφ, fun y => ?_⟩
  have := ((WeakDual.eval_continuous y).tendsto b).comp hlim
  have h2 : Tendsto (fun n => inner ℝ (G (φ n)) y) atTop (𝓝 (b y)) := by
    refine this.congr (fun n => ?_)
    simp [a, Function.comp, InnerProductSpace.toDual_apply_apply]
  rw [InnerProductSpace.toDual_symm_apply]
  exact h2

/-- the `L²` pairing of two `L²` functions -/
lemma inner_toLp {u v : (Fin d → ℝ) → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    inner ℝ (hu.toLp u) (hv.toLp v) = ∫ x, u x * v x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x h1 h2
  simp [h1, h2, mul_comm]

/-- **Q2** (Evans §5.8.2 Thm 3 (ii)): an `L²(ℝ^d)` function whose difference quotients are bounded in `L²`
along a sequence `hₙ → 0` has a weak derivative `∂ᵢ f ∈ L²`. -/
theorem weakDeriv_of_bounded_dq {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) (i : Fin d) {C : ℝ}
    (hC : 0 ≤ C) {h : ℕ → ℝ} (hh0 : ∀ n, h n ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hb : ∀ n, eLpNorm (dq i (h n) f) 2 volume ≤ ENNReal.ofReal C) :
    ∃ g : (Fin d → ℝ) → ℝ, MemLp g 2 volume ∧ WeakDeriv f g i := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let G : ℕ → Lp ℝ 2 (volume : Measure (Fin d → ℝ)) := fun n => (memLp_dq hf i (h n)).toLp (dq i (h n) f)
  have hG : ∀ n, ‖G n‖ ≤ C := fun n => by
    simp only [G, Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hC (hb n)
  obtain ⟨g, φs, hφs, hweak⟩ := weak_subseq G C hG
  refine ⟨(g : (Fin d → ℝ) → ℝ), Lp.memLp g, (hf.locallyIntegrable (by norm_num)),
    (Lp.memLp g).locallyIntegrable (by norm_num), fun φ hφ hs => ?_⟩
  have hφS : Sm φ := hφ
  have hφm : MemLp φ 2 volume := hφS.continuous.memLp_of_hasCompactSupport hs
  have h1 : Tendsto (fun n => ∫ x, dq i (h (φs n)) f x * φ x) atTop (𝓝 (∫ x, (g : (Fin d → ℝ) → ℝ) x * φ x)) := by
    have := hweak (hφm.toLp φ)
    have e1 : ∀ n, inner ℝ (G (φs n)) (hφm.toLp φ) = ∫ x, dq i (h (φs n)) f x * φ x := fun n =>
      inner_toLp (memLp_dq hf i (h (φs n))) hφm
    have e2 : inner ℝ g (hφm.toLp φ) = ∫ x, (g : (Fin d → ℝ) → ℝ) x * φ x := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hφm.coeFn_toLp] with x hx
      simp [hx, mul_comm]
    simpa [e1, e2] using this
  have hhs : Tendsto (fun n => h (φs n)) atTop (𝓝 0) := hlim.comp hφs.tendsto_atTop
  have h2 := dq_tendsto (hf.locallyIntegrable (by norm_num)) hφS hs i (h := fun n => h (φs n))
    (fun n => hh0 _) hhs
  have h3 : ∀ n, ∫ x, dq i (h (φs n)) f x * φ x = - ∫ x, f x * dq i (-(h (φs n))) φ x := fun n =>
    dq_ibp (hf.locallyIntegrable (by norm_num)) hφS.continuous hs i _
  have h4 := tendsto_nhds_unique h1 (by simpa only [h3] using h2.neg)
  show ∫ x, f x * pderiv φ i x = _
  linarith

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
