import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticQ3
import MarkovTriple.BGL.Instances.GibbsRd.Cutoff

/-!
# Localisation of weak derivatives and of the difference-quotient criterion (R16, elliptic half)

Statements R2a, R2b of `STATEMENTS_R16_Elliptic.md` (continuation, batch 2).
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- every compact set lies in some Euclidean ball `{qd ≤ N²}` -/
lemma exists_ball_of_compact {K : Set (Fin d → ℝ)} (hK : IsCompact K) :
    ∃ N : ℕ, ∀ x ∈ K, qd x ≤ (N : ℝ) ^ 2 := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := qd) sm_qd.continuous.continuousOn
  refine ⟨⌈C⌉₊ + 1, fun x hx => ?_⟩
  have h1 : qd x ≤ C := (le_abs_self _).trans (by simpa using hC x hx)
  have h2 : C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
  have h3 : (1 : ℝ) ≤ ((⌈C⌉₊ + 1 : ℕ) : ℝ) := by norm_cast; omega
  push_cast at h3 ⊢
  nlinarith [Nat.cast_nonneg (α := ℝ) ⌈C⌉₊]

lemma isOpen_ball_qd (R : ℝ) : IsOpen {x : Fin d → ℝ | qd x < R} :=
  isOpen_lt sm_qd.continuous continuous_const

/-- **R2a** a function whose cut-offs `cut(N+1)·f` all have `L²_loc` weak derivatives has one itself. -/
theorem weakDeriv_of_local {f : (Fin d → ℝ) → ℝ} (hf : LocL2 f) (i : Fin d)
    (H : ∀ N : ℕ, ∃ g, LocL2 g ∧ WeakDeriv (fun x => cut ((N : ℝ) + 1) x * f x) g i) :
    ∃ g, LocL2 g ∧ WeakDeriv f g i := by
  have hloc : LocallyIntegrable f := hf.locallyIntegrable
  -- strongly measurable representatives
  have H' : ∀ N : ℕ, ∃ g : (Fin d → ℝ) → ℝ, StronglyMeasurable g ∧ LocL2 g ∧
      WeakDeriv (fun x => cut ((N : ℝ) + 1) x * f x) g i := by
    intro N
    obtain ⟨g, hg, hw⟩ := H N
    have hm := hg.locallyIntegrable.aestronglyMeasurable
    exact ⟨hm.mk g, hm.stronglyMeasurable_mk, hg.congr_ae hm.ae_eq_mk,
      hw.congr_ae (Filter.EventuallyEq.refl _ _) hm.ae_eq_mk⟩
  choose gs hgm hgL hgw using H'
  -- local identity
  have hlocid : ∀ N : ℕ, ∀ φ : (Fin d → ℝ) → ℝ, Sm φ → HasCompactSupport φ →
      tsupport φ ⊆ {x | qd x < ((N : ℝ) + 1) ^ 2} →
      ∫ x, f x * fderiv ℝ φ x (Pi.single i 1) = - ∫ x, gs N x * φ x := by
    intro N φ hφ hs hsub
    rw [← (hgw N).2.2 φ hφ hs]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ tsupport φ
    · show f x * _ = cut ((N : ℝ) + 1) x * f x * _
      rw [cut_eq_one (by positivity) (hsub hx).le, one_mul]
    · have : fderiv ℝ φ x = 0 := by
        by_contra hne
        exact hx (support_fderiv_subset ℝ hne)
      simp [this]
  -- agreement
  have hagree : ∀ n N : ℕ, n ≤ N → ∀ᵐ x, x ∈ {x : Fin d → ℝ | qd x < ((n : ℝ) + 1) ^ 2} → gs n x = gs N x := by
    intro n N hnN
    have hU := isOpen_ball_qd (d := d) (((n : ℝ) + 1) ^ 2)
    have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (f := fun x => gs n x - gs N x)
      (μ := (volume : Measure (Fin d → ℝ)))
      (((hgL n).locallyIntegrable.sub (hgL N).locallyIntegrable).locallyIntegrableOn _)
      (fun φ hφ hs hsub => by
        have hφ' : Sm φ := hφ
        have e1 := hlocid n φ hφ' hs hsub
        have e2 := hlocid N φ hφ' hs (hsub.trans (fun x hx => by
          have : ((n : ℝ) + 1) ^ 2 ≤ ((N : ℝ) + 1) ^ 2 := by
            have : (n : ℝ) ≤ N := by exact_mod_cast hnN
            nlinarith [Nat.cast_nonneg (α := ℝ) n]
          exact lt_of_lt_of_le hx this))
        have i1 := integrable_mul_cs (hgL n).locallyIntegrable hφ.continuous hs
        have i2 := integrable_mul_cs (hgL N).locallyIntegrable hφ.continuous hs
        have e3 : ∀ x, φ x • (gs n x - gs N x) = gs n x * φ x - gs N x * φ x := by
          intro x; simp only [smul_eq_mul]; ring
        simp only [e3]
        rw [integral_sub i1 i2]
        linarith)
    filter_upwards [key] with x hx hxU
    exact sub_eq_zero.1 (hx hxU)
  -- the glued function
  let nn : (Fin d → ℝ) → ℕ := fun x => ⌈Real.sqrt (qd x)⌉₊
  have hnn : Measurable nn :=
    (Real.continuous_sqrt.comp sm_qd.continuous).measurable.nat_ceil
  let g : (Fin d → ℝ) → ℝ := fun x => gs (nn x) x
  have hgmeas : Measurable g := by
    have : Measurable (fun p : (Fin d → ℝ) × ℕ => gs p.2 p.1) :=
      measurable_from_prod_countable_left (fun N => (hgm N).measurable)
    exact this.comp (measurable_id.prodMk hnn)
  have hnn_le : ∀ (x : Fin d → ℝ) (N : ℕ), qd x ≤ (N : ℝ) ^ 2 → nn x ≤ N := by
    intro x N hx
    refine Nat.ceil_le.2 ?_
    exact Real.sqrt_le_iff.2 ⟨Nat.cast_nonneg _, hx⟩
  have hnn_mem : ∀ x, qd x < ((nn x : ℝ) + 1) ^ 2 := by
    intro x
    have h1 : Real.sqrt (qd x) ≤ nn x := Nat.le_ceil _
    have h2 : qd x ≤ (nn x : ℝ) ^ 2 := by
      have := Real.sq_sqrt (qd_nonneg x)
      nlinarith [Real.sqrt_nonneg (qd x)]
    nlinarith [Nat.cast_nonneg (α := ℝ) (nn x)]
  have hgN : ∀ N : ℕ, ∀ᵐ x, qd x ≤ (N : ℝ) ^ 2 → g x = gs N x := by
    intro N
    have hall : ∀ᵐ x, ∀ n : ℕ, n ≤ N → x ∈ {x : Fin d → ℝ | qd x < ((n : ℝ) + 1) ^ 2} → gs n x = gs N x := by
      rw [ae_all_iff]
      intro n
      by_cases hn : n ≤ N
      · filter_upwards [hagree n N hn] with x hx _ using hx
      · exact Eventually.of_forall fun x h => absurd h hn
    filter_upwards [hall] with x hx hxq
    exact hx (nn x) (hnn_le x N hxq) (hnn_mem x)
  have hgL' : LocL2 g := by
    intro K hK
    obtain ⟨N, hN⟩ := exists_ball_of_compact hK
    have : g =ᵐ[volume.restrict K] gs N := by
      rw [Filter.EventuallyEq, ae_restrict_iff' hK.measurableSet]
      filter_upwards [hgN N] with x hx hxK using hx (hN x hxK)
    exact (hgL N K hK).ae_eq this.symm
  refine ⟨g, hgL', hloc, hgL'.locallyIntegrable, fun φ hφ hs => ?_⟩
  have hφ' : Sm φ := hφ
  obtain ⟨N, hN⟩ := exists_ball_of_compact (hs : IsCompact (tsupport φ))
  have hsub : tsupport φ ⊆ {x | qd x < ((N : ℝ) + 1) ^ 2} := fun x hx => by
    have := hN x hx
    simp only [Set.mem_ofPred_eq]
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  rw [hlocid N φ hφ' hs hsub]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hgN N] with x hx
  by_cases hxs : x ∈ tsupport φ
  · rw [hx (hN x hxs)]
  · simp [image_eq_zero_of_notMem_tsupport hxs]

/-- the difference quotients of a `C_c^∞` function are uniformly bounded -/
lemma abs_dq_le {φ : (Fin d → ℝ) → ℝ} (hφ : Sm φ) (hs : HasCompactSupport φ) (i : Fin d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (u : ℝ) (x : Fin d → ℝ), ‖dq i u φ x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hφ.continuous_fderiv (by simp)).bounded_above_of_compact_support (hs.fderiv (𝕜 := ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  refine ⟨M, hM0, fun u x => ?_⟩
  by_cases hu : u = 0
  · simp [dq, hu, hM0]
  have mv := Convex.norm_image_sub_le_of_norm_fderiv_le (f := φ) (s := Set.univ) (C := M)
    (fun y _ => hφ.differentiableAt y) (fun y _ => hM y) convex_univ (Set.mem_univ x)
    (Set.mem_univ (x + u • (Pi.single i (1 : ℝ) : Fin d → ℝ)))
  have hn : ‖(x + u • (Pi.single i (1 : ℝ) : Fin d → ℝ)) - x‖ ≤ |u| := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_single_le i)
  have hu' : 0 < |u| := abs_pos.2 hu
  calc ‖dq i u φ x‖ = ‖φ (x + u • (Pi.single i (1 : ℝ) : Fin d → ℝ)) - φ x‖ / |u| := by
        simp [dq, norm_div]
    _ ≤ (M * |u|) / |u| := by
        gcongr
        exact mv.trans (mul_le_mul_of_nonneg_left hn hM0)
    _ = M := by field_simp

lemma aestronglyMeasurable_dq {f : (Fin d → ℝ) → ℝ} (hf : AEStronglyMeasurable f volume) (i : Fin d) (u : ℝ) :
    AEStronglyMeasurable (dq i u f) volume := by
  have h1 : AEStronglyMeasurable (fun x => f (x + u • Pi.single i 1)) volume :=
    hf.comp_quasiMeasurePreserving (measurePreserving_add_right volume _).quasiMeasurePreserving
  refine ((h1.sub hf).mul_const u⁻¹).congr (Eventually.of_forall fun x => ?_)
  simp [dq, div_eq_mul_inv]

/-- Leibniz rule for difference quotients -/
lemma dq_mul (i : Fin d) (u : ℝ) (ζ f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    dq i u (fun y => ζ y * f y) x = ζ (x + u • Pi.single i 1) * dq i u f x + f x * dq i u ζ x := by
  simp only [dq]; ring

/-- **R2b** (Evans §5.8.2 Thm 3(ii), local form): locally bounded `L²` difference quotients give a weak
derivative in `L²_loc`. -/
theorem weakDeriv_of_local_dq {f : (Fin d → ℝ) → ℝ} (hf : LocL2 f) (i : Fin d) {h : ℕ → ℝ}
    (hh0 : ∀ n, h n ≠ 0) (hlim : Tendsto h atTop (𝓝 0))
    (hb : ∀ K : Set (Fin d → ℝ), IsCompact K → ∃ C : ℝ, 0 ≤ C ∧
      ∀ n, eLpNorm (dq i (h n) f) 2 (volume.restrict K) ≤ ENNReal.ofReal C) :
    ∃ g, LocL2 g ∧ WeakDeriv f g i := by
  refine weakDeriv_of_local hf i (fun N => ?_)
  set ζ : (Fin d → ℝ) → ℝ := cut ((N : ℝ) + 1) with hζdef
  have hζ : Sm ζ := sm_cut _
  have hζc : HasCompactSupport ζ := hcs_cut (by positivity)
  -- tail of the sequence with |h n| ≤ 1
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (show ∀ᶠ n in atTop, |h n| ≤ 1 by
    have := hlim.eventually (Metric.closedBall_mem_nhds (0 : ℝ) one_pos)
    filter_upwards [this] with n hn using by simpa using hn)
  set K' : Set (Fin d → ℝ) := Metric.cthickening 1 (tsupport ζ) with hK'
  have hK'c : IsCompact K' := hζc.cthickening
  obtain ⟨C, hC0, hC⟩ := hb K' hK'c
  obtain ⟨M, hM0, hM⟩ := abs_dq_le hζ hζc i
  set F : (Fin d → ℝ) → ℝ := fun x => ζ x * f x with hF
  have hFmem : MemLp F 2 volume := by
    have h1 : MemLp F 2 (volume.restrict (tsupport ζ)) := LocL2.mul_continuous hf hζ.continuous _ hζc
    have h2 : F = (tsupport ζ).indicator F := by
      funext x
      by_cases hx : x ∈ tsupport ζ
      · simp [hx]
      · simp [hx, hF, image_eq_zero_of_notMem_tsupport hx]
    rw [h2]
    exact (memLp_indicator_iff_restrict (isClosed_tsupport ζ).measurableSet).2 h1
  have hfK' : MemLp f 2 (volume.restrict K') := hf K' hK'c
  set B : ℝ≥0∞ := ENNReal.ofReal C + ENNReal.ofReal M * eLpNorm f 2 (volume.restrict K') with hB
  have hBtop : B ≠ ⊤ := by
    refine ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfK'.eLpNorm_ne_top⟩
  have hbound : ∀ n, N0 ≤ n → eLpNorm (dq i (h n) F) 2 volume ≤ ENNReal.ofReal B.toReal := by
    intro n hn
    rw [ENNReal.ofReal_toReal hBtop]
    have hu : |h n| ≤ 1 := hN0 n hn
    have hpt : ∀ x, ‖dq i (h n) F x‖ ≤
        ‖K'.indicator (fun x => ‖dq i (h n) f x‖ + M * ‖f x‖) x‖ := by
      intro x
      by_cases hx : x ∈ K'
      · rw [Set.indicator_of_mem hx, Real.norm_of_nonneg (r := ‖dq i (h n) f x‖ + M * ‖f x‖)
        (add_nonneg (norm_nonneg _) (mul_nonneg hM0 (norm_nonneg _)))]
        rw [dq_mul i (h n) ζ f x]
        have hz : |ζ (x + h n • Pi.single i 1)| ≤ 1 := by
          rw [abs_of_nonneg (cut_nonneg _ _)]; exact cut_le_one _ _
        calc ‖ζ (x + h n • Pi.single i 1) * dq i (h n) f x + f x * dq i (h n) ζ x‖
            ≤ ‖ζ (x + h n • Pi.single i 1) * dq i (h n) f x‖ + ‖f x * dq i (h n) ζ x‖ := norm_add_le _ _
          _ ≤ ‖dq i (h n) f x‖ + M * ‖f x‖ := by
              rw [norm_mul, norm_mul, Real.norm_eq_abs]
              have := hM (h n) x
              nlinarith [norm_nonneg (dq i (h n) f x), norm_nonneg (f x), abs_nonneg (ζ (x + h n • Pi.single i 1)),
                norm_nonneg (dq i (h n) ζ x), mul_le_mul_of_nonneg_right hz (norm_nonneg (dq i (h n) f x)),
                mul_le_mul_of_nonneg_left this (norm_nonneg (f x))]
      · rw [Set.indicator_of_notMem hx]
        have h1 : ζ x = 0 := by
          by_contra hne
          exact hx (Metric.self_subset_cthickening _ (subset_tsupport _ hne))
        have h2 : ζ (x + h n • Pi.single i 1) = 0 := by
          by_contra hne
          refine hx (Metric.mem_cthickening_of_dist_le x (x + h n • Pi.single i 1) 1 (tsupport ζ)
            (subset_tsupport _ hne) ?_)
          rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs]
          exact (mul_le_of_le_one_right (abs_nonneg _) (norm_single_le i)).trans hu
        simp [dq, hF, h1, h2]
    calc eLpNorm (dq i (h n) F) 2 volume
        ≤ eLpNorm (K'.indicator (fun x => ‖dq i (h n) f x‖ + M * ‖f x‖)) 2 volume :=
          eLpNorm_mono (aestronglyMeasurable_dq hFmem.aestronglyMeasurable i _) hpt
      _ = eLpNorm (fun x => ‖dq i (h n) f x‖ + M * ‖f x‖) 2 (volume.restrict K') :=
          eLpNorm_indicator_eq_eLpNorm_restrict hK'c.measurableSet
      _ ≤ eLpNorm (fun x => ‖dq i (h n) f x‖) 2 (volume.restrict K') +
            eLpNorm (fun x => M * ‖f x‖) 2 (volume.restrict K') := by
          exact eLpNorm_add_le (by norm_num)
      _ ≤ ENNReal.ofReal C + ENNReal.ofReal M * eLpNorm f 2 (volume.restrict K') := by
          gcongr
          · exact (eLpNorm_norm _ (aestronglyMeasurable_dq hf.locallyIntegrable.aestronglyMeasurable i _).restrict).le.trans (hC n)
          · have : eLpNorm (fun x => M * ‖f x‖) 2 (volume.restrict K') =
                ENNReal.ofReal M * eLpNorm f 2 (volume.restrict K') := by
              have := eLpNorm_const_smul M (fun x => ‖f x‖) 2 (volume.restrict K')
              have e1 : (M • fun x => ‖f x‖) = fun x => M * ‖f x‖ := by funext x; simp
              rw [e1] at this
              rw [this, Real.enorm_eq_ofReal hM0, eLpNorm_norm _ hfK'.aestronglyMeasurable]
            exact this.le
  obtain ⟨g, hg, hw⟩ := weakDeriv_of_bounded_dq (f := F) hFmem i (C := B.toReal) ENNReal.toReal_nonneg
    (h := fun n => h (n + N0)) (fun n => hh0 _) (hlim.comp (tendsto_add_atTop_nat N0))
    (fun n => hbound _ (by omega))
  exact ⟨g, fun K _ => hg.restrict K, hw⟩

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
