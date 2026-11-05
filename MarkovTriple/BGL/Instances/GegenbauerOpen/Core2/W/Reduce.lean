import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Core2.Frobenius
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Defs
import MarkovTriple.BGL.Instances.Riemannian.R24.GoCore2
import MarkovTriple.BGL.Semigroup.Mass

/-!
# R31-W: `Core2L lam` (FullTriple-free transcription of `Core2`) and the deficiency-pair reduction

See `STATEMENTS_R31_W.md`.  `muL lam` is the (unnormalised) Gegenbauer weight on `(-1,1)`, `gL lam` the
generator; `Core2L lam` is the literal statement of `FullTriple.Core2`.  `not_core2L_of_pair` is the
analogue of `go_not_core2_of_pair` (R24-D) for every real `lam`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.Core2W

open MarkovTriple.BGL.Instances.GegenbauerOpen
open MarkovTriple.BGL.Instances.GegenbauerOpen.Core2Q

/-- the (unnormalised) Gegenbauer weight on `(-1,1)`. -/
noncomputable def muL (lam : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity (fun x => ENNReal.ofReal (Core2Q.gρ lam x))

/-- literal transcription of `FullTriple.Core2` for `L_lam` on `goA₀` in `L²(muL lam)`. -/
def Core2L (lam : ℝ) : Prop :=
  ∀ a ∈ goA₀, ∃ b : ℕ → ℝ → ℝ, (∀ n, b n ∈ goA₀) ∧
    Tendsto (fun n => eLpNorm (fun x => (b n x - Core2Q.gL lam (b n) x) - a x) 2 (muL lam)) atTop (𝓝 0) ∧
    Tendsto (fun n => eLpNorm (fun x => (Core2Q.gL lam (b n) x - Core2Q.gL lam (Core2Q.gL lam (b n)) x)
      - Core2Q.gL lam a x) 2 (muL lam)) atTop (𝓝 0)

lemma one_sub_sq_pos' {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2]

lemma hasDerivAt_sp (r : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => (1 - y ^ 2) ^ r) (-2 * r * x * (1 - x ^ 2) ^ (r - 1)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
    simpa using ((hasDerivAt_pow 2 x).const_sub 1)
  have := h1.rpow_const (p := r) (Or.inl (one_sub_sq_pos' hx).ne')
  convert this using 1
  ring

lemma measurable_gρ' (lam : ℝ) : Measurable (gρ lam) :=
  (measurable_const.sub (measurable_id.pow_const 2)).pow_const _

lemma gρ_pos (lam : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < gρ lam x :=
  Real.rpow_pos_of_pos (by nlinarith [hx.1, hx.2]) _

lemma integral_muL (lam : ℝ) {h : ℝ → ℝ} (hh : ∀ x ∉ Ioo (-1 : ℝ) 1, h x = 0) :
    ∫ x, h x ∂muL lam = ∫ x, gρ lam x * h x := by
  have e : ∫ x, h x ∂muL lam = ∫ x, (Real.toNNReal (gρ lam x)) • h x
      ∂(volume.restrict (Ioo (-1 : ℝ) 1)) :=
    integral_withDensity_eq_integral_smul (f := fun x => Real.toNNReal (gρ lam x))
      (measurable_gρ' lam).real_toNNReal h
  rw [e]
  have e2 : ∫ x, (Real.toNNReal (gρ lam x)) • h x ∂(volume.restrict (Ioo (-1 : ℝ) 1))
      = ∫ x, (Real.toNNReal (gρ lam x)) • h x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by simp [hh x hx]
  rw [e2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · simp [NNReal.smul_def, Real.coe_toNNReal _ (gρ_pos lam hx).le]
  · simp [hh x hx]

lemma continuousOn_gρ (lam : ℝ) : ContinuousOn (gρ lam) (Ioo (-1 : ℝ) 1) := by
  refine ContinuousOn.rpow_const (by fun_prop) fun x hx => Or.inl (one_sub_sq_pos' hx).ne'

lemma integrable_muL_goA₀ (lam : ℝ) {f : ℝ → ℝ} (hf : f ∈ goA₀) : Integrable f (muL lam) := by
  unfold muL
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gρ' lam).ennreal_ofReal
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  have hK : IsCompact (tsupport f) := goA₀_cs hf
  have hKI : tsupport f ⊆ Ioo (-1 : ℝ) 1 := hf.2
  have hcont : ContinuousOn (fun x => (ENNReal.ofReal (gρ lam x)).toReal • f x) (tsupport f) := by
    have : ContinuousOn (fun x => gρ lam x * f x) (tsupport f) :=
      ((continuousOn_gρ lam).mono hKI).mul (goA₀_smooth hf).continuous.continuousOn
    refine this.congr fun x hx => ?_
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (gρ_pos lam (hKI hx)).le]
  have hI : IntegrableOn (fun x => (ENNReal.ofReal (gρ lam x)).toReal • f x) (tsupport f) volume :=
    hcont.integrableOn_compact hK
  have hI2 : IntegrableOn (fun x => (ENNReal.ofReal (gρ lam x)).toReal • f x) (Ioo (-1 : ℝ) 1) volume :=
    hI.of_forall_sdiff_eq_zero measurableSet_Ioo fun x hx => by
      have : f x = 0 := image_eq_zero_of_notMem_tsupport hx.2
      simp [this]
  exact hI2

lemma memLp_muL_goA₀ (lam : ℝ) {f : ℝ → ℝ} (hf : f ∈ goA₀) : MemLp f 2 (muL lam) := by
  have hm : AEStronglyMeasurable f (muL lam) := (goA₀_smooth hf).continuous.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hm]
  have := integrable_muL_goA₀ lam (goA₀.mul_mem hf hf)
  exact this.congr (Filter.Eventually.of_forall fun x => by simp [sq])

/-- `|∫ f g| ≤ ‖f‖₂ ‖g‖₂`. -/
lemma abs_integral_mul_le {μ : Measure ℝ} {f g : ℝ → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have h := abs_real_inner_le_norm (hf.toLp f) (hg.toLp g)
  rw [L2_inner_eq, Lp.norm_toLp, Lp.norm_toLp] at h
  have e : ∫ x, (hf.toLp f) x * (hg.toLp g) x ∂μ = ∫ x, f x * g x ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rwa [e] at h

/-! ### the generator on `𝒜₀` -/

lemma gL_mem (lam : ℝ) {f : ℝ → ℝ} (hf : f ∈ goA₀) : gL lam f ∈ goA₀ := by
  have h1 := smul_mem_goA₀ (p := fun x : ℝ => 1 - x ^ 2) sm_w1
    (deriv_mem_goA₀ (deriv_mem_goA₀ hf))
  have h2 := smul_mem_goA₀ (p := fun x : ℝ => (2 * lam + 1) * x)
    (contDiff_const.mul contDiff_id) (deriv_mem_goA₀ hf)
  have := sub_mem h1 h2
  convert this using 1
  funext x
  simp only [gL, Pi.sub_apply, mul_assoc]

lemma gL_eq_of_eventuallyEq (lam : ℝ) {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) :
    gL lam f x = gL lam g x := by
  have h1 : deriv f =ᶠ[𝓝 x] deriv g := h.deriv
  simp only [gL, h.deriv_eq, h1.deriv_eq]

lemma gL_zero_off (lam : ℝ) {c : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport c) : gL lam c x = 0 := by
  have h0 : deriv c x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_deriv_subset h))
  have h1 : deriv (deriv c) x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (tsupport_deriv_subset (tsupport_deriv_subset h)))
  simp [gL, h0, h1]

lemma gL_sub (lam : ℝ) {f g : ℝ → ℝ} (hf : f ∈ goA₀) (hg : g ∈ goA₀) :
    gL lam (fun x => f x - g x) = fun x => gL lam f x - gL lam g x := by
  have hdf : Differentiable ℝ f := (goA₀_smooth hf).differentiable (by simp)
  have hdg : Differentiable ℝ g := (goA₀_smooth hg).differentiable (by simp)
  have hdf' : Differentiable ℝ (deriv f) := (goA₀_smooth (deriv_mem_goA₀ hf)).differentiable (by simp)
  have hdg' : Differentiable ℝ (deriv g) := (goA₀_smooth (deriv_mem_goA₀ hg)).differentiable (by simp)
  have e1 : deriv (fun x => f x - g x) = fun x => deriv f x - deriv g x := by
    funext x; exact deriv_sub (hdf x) (hdg x)
  funext x
  simp only [gL, e1]
  have e2 : deriv (fun x => deriv f x - deriv g x) x = deriv (deriv f) x - deriv (deriv g) x :=
    deriv_sub (hdf' x) (hdg' x)
  rw [e2]
  ring

/-! ### symmetry of `L_lam` on `𝒜₀` w.r.t. `muL lam` -/

/-- cut-off times `(1-x²)^(lam+1/2)`. -/
noncomputable def qt (lam : ℝ) (n : ℕ) (x : ℝ) : ℝ := gocut n x * (1 - x ^ 2) ^ (lam + 1 / 2)

lemma qt_smooth (lam : ℝ) (n : ℕ) : Lebesgue.Sm (qt lam n) := by
  refine smooth_cut_mul (f := fun x => (1 - x ^ 2) ^ (lam + 1 / 2)) ?_ n
  refine ContDiffOn.rpow_const_of_ne ?_ fun x hx => (by nlinarith [hx.1, hx.2] : (0 : ℝ) < 1 - x ^ 2).ne'
  exact (contDiff_const.sub (contDiff_id.pow 2)).contDiffOn

lemma ibp_aux (lam : ℝ) {c d : ℝ → ℝ} (hc : c ∈ goA₀) (hd : d ∈ goA₀) {n : ℕ}
    (hcU : tsupport c ⊆ Ioo (-1 + 4 / ((n : ℝ) + 1)) (1 - 4 / ((n : ℝ) + 1))) :
    ∫ x, c x * gL lam d x ∂muL lam = -∫ x, qt lam n x * (deriv c x * deriv d x) := by
  set v : ℝ → ℝ := fun x => qt lam n x * deriv d x with hv
  have hvs : Lebesgue.Sm v := (qt_smooth lam n).mul (goA₀_smooth hd).deriv'
  have h := Lebesgue.ibp_cs (goA₀_smooth hc) hvs (Or.inl (goA₀_cs hc))
  rw [integral_muL lam (fun x hx => by simp [zero_off_go hc hx])]
  have hpt : ∀ x, gρ lam x * (c x * gL lam d x) = c x * deriv v x := by
    intro x
    by_cases hx : x ∈ tsupport c
    · have hU := hcU hx
      have hxI : x ∈ Ioo (-1 : ℝ) 1 := by
        have hpos : 0 < 4 / ((n : ℝ) + 1) := by positivity
        exact ⟨by linarith [hU.1], by linarith [hU.2]⟩
      have hs : 0 < 1 - x ^ 2 := by nlinarith [hxI.1, hxI.2]
      have hev : v =ᶠ[𝓝 x] fun y => (1 - y ^ 2) ^ (lam + 1 / 2) * deriv d y := by
        filter_upwards [isOpen_Ioo.mem_nhds hU] with y hy
        simp only [hv, qt, gocut_eq_one_of_mem hy, one_mul]
      have hq : HasDerivAt (fun y => (1 - y ^ 2) ^ (lam + 1 / 2) * deriv d y) _ x :=
        (hasDerivAt_sp (lam + 1 / 2) hxI).mul ((goA₀_smooth hd).deriv'.hasDerivAt x)
      rw [hev.deriv_eq, hq.deriv]
      have e1 : (1 - x ^ 2) ^ (lam + 1 / 2 - 1) = (1 - x ^ 2) ^ (lam - 1 / 2) := by
        congr 1; ring
      have e2 : (1 - x ^ 2) ^ (lam + 1 / 2) = (1 - x ^ 2) ^ (lam - 1 / 2) * (1 - x ^ 2) := by
        rw [show lam + 1 / 2 = (lam - 1 / 2) + 1 by ring, Real.rpow_add hs, Real.rpow_one]
      rw [e1, e2]
      simp only [gρ, gL]
      ring
    · have : c x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this]
  have e1 : ∫ x, gρ lam x * (c x * gL lam d x) = ∫ x, c x * deriv v x :=
    integral_congr_ae (Filter.Eventually.of_forall hpt)
  rw [e1, h]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [hv]
  ring

lemma sym_A₀L (lam : ℝ) {c d : ℝ → ℝ} (hc : c ∈ goA₀) (hd : d ∈ goA₀) :
    ∫ x, c x * gL lam d x ∂muL lam = ∫ x, gL lam c x * d x ∂muL lam := by
  obtain ⟨n, hn⟩ := exists_gocut_eq_one ((goA₀_cs hc).union (goA₀_cs hd))
    (union_subset hc.2 hd.2)
  have h1 := ibp_aux lam hc hd (n := n) (subset_union_left.trans hn)
  have h2 := ibp_aux lam hd hc (n := n) (subset_union_right.trans hn)
  have e2 : ∫ x, gL lam c x * d x ∂muL lam = ∫ x, d x * gL lam c x ∂muL lam :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [e2, h1, h2]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring

/-! ### local replacement and the key computation -/

lemma key (lam : ℝ) {w h : ℝ → ℝ} (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1)) {c : ℝ → ℝ} (hc : c ∈ goA₀)
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) (hcK : tsupport c ⊆ K) :
    ∃ w₁ ∈ goA₀, (∀ x ∈ K, w =ᶠ[𝓝 x] w₁) ∧
      ∫ x, c x * (w x - gL lam h x) ∂muL lam + ∫ x, gL lam c x * h x ∂muL lam
        = ∫ x, c x * w₁ x ∂muL lam := by
  obtain ⟨w₁, hw₁, hwa⟩ := loc_agree hw hK hKI
  obtain ⟨h₁, hh₁, hha⟩ := loc_agree hh hK hKI
  refine ⟨w₁, hw₁, hwa, ?_⟩
  have hpt1 : ∀ x, c x * (w x - gL lam h x) = c x * w₁ x - c x * gL lam h₁ x := by
    intro x
    by_cases hx : x ∈ tsupport c
    · have e1 : w x = w₁ x := (hwa x (hcK hx)).eq_of_nhds
      have e3 : gL lam h x = gL lam h₁ x := gL_eq_of_eventuallyEq lam (hha x (hcK hx))
      rw [e1, e3]; ring
    · have e1 : c x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [e1]; ring
  have hpt2 : ∀ x, gL lam c x * h x = gL lam c x * h₁ x := by
    intro x
    by_cases hx : x ∈ tsupport c
    · rw [(hha x (hcK hx)).eq_of_nhds]
    · rw [gL_zero_off lam hx]; ring
  have i1 : Integrable (fun x => c x * w₁ x) (muL lam) :=
    integrable_muL_goA₀ lam (goA₀.mul_mem hc hw₁)
  have i2 : Integrable (fun x => c x * gL lam h₁ x) (muL lam) :=
    integrable_muL_goA₀ lam (goA₀.mul_mem hc (gL_mem lam hh₁))
  simp_rw [hpt1, hpt2]
  rw [integral_sub i1 i2, sym_A₀L lam hc hh₁]
  ring

/-- a test function in `𝒜₀` detecting a point where `w ≠ 0`. -/
lemma exists_test (lam : ℝ) {w : ℝ → ℝ}
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1)) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo (-1 : ℝ) 1) (hne : w x₀ ≠ 0) :
    ∃ a ∈ goA₀, ∀ w₁ ∈ goA₀, (∀ x ∈ tsupport a, w =ᶠ[𝓝 x] w₁) → ∫ x, a x * w₁ x ∂muL lam ≠ 0 := by
  have hcont : ContinuousAt w x₀ := hw.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hx₀)
  have hnb : ∀ᶠ y in 𝓝 x₀, y ∈ Ioo (-1 : ℝ) 1 ∧ |w y - w x₀| < |w x₀| :=
    Filter.Eventually.and (isOpen_Ioo.mem_nhds hx₀)
      ((hcont.sub continuousAt_const).abs.eventually (gt_mem_nhds (by simpa using hne)))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hnb
  let f : ContDiffBump x₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hfs : tsupport (f : ℝ → ℝ) ⊆ Metric.ball x₀ ε := by
    rw [f.tsupport_eq]
    intro y hy
    rw [Metric.mem_ball]
    have : dist y x₀ ≤ ε / 2 := hy
    linarith
  refine ⟨f, ⟨f.contDiff, fun y hy => (hball y (hfs hy)).1⟩, fun w₁ hw₁ hag => ?_⟩
  have hFc : HasCompactSupport (fun x => gρ lam x * (f x * w₁ x)) := by
    have h1 : HasCompactSupport (fun x => f x * w₁ x) := f.hasCompactSupport.mul_right
    exact h1.mul_left
  have hF : Continuous (fun x => gρ lam x * (f x * w₁ x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : x ∈ tsupport (f : ℝ → ℝ)
    · have hxI : x ∈ Ioo (-1 : ℝ) 1 := (hball x (hfs hx)).1
      exact ((continuousOn_gρ lam).continuousAt (isOpen_Ioo.mem_nhds hxI)).mul
        (f.continuous.mul (goA₀_smooth hw₁).continuous).continuousAt
    · have hz : (fun x => gρ lam x * (f x * w₁ x)) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [(isClosed_tsupport (f : ℝ → ℝ)).isOpen_compl.mem_nhds hx] with y hy
        simp [image_eq_zero_of_notMem_tsupport hy]
      exact continuousAt_const.congr hz.symm
  have hvan : ∀ x ∉ Ioo (-1 : ℝ) 1, f x * w₁ x = 0 := fun x hx => by
    have : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx ((hball x (hfs h)).1))
    simp [this]
  have hI : ∫ x, f x * w₁ x ∂muL lam = ∫ x, gρ lam x * (f x * w₁ x) :=
    integral_muL lam hvan
  rw [hI]
  have hf0 : 0 < f x₀ := f.pos_of_mem_ball (Metric.mem_ball_self f.rOut_pos)
  have hx₀s : x₀ ∈ tsupport (f : ℝ → ℝ) := subset_tsupport _ hf0.ne'
  have hw1 : w₁ x₀ = w x₀ := (hag x₀ hx₀s).eq_of_nhds.symm
  have hd0 : 0 < gρ lam x₀ := gρ_pos lam hx₀
  have hFx0 : gρ lam x₀ * (f x₀ * w₁ x₀) ≠ 0 := by
    rw [hw1]; exact mul_ne_zero hd0.ne' (mul_ne_zero hf0.ne' hne)
  refine integral_ne_zero_of_sign hF hFc (x₀ := x₀) ?_ hFx0
  have hsgn : ∀ x, (f x ≠ 0) → x ∈ Ioo (-1 : ℝ) 1 ∧ w₁ x = w x ∧ |w x - w x₀| < |w x₀| := by
    intro x hx
    have hxs : x ∈ tsupport (f : ℝ → ℝ) := subset_tsupport _ hx
    have hb := hball x (hfs hxs)
    exact ⟨hb.1, (hag x hxs).eq_of_nhds.symm, hb.2⟩
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · right
    intro x
    by_cases hx : f x = 0
    · simp [hx]
    · obtain ⟨h1, h2, h3⟩ := hsgn x hx
      have hwx : w x < 0 := by
        rw [abs_of_neg hneg] at h3
        have := (abs_lt.1 h3).2
        linarith
      have hdx : 0 ≤ gρ lam x := (gρ_pos lam h1).le
      have hfx : 0 ≤ f x := f.nonneg
      rw [h2]
      have : f x * w x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hfx hwx.le
      exact mul_nonpos_of_nonneg_of_nonpos hdx this
  · left
    intro x
    by_cases hx : f x = 0
    · simp [hx]
    · obtain ⟨h1, h2, h3⟩ := hsgn x hx
      have hwx : 0 < w x := by
        rw [abs_of_pos hpos] at h3
        have := (abs_lt.1 h3).1
        linarith
      have hdx : 0 ≤ gρ lam x := (gρ_pos lam h1).le
      have hfx : 0 ≤ f x := f.nonneg
      rw [h2]
      exact mul_nonneg hdx (mul_nonneg hfx hwx.le)

end MarkovTriple.BGL.Instances.GegenbauerOpen.Core2W
