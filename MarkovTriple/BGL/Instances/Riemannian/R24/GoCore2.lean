import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Final
import MarkovTriple.BGL.Instances.Riemannian.R24.Core2Criterion

/-!
# Round 24 (stream D), part B: a deficiency pair refutes `Core2` for the non-complete triple `goFullTriple`

`goFullTriple` is the zonal Gegenbauer triple `λ = 3/2` (`S⁴` minus its poles; R23-F-1).  Here:
`go_not_core2_of_pair` : if `w, h` are smooth on `(-1,1)` with `L w = w`, `h ∈ L²(μ)`, `w - L h ∈ L²(μ)` and
`w ≢ 0`, then `¬ goFullTriple.Core2`.  The existence of such a pair (Frobenius analysis at the endpoints,
`h = (F₁/8) log(1-x) - (F₋₁/8) log(1+x)`) is NOT proved here: see `STATEMENTS_R24_D.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

open MarkovTriple.BGL

lemma goL_eq_of_eventuallyEq {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) : goL f x = goL g x := by
  have h1 : deriv f =ᶠ[𝓝 x] deriv g := h.deriv
  simp only [goL, h.deriv_eq, h1.deriv_eq]

lemma goL_zero_off {c : ℝ → ℝ} {x : ℝ} (hx : x ∉ tsupport c) : goL c x = 0 := by
  have h0 : deriv c x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (tsupport_deriv_subset h))
  have h1 : deriv (deriv c) x = 0 :=
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (tsupport_deriv_subset (tsupport_deriv_subset h)))
  simp [goL, h0, h1]

lemma integrable_goA₀ {f : ℝ → ℝ} (hf : f ∈ goA₀) : Integrable f goμ :=
  (goA₀_smooth hf).continuous.integrable_of_hasCompactSupport (goA₀_cs hf)

lemma sym_A₀ {f g : ℝ → ℝ} (hf : f ∈ goA₀) (hg : g ∈ goA₀) :
    ∫ x, f x * goL g x ∂goμ = ∫ x, goL f x * g x ∂goμ := by
  have h1 := integral_go_L (goA₀_smooth hg) hf
  have h2 := integral_go_L (goA₀_smooth hf) hg
  have e : ∫ x, goΓ g f x ∂goμ = ∫ x, goΓ f g x ∂goμ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [goΓ, mul_comm])
  have e2 : ∫ x, goL f x * g x ∂goμ = ∫ x, g x * goL f x ∂goμ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  rw [e2, h1, h2, e]

/-- local replacement of a function smooth on `(-1,1)` by an element of `𝒜₀`. -/
lemma loc_agree {f : ℝ → ℝ} (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1))
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ f₁ ∈ goA₀, ∀ x ∈ K, f =ᶠ[𝓝 x] f₁ := by
  obtain ⟨n, hn⟩ := exists_gocut_eq_one hK hKI
  refine ⟨fun x => gocut n x * f x,
    ⟨smooth_cut_mul hf n, tsupport_mul_subset_left.trans (gocut_tsupport n)⟩, fun x hx => ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds (hn hx)] with y hy
  simp [gocut_eq_one_of_mem hy]

/-- the key computation: for `c ∈ 𝒜₀` supported in `K`, `∫ c (w - Lh) + ∫ (Lc) h = ∫ c w₁`,
`w₁ ∈ 𝒜₀` a local copy of `w` (and the two integrals on the left exist). -/
lemma key {w h : ℝ → ℝ} (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1)) {c : ℝ → ℝ} (hc : c ∈ goA₀)
    {K : Set ℝ} (hK : IsCompact K) (hKI : K ⊆ Ioo (-1 : ℝ) 1) (hcK : tsupport c ⊆ K) :
    ∃ w₁ ∈ goA₀, (∀ x ∈ K, w =ᶠ[𝓝 x] w₁) ∧
      ∫ x, c x * (w x - goL h x) ∂goμ + ∫ x, goL c x * h x ∂goμ = ∫ x, c x * w₁ x ∂goμ := by
  obtain ⟨w₁, hw₁, hwa⟩ := loc_agree hw hK hKI
  obtain ⟨h₁, hh₁, hha⟩ := loc_agree hh hK hKI
  refine ⟨w₁, hw₁, hwa, ?_⟩
  have hpt1 : ∀ x, c x * (w x - goL h x) = c x * w₁ x - c x * goL h₁ x := by
    intro x
    by_cases hx : x ∈ tsupport c
    · have e1 : w x = w₁ x := (hwa x (hcK hx)).eq_of_nhds
      have e3 : goL h x = goL h₁ x := goL_eq_of_eventuallyEq (hha x (hcK hx))
      rw [e1, e3]; ring
    · have e1 : c x = 0 := image_eq_zero_of_notMem_tsupport hx
      rw [e1]; ring
  have hpt2 : ∀ x, goL c x * h x = goL c x * h₁ x := by
    intro x
    by_cases hx : x ∈ tsupport c
    · rw [(hha x (hcK hx)).eq_of_nhds]
    · rw [goL_zero_off hx]; ring
  have i1 : Integrable (fun x => c x * w₁ x) goμ :=
    integrable_goA₀ (goA₀.mul_mem hc hw₁)
  have i2 : Integrable (fun x => c x * goL h₁ x) goμ :=
    integrable_goA₀ (goA₀.mul_mem hc (goL_mem hh₁))
  simp_rw [hpt1, hpt2]
  rw [integral_sub i1 i2, sym_A₀ hc hh₁]
  ring

lemma integral_ne_zero_of_sign {F : ℝ → ℝ} (hF : Continuous F) (hc : HasCompactSupport F) {x₀ : ℝ}
    (hs : (∀ x, 0 ≤ F x) ∨ (∀ x, F x ≤ 0)) (h0 : F x₀ ≠ 0) : ∫ x, F x ≠ 0 := by
  rcases hs with hs | hs
  · have := hF.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) (x := x₀) hc hs h0
    exact this.ne'
  · have hF' : Continuous (fun x => -F x) := hF.neg
    have := hF'.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) (x := x₀) hc.neg
      (fun x => neg_nonneg.2 (hs x)) (by simpa using h0)
    rw [integral_neg] at this
    linarith


/-- a test function in `𝒜₀` detecting a point where `w ≠ 0`. -/
lemma exists_test {w : ℝ → ℝ} (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1)) {x₀ : ℝ}
    (hx₀ : x₀ ∈ Ioo (-1 : ℝ) 1) (hne : w x₀ ≠ 0) :
    ∃ a ∈ goA₀, ∀ w₁ ∈ goA₀, (∀ x ∈ tsupport a, w =ᶠ[𝓝 x] w₁) → ∫ x, a x * w₁ x ∂goμ ≠ 0 := by
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
  have hF : Continuous (fun x => 3 / 4 * (1 - x ^ 2) * (f x * w₁ x)) :=
    (by fun_prop : Continuous fun x : ℝ => 3 / 4 * (1 - x ^ 2)).mul
      (f.continuous.mul (goA₀_smooth hw₁).continuous)
  have hFc : HasCompactSupport (fun x => 3 / 4 * (1 - x ^ 2) * (f x * w₁ x)) := by
    have h1 : HasCompactSupport (fun x => f x * w₁ x) := f.hasCompactSupport.mul_right
    exact h1.mul_left
  have hvan : ∀ x ∉ Ioo (-1 : ℝ) 1, f x * w₁ x = 0 := fun x hx => by
    have : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx ((hball x (hfs h)).1))
    simp [this]
  have hI : ∫ x, f x * w₁ x ∂goμ = ∫ x, 3 / 4 * (1 - x ^ 2) * (f x * w₁ x) :=
    integral_goμ hvan
  rw [hI]
  have hf0 : 0 < f x₀ := f.pos_of_mem_ball (Metric.mem_ball_self f.rOut_pos)
  have hx₀s : x₀ ∈ tsupport (f : ℝ → ℝ) := subset_tsupport _ hf0.ne'
  have hw1 : w₁ x₀ = w x₀ := (hag x₀ hx₀s).eq_of_nhds.symm
  have hd0 : 0 < 3 / 4 * (1 - x₀ ^ 2) := by nlinarith [hx₀.1, hx₀.2]
  have hFx0 : 3 / 4 * (1 - x₀ ^ 2) * (f x₀ * w₁ x₀) ≠ 0 := by
    rw [hw1]; exact mul_ne_zero hd0.ne' (mul_ne_zero hf0.ne' hne)
  refine integral_ne_zero_of_sign hF hFc (x₀ := x₀) ?_ hFx0
  -- sign
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
      have hdx : 0 ≤ 3 / 4 * (1 - x ^ 2) := by nlinarith [h1.1, h1.2]
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
      have hdx : 0 ≤ 3 / 4 * (1 - x ^ 2) := by nlinarith [h1.1, h1.2]
      have hfx : 0 ≤ f x := f.nonneg
      rw [h2]
      exact mul_nonneg hdx (mul_nonneg hfx hwx.le)

lemma goT_μ : goFullTriple.μ = goμ := rfl

lemma goT_L (f : ℝ → ℝ) : goFullTriple.L f = goL f := rfl

lemma goT_mem (b : goFullTriple.A₀) : b.1 ∈ goA₀ := b.2

/-- **D-B1.  A deficiency pair refutes `Core2` for `goFullTriple`.**  Let `w, h` be smooth on `(-1,1)`, `L w = w`
there, `h ∈ L²(μ)`, `w - L h ∈ L²(μ)`, and `w ≢ 0`.  Then `Core2` fails for the non-complete triple
`goFullTriple` (the pair `(g,h) = (w - L h, h)` is orthogonal to `((1-L)b, L(1-L)b)` for all `b ∈ 𝒜₀` but
pairs to `∫ a w ≠ 0` with a suitable `a ∈ 𝒜₀`). -/
theorem go_not_core2_of_pair (w h : ℝ → ℝ)
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1))
    (hwL : ∀ x ∈ Ioo (-1 : ℝ) 1, goL w x = w x)
    (hh2 : MemLp h 2 goμ) (hg2 : MemLp (fun x => w x - goL h x) 2 goμ)
    (hne : ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0) : ¬ goFullTriple.Core2 := by
  intro hC
  obtain ⟨x₀, hx₀, hx₀ne⟩ := hne
  have hh2' : MemLp h 2 goFullTriple.μ := hh2
  have hg2' : MemLp (fun x => w x - goL h x) 2 goFullTriple.μ := hg2
  -- the sum of the two pairings, as a single functional of `c ∈ 𝒜₀`
  have hpair : ∀ c : goFullTriple.A₀,
      inner ℝ (goFullTriple.toDiffusionTriple.cls c) (hg2'.toLp _) +
        inner ℝ (goFullTriple.toDiffusionTriple.Lcls c) (hh2'.toLp h) =
      ∫ x, c.1 x * (w x - goL h x) ∂goμ + ∫ x, goL c.1 x * h x ∂goμ := by
    intro c
    rw [FullTriple.inner_cls_f hg2', FullTriple.inner_Lcls_f hh2']
    rfl
  have hb : ∀ b : goFullTriple.A₀,
      inner ℝ (goFullTriple.toDiffusionTriple.cls b - goFullTriple.toDiffusionTriple.Lcls b)
          (hg2'.toLp _) +
        inner ℝ (goFullTriple.toDiffusionTriple.Lcls b - FullTriple.LLₗ goFullTriple b)
          (hh2'.toLp h) = 0 := by
    intro b
    rw [← FullTriple.cls_Iₐ, ← FullTriple.Lcls_Iₐ, hpair]
    have hb0 : b.1 ∈ goA₀ := b.2
    have hc : (FullTriple.Iₐ goFullTriple b).1 ∈ goA₀ := (FullTriple.Iₐ goFullTriple b).2
    have hK : IsCompact (tsupport b.1) := goA₀_cs hb0
    have hsub : tsupport (FullTriple.Iₐ goFullTriple b).1 ⊆ tsupport b.1 := by
      refine closure_minimal (fun x hx => ?_) (isClosed_tsupport _)
      by_contra hxn
      apply hx
      show b.1 x - goL b.1 x = 0
      rw [image_eq_zero_of_notMem_tsupport hxn, goL_zero_off hxn]; ring
    obtain ⟨w₁, hw₁, hwa, hI⟩ := key hw hh hc hK hb0.2 hsub
    rw [hI]
    have i1 : Integrable (fun x => b.1 x * w₁ x) goμ := integrable_goA₀ (goA₀.mul_mem hb0 hw₁)
    have i2 : Integrable (fun x => goL b.1 x * w₁ x) goμ :=
      integrable_goA₀ (goA₀.mul_mem (goL_mem hb0) hw₁)
    have e1 : ∫ x, (FullTriple.Iₐ goFullTriple b).1 x * w₁ x ∂goμ =
        ∫ x, b.1 x * w₁ x ∂goμ - ∫ x, goL b.1 x * w₁ x ∂goμ := by
      rw [← integral_sub i1 i2]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show (b.1 x - goL b.1 x) * w₁ x = _
      ring
    have e2 : ∫ x, b.1 x * goL w₁ x ∂goμ = ∫ x, b.1 x * w₁ x ∂goμ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      show b.1 x * goL w₁ x = b.1 x * w₁ x
      by_cases hx : x ∈ tsupport b.1
      · have h1 : goL w₁ x = goL w x := (goL_eq_of_eventuallyEq (hwa x hx)).symm
        have h2 : w x = w₁ x := (hwa x hx).eq_of_nhds
        rw [h1, hwL x (hb0.2 hx), h2]
      · rw [image_eq_zero_of_notMem_tsupport hx]; ring
    rw [e1, ← sym_A₀ hb0 hw₁, e2]; ring
  -- the test function
  obtain ⟨a, ha, hta⟩ := exists_test hw hx₀ hx₀ne
  have hz := FullTriple.core2_orth hC (hg2'.toLp _) (hh2'.toLp h) hb ⟨a, ha⟩
  rw [hpair] at hz
  obtain ⟨w₁, hw₁, hwa, hI⟩ := key hw hh ha (goA₀_cs ha) ha.2 (subset_refl _)
  exact hta w₁ hw₁ hwa (by rw [← hI]; exact hz)

end MarkovTriple.BGL.Instances.GegenbauerOpen
