import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Defs
import MarkovTriple.BGL.Instances.GegenbauerOpen.Curvature
import MarkovTriple.BGL.Instances.Gibbs.FunctPreFull
import MarkovTriple.BGL.Instances.Lebesgue.FullEasy

/-!
# The semigroup-free fields of the zonal Gegenbauer `FullTriple` (R23-G2): `PreFull goDiff goA`

F1, F2, F4, F5, F6 (`Γ`), F7, F9 and the `L`-chain rule F6 (`L`), F3 (closure under smooth composition),
for the extended algebra `goA` (measurable, `C^∞` on `(-1,1)`).  Everything is local calculus: `goL`, `ΓA` at
`x ∈ (-1,1)` only see the germ of `f` at `x`, so one replaces `f` by a globally smooth function that agrees
with it near `x` (`exists_smooth_agree_at`).  See `STATEMENTS_R23_G2.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

/-! ### Locality -/

lemma goL_eventuallyEq {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) : goL f =ᶠ[𝓝 x] goL g := by
  have h1 : deriv f =ᶠ[𝓝 x] deriv g := h.deriv
  have h2 : deriv (deriv f) =ᶠ[𝓝 x] deriv (deriv g) := h1.deriv
  filter_upwards [h1, h2] with y hy1 hy2
  simp only [goL, hy1, hy2]

lemma goL_congr_at {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[𝓝 x] g) : goL f x = goL g x :=
  (goL_eventuallyEq h).eq_of_nhds

lemma goL_zero : goL (0 : ℝ → ℝ) = 0 := by
  funext x; simp [goL]

/-- `ΓA` at `x` only depends on the germs. -/
lemma goΓA_congr_at {f f' g g' : ℝ → ℝ} {x : ℝ} (hf : f =ᶠ[𝓝 x] f') (hg : g =ᶠ[𝓝 x] g') :
    goDiff.ΓA f g x = goDiff.ΓA f' g' x := by
  show (goL (f * g) x - f x * goL g x - g x * goL f x) / 2 =
    (goL (f' * g') x - f' x * goL g' x - g' x * goL f' x) / 2
  rw [goL_congr_at (hf.mul hg), goL_congr_at hg, goL_congr_at hf, hf.eq_of_nhds, hg.eq_of_nhds]

/-- `goL f x` is the formula (definitional). -/
lemma go_L_local (f : ℝ → ℝ) (x : ℝ) :
    goDiff.L f x = (1 - x ^ 2) * deriv (deriv f) x - 4 * x * deriv f x := rfl

lemma exists_smooth_family {k : ℕ} {f : Fin k → ℝ → ℝ} (hf : ∀ i, f i ∈ goA) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ∃ ft : Fin k → ℝ → ℝ, (∀ i, Lebesgue.Sm (ft i)) ∧ ∀ᶠ y in 𝓝 x, ∀ i, f i y = ft i y := by
  have : ∀ i, ∃ g : ℝ → ℝ, Lebesgue.Sm g ∧ f i =ᶠ[𝓝 x] g := fun i =>
    exists_smooth_agree_at (hf i).2 hx
  choose ft hft1 hft2 using this
  exact ⟨ft, hft1, Filter.eventually_all.2 hft2⟩

theorem go_ΓA_local {f g : ℝ → ℝ} (hf : f ∈ goA) (hg : g ∈ goA) :
    ∀ x ∈ Ioo (-1 : ℝ) 1, goDiff.ΓA f g x = (1 - x ^ 2) * (deriv f x * deriv g x) := by
  intro x hx
  obtain ⟨f', hf's, hff'⟩ := exists_smooth_agree_at hf.2 hx
  obtain ⟨g', hg's, hgg'⟩ := exists_smooth_agree_at hg.2 hx
  rw [goΓA_congr_at hff' hgg', go_ΓA hf's hg's, hff'.deriv_eq, hgg'.deriv_eq]

/-- the global-smoothness of `h * f`, `h ∈ C_c^∞((-1,1))`, `f ∈ C^∞((-1,1))`. -/
lemma smooth_mul_goA₀ {h f : ℝ → ℝ} (hh : h ∈ goA₀)
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1)) : Lebesgue.Sm (h * f) := by
  show ContDiff ℝ _ _
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ioo (-1 : ℝ) 1
  · exact (goA₀_smooth hh).contDiffAt.mul (hf.contDiffAt (isOpen_Ioo.mem_nhds hx))
  · have hxs : x ∉ tsupport h := fun h' => hx (hh.2 h')
    have hz : (h * f) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport h).isOpen_compl.mem_nhds hxs] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact (contDiffAt_const).congr_of_eventuallyEq hz

lemma exists_goA₀_agree {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1)) {K : Set ℝ} (hK : IsCompact K)
    (hKI : K ⊆ Ioo (-1 : ℝ) 1) :
    ∃ g ∈ goA₀, ∃ U : Set ℝ, IsOpen U ∧ K ⊆ U ∧ EqOn f g U := by
  obtain ⟨n, hn⟩ := exists_gocut_eq_one hK hKI
  refine ⟨fun x => gocut n x * f x, ⟨smooth_cut_mul hf n, ?_⟩, _, isOpen_Ioo, hn, fun x hx => ?_⟩
  · exact (tsupport_mul_subset_left (f := gocut n) (g := f)).trans (gocut_tsupport n)
  · simp [gocut_eq_one_of_mem hx]

/-! ### F3: composition -/

theorem go_A_comp (k : ℕ) (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ goA) : (fun x => ψ (fun i => f i x)) ∈ goA := by
  refine ⟨?_, ?_⟩
  · exact hψ.continuous.measurable.comp (measurable_pi_iff.2 fun i => (hf i).1)
  · exact hψ.comp_contDiffOn (contDiffOn_pi.2 fun i => (hf i).2)

/-! ### F4 -/

lemma contDiffOn_deriv_goA {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ioo (-1 : ℝ) 1)) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv f) (Ioo (-1 : ℝ) 1) :=
  hf.deriv_of_isOpen isOpen_Ioo (by simp)

theorem go_L_mem_A {f : ℝ → ℝ} (hf : f ∈ goA) : goL f ∈ goA := by
  have h1 := contDiffOn_deriv_goA hf.2
  have h2 := contDiffOn_deriv_goA h1
  refine ⟨?_, ?_⟩
  · have := measurable_deriv (𝕜 := ℝ) f
    have h' := measurable_deriv (𝕜 := ℝ) (deriv f)
    exact ((by fun_prop : Measurable fun x : ℝ => 1 - x ^ 2).mul h').sub
      ((by fun_prop : Measurable fun x : ℝ => 4 * x).mul this)
  · exact ((contDiffOn_const.sub (contDiffOn_id.pow 2)).mul h2).sub
      ((contDiffOn_const.mul contDiffOn_id).mul h1)

/-! ### F5 -/

theorem go_ΓA_nonneg {f : ℝ → ℝ} (hf : f ∈ goA) : 0 ≤ᵐ[goμ] goDiff.ΓA f f :=
  ae_go fun x hx => by
    simp only [Pi.zero_apply]
    rw [go_ΓA_local hf hf x hx]
    exact mul_nonneg (by nlinarith [hx.1, hx.2]) (mul_self_nonneg _)


/-! ### Chain rules at a point -/

lemma go_chain_at {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    {f : Fin k → ℝ → ℝ} (hf : ∀ i, f i ∈ goA) {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    deriv (fun x => ψ (fun i => f i x)) x =
        ∑ i, pderiv ψ i (fun j => f j x) * deriv (f i) x ∧
      goDiff.L (fun x => ψ (fun i => f i x)) x =
        ∑ i, pderiv ψ i (fun j => f j x) * goDiff.L (f i) x +
          ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * goDiff.ΓA (f i) (f j) x := by
  obtain ⟨ft, hft, hev⟩ := exists_smooth_family hf hx
  have hxe : ∀ i, f i x = ft i x := fun i => hev.self_of_nhds i
  have hevi : ∀ i, f i =ᶠ[𝓝 x] ft i := fun i => hev.mono fun y hy => hy i
  have hF : (fun x => ψ (fun i => f i x)) =ᶠ[𝓝 x] fun x => ψ (fun i => ft i x) := by
    filter_upwards [hev] with y hy
    simp only [hy]
  have hdi : ∀ i, deriv (f i) x = deriv (ft i) x := fun i => (hevi i).deriv_eq
  have hfun : (fun j => f j x) = fun j => ft j x := funext hxe
  have hd := congrFun (Lebesgue.deriv_comp1 ψ hψ ft hft) x
  have hc := Lebesgue.diffusion_c k ψ hψ ft hft
  have hc2 := congrFun hc.2 x
  refine ⟨?_, ?_⟩
  · rw [hF.deriv_eq, hd, hfun]
    exact Finset.sum_congr rfl fun i _ => by rw [hdi i]
  · rw [go_L_local, hF.deriv_eq, hF.deriv.deriv_eq]
    have e1 : Lebesgue.Lf (fun x => ψ (fun i => ft i x)) x =
        deriv (deriv fun x => ψ (fun i => ft i x)) x := rfl
    rw [← e1, hc2, hd, hfun]
    have hLi : ∀ i, goL (f i) x =
        (1 - x ^ 2) * Lebesgue.Lf (ft i) x - 4 * x * deriv (ft i) x := by
      intro i
      show (1 - x ^ 2) * deriv (deriv (f i)) x - 4 * x * deriv (f i) x = _
      rw [(hevi i).deriv_eq, (hevi i).deriv.deriv_eq]
      rfl
    have hΓi : ∀ i j, goDiff.ΓA (f i) (f j) x = (1 - x ^ 2) * Lebesgue.Gf (ft i) (ft j) x := by
      intro i j
      rw [go_ΓA_local (hf i) (hf j) x hx, hdi i, hdi j]
      rfl
    simp only [hLi, hΓi]
    have s1 : ∑ i, pderiv ψ i (fun j => ft j x) * ((1 - x ^ 2) * Lebesgue.Lf (ft i) x
        - 4 * x * deriv (ft i) x) = (1 - x ^ 2) *
          ∑ i, pderiv ψ i (fun j => ft j x) * Lebesgue.Lf (ft i) x
          - 4 * x * ∑ i, pderiv ψ i (fun j => ft j x) * deriv (ft i) x := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have s2 : ∑ i, ∑ j, pderiv₂ ψ i j (fun l => ft l x) *
        ((1 - x ^ 2) * Lebesgue.Gf (ft i) (ft j) x)
        = (1 - x ^ 2) * ∑ i, ∑ j, pderiv₂ ψ i j (fun l => ft l x) *
          Lebesgue.Gf (ft i) (ft j) x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [s1, s2]
    ring

theorem go_diffusion_L_A (k : ℕ) (ψ : (Fin k → ℝ) → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ goA) :
    goDiff.L (fun x => ψ (fun i => f i x)) =ᵐ[goμ]
      fun x => ∑ i, pderiv ψ i (fun j => f j x) * goDiff.L (f i) x +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * goDiff.ΓA (f i) (f j) x :=
  ae_go fun _ hx => (go_chain_at ψ hψ hf hx).2

theorem go_diffusion_Γ_A (k : ℕ) (ψ : (Fin k → ℝ) → ℝ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ) (f : Fin k → ℝ → ℝ) (hf : ∀ i, f i ∈ goA)
    {g : ℝ → ℝ} (hg : g ∈ goA) :
    goDiff.ΓA (fun x => ψ (fun i => f i x)) g =ᵐ[goμ]
      fun x => ∑ i, pderiv ψ i (fun j => f j x) * goDiff.ΓA (f i) g x :=
  ae_go fun x hx => by
    rw [go_ΓA_local (go_A_comp k ψ hψ f hf) hg x hx, (go_chain_at ψ hψ hf hx).1, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [go_ΓA_local (hf i) hg x hx]; ring

/-! ### F1 -/

theorem go_ideal {f h : ℝ → ℝ} (hf : f ∈ goA) (hh : h ∈ goA₀) : h * f ∈ goA₀ :=
  ⟨smooth_mul_goA₀ hh hf.2, tsupport_mul_subset_left.trans hh.2⟩

/-! ### F2 -/

theorem go_pos_detect {f : ℝ → ℝ} (hf : f ∈ goA)
    (h : ∀ h ∈ goA₀, 0 ≤ᵐ[goμ] h → 0 ≤ ∫ x, h x * f x ∂goμ) : 0 ≤ᵐ[goμ] f := by
  refine ae_go fun x0 hx0 => ?_
  by_contra hneg
  push Not at hneg
  have hcont : ContinuousOn f (Ioo (-1 : ℝ) 1) := hf.2.continuousOn
  obtain ⟨r, hr, hball⟩ : ∃ r : ℝ, 0 < r ∧ Metric.ball x0 r ⊆ Ioo (-1 : ℝ) 1 ∩ {x | f x < 0} := by
    have hopen : IsOpen (Ioo (-1 : ℝ) 1 ∩ {x | f x < 0}) := by
      have := hcont.isOpen_inter_preimage isOpen_Ioo (isOpen_Iio (a := (0 : ℝ)))
      simpa [Set.preimage] using this
    obtain ⟨r, hr, hb⟩ := Metric.isOpen_iff.1 hopen x0 ⟨hx0, hneg⟩
    exact ⟨r, hr, hb⟩
  let b : ContDiffBump x0 := ⟨r / 4, r / 2, by positivity, by linarith⟩
  have hbsupp : tsupport b ⊆ Metric.closedBall x0 (r / 2) := by
    rw [b.tsupport_eq]
  have hcb : Metric.closedBall x0 (r / 2) ⊆ Metric.ball x0 r :=
    Metric.closedBall_subset_ball (by linarith)
  have hbI : tsupport b ⊆ Ioo (-1 : ℝ) 1 := fun x hx => (hball (hcb (hbsupp hx))).1
  have hbm : (fun x => b x) ∈ goA₀ := ⟨b.contDiff, hbI⟩
  obtain ⟨f', hf's, U, hU, hKU, hfU⟩ := exists_smooth_agree hf.2 (isCompact_closedBall x0 (r / 2))
    (fun x hx => (hball (hcb hx)).1)
  have hb0 : ∀ x, 0 ≤ b x := fun x => b.nonneg
  have hbz : ∀ x, x ∉ Metric.closedBall x0 (r / 2) → b x = 0 := fun x hx =>
    b.zero_of_le_dist (by
      have := not_le.1 (Metric.mem_closedBall.not.1 hx)
      exact this.le)
  have hG : ∀ x, (3 / 4 * (1 - x ^ 2)) * (b x * f x) = (3 / 4 * (1 - x ^ 2)) * (b x * f' x) := by
    intro x
    by_cases hx : x ∈ Metric.closedBall x0 (r / 2)
    · rw [hfU (hKU hx)]
    · rw [hbz x hx]; simp
  have hint : ∫ x, b x * f x ∂goμ = ∫ x, (3 / 4 * (1 - x ^ 2)) * (b x * f' x) := by
    rw [integral_goμ (fun x hx => by
      have : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h' => hx (hbI h'))
      simp [this])]
    exact integral_congr_ae (Filter.Eventually.of_forall hG)
  have hpos : 0 < ∫ x, -((3 / 4 * (1 - x ^ 2)) * (b x * f' x)) := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x0)
      (by have := hf's.continuous; have := b.continuous; fun_prop) ?_ (fun x => ?_) ?_
    · refine HasCompactSupport.neg (HasCompactSupport.mul_left ?_)
      exact b.hasCompactSupport.mul_right
    · by_cases hx : x ∈ Metric.closedBall x0 (r / 2)
      · have h1 := hball (hcb hx)
        have : 0 ≤ 1 - x ^ 2 := by nlinarith [h1.1.1, h1.1.2]
        have h2 : f' x < 0 := by rw [← hfU (hKU hx)]; exact h1.2
        have h3 : (3 / 4 * (1 - x ^ 2)) * (b x * (-f' x)) ≥ 0 :=
          mul_nonneg (by linarith) (mul_nonneg (hb0 x) (by linarith))
        show 0 ≤ -((3 / 4 * (1 - x ^ 2)) * (b x * f' x))
        linarith
      · show 0 ≤ -((3 / 4 * (1 - x ^ 2)) * (b x * f' x))
        simp [hbz x hx]
    · have h1 : 0 < b x0 := b.pos_of_mem_ball (Metric.mem_ball_self b.rOut_pos)
      have h2 : f' x0 < 0 := by
        rw [← hfU (hKU (Metric.mem_closedBall_self (by linarith)))]; exact hneg
      have h3 : 0 < 1 - x0 ^ 2 := by nlinarith [hx0.1, hx0.2]
      have : 0 < (3 / 4 * (1 - x0 ^ 2)) * (b x0 * (-f' x0)) :=
        mul_pos (by linarith) (mul_pos h1 (by linarith))
      show -((3 / 4 * (1 - x0 ^ 2)) * (b x0 * f' x0)) ≠ 0
      intro h0
      linarith
  have := h _ hbm (Filter.Eventually.of_forall hb0)
  rw [hint] at this
  rw [integral_neg] at hpos
  linarith

/-! ### F7 -/

lemma go_agree_ibp {f g : ℝ → ℝ} (hf : f ∈ goA) (hg : g ∈ goA₀) :
    ∃ ft ∈ goA₀, goDiff.ΓA f g = goΓ ft g ∧ (fun x => g x * goL f x) = (fun x => g x * goL ft x) ∧
      (fun x => f x * goL g x) = (fun x => ft x * goL g x) := by
  have hK : IsCompact (tsupport g) := goA₀_cs hg
  obtain ⟨ft, hft, U, hU, hKU, hfU⟩ := exists_goA₀_agree hf.2 hK hg.2
  have hgz : ∀ x, x ∉ U → g =ᶠ[𝓝 x] (0 : ℝ → ℝ) := fun x hx => by
    have hxs : x ∉ tsupport g := fun h' => hx (hKU h')
    filter_upwards [(isClosed_tsupport g).isOpen_compl.mem_nhds hxs] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  have hdz : ∀ x, x ∉ U → deriv g x = 0 := fun x hx => by
    rw [(hgz x hx).deriv_eq]; simp
  have hLz : ∀ x, x ∉ U → goL g x = 0 := fun x hx => by
    rw [goL_congr_at (hgz x hx), goL_zero]; rfl
  refine ⟨ft, hft, ?_, ?_, ?_⟩
  · funext x
    by_cases hx : x ∈ U
    · have hev : f =ᶠ[𝓝 x] ft := Filter.mem_of_superset (hU.mem_nhds hx) hfU
      rw [goΓA_congr_at hev (Filter.EventuallyEq.refl _ g),
        go_ΓA (goA₀_smooth hft) (goA₀_smooth hg)]
      rfl
    · rw [goΓA_congr_at (Filter.EventuallyEq.refl _ f) (hgz x hx)]
      show (goL (f * 0) x - f x * goL 0 x - 0 * goL f x) / 2 = _
      have h0 : goL (0 : ℝ → ℝ) x = 0 := congrFun goL_zero x
      simp [goΓ, hdz x hx, h0]
  · funext x
    by_cases hx : x ∈ U
    · have hev : f =ᶠ[𝓝 x] ft := Filter.mem_of_superset (hU.mem_nhds hx) hfU
      rw [goL_congr_at hev]
    · rw [image_eq_zero_of_notMem_tsupport (fun h' => hx (hKU h'))]; simp
  · funext x
    by_cases hx : x ∈ U
    · rw [hfU hx]
    · rw [hLz x hx]; simp

theorem go_ibp_A {f g : ℝ → ℝ} (hf : f ∈ goA) (hg : g ∈ goA₀) :
    ∫ x, goDiff.ΓA f g x ∂goμ = -∫ x, g x * goDiff.L f x ∂goμ ∧
    ∫ x, goDiff.ΓA f g x ∂goμ = -∫ x, f x * goDiff.L g x ∂goμ := by
  obtain ⟨ft, hft, e1, e2, e3⟩ := go_agree_ibp hf hg
  have h1 : ∫ x, g x * goL f x ∂goμ = ∫ x, g x * goL ft x ∂goμ := by rw [e2]
  have h2 : ∫ x, f x * goL g x ∂goμ = ∫ x, ft x * goL g x ∂goμ := by rw [e3]
  have i1 := integral_go_L (goA₀_smooth hft) hg
  have i2 := integral_go_L (goA₀_smooth hg) hft
  have hs : goΓ g ft = goΓ ft g := funext fun x => by simp [goΓ, mul_comm]
  rw [hs] at i2
  rw [e1]
  show ∫ x, goΓ ft g x ∂goμ = -∫ x, g x * goL f x ∂goμ ∧
    ∫ x, goΓ ft g x ∂goμ = -∫ x, f x * goL g x ∂goμ
  rw [h1, h2]
  exact ⟨by linarith, by linarith⟩

/-! ### F9 -/

theorem go_connected {f : ℝ → ℝ} (hf : f ∈ goA) (h0 : goDiff.ΓA f f =ᵐ[goμ] 0) :
    ∃ c : ℝ, f =ᵐ[goμ] fun _ => c := by
  have h1 : ∀ᵐ x ∂goμ, goDiff.ΓA f f x = 0 := h0
  have h2 := (ae_withDensity_iff measurable_goρ).1 h1
  have h3 : ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), deriv f x = 0 := by
    refine (ae_restrict_iff' measurableSet_Ioo).2 ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Ioo).1 h2] with x hx hxI
    have hne : ENNReal.ofReal (3 / 4 * (1 - x ^ 2)) ≠ 0 := by
      rw [Ne, ENNReal.ofReal_eq_zero, not_le]; nlinarith [hxI.1, hxI.2]
    have := hx hxI hne
    rw [go_ΓA_local hf hf x hxI] at this
    have hw : (1 - x ^ 2) ≠ 0 := by nlinarith [hxI.1, hxI.2]
    have := (mul_eq_zero.1 this).resolve_left hw
    exact mul_self_eq_zero.1 this
  have h4 : Set.EqOn (deriv f) 0 (Ioo (-1 : ℝ) 1) :=
    Measure.eqOn_open_of_ae_eq (μ := volume) h3 isOpen_Ioo (contDiffOn_deriv_goA hf.2).continuousOn
      continuousOn_const
  have h5 : ∀ {x y : ℝ}, x ∈ Ioo (-1 : ℝ) 1 → y ∈ Ioo (-1 : ℝ) 1 → f x = f y :=
    isOpen_Ioo.is_const_of_deriv_eq_zero (isPreconnected_Ioo)
    (hf.2.differentiableOn (by simp)) h4
  refine ⟨f 0, ae_go fun x hx => ?_⟩
  exact h5 hx ⟨by norm_num, by norm_num⟩

/-- **`PreFull goDiff goA`** : the semigroup-free fields F1, F2, F4, F5, F6 (`Γ`), F7, F9. -/
theorem goPreFull : PreFull goDiff goA where
  A₀_le := fun _ hf => goA₀_le_goA hf
  A_measurable := fun _ hf => hf.1
  ideal := fun _ hf _ hh => go_ideal hf hh
  pos_detect := fun _ hf h => go_pos_detect hf h
  L_mem_A := fun _ hf => go_L_mem_A hf
  ΓA_nonneg := fun _ hf => go_ΓA_nonneg hf
  diffusion_Γ_A := fun k ψ hψ f hf _ hg => go_diffusion_Γ_A k ψ hψ f hf hg
  ibp_A := fun _ hf _ hg => go_ibp_A hf hg
  connected := fun _ hf h => go_connected hf h

end MarkovTriple.BGL.Instances.GegenbauerOpen
