import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Full.Defs
import MarkovTriple.BGL.Instances.Gibbs.RegAnalysis

/-!
# Local one-dimensional elliptic regularity for the zonal Gegenbauer operator (R23-G2)

Local version (test functions in `C_c^∞((-1,1))`, weight `W = (1-x²)²`) of `Gibbs/RegCore` + `Gibbs/RegBridge`:
a weak solution `u ∈ L¹(goμ)` of `goL u = h` (`h ∈ L¹(goμ)`) is `C¹` on `(-1,1)`, with
`(1-x²)² U' = c + ∫₀ˣ (1-y²) h`, and `C^{j+2}` if `h` is `C^j` there.
-/

open MeasureTheory Filter Topology Set

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

/-- the weight `W = (1-x²)²`. -/
noncomputable def goW (x : ℝ) : ℝ := (1 - x ^ 2) ^ 2

lemma goW_sm : Lebesgue.Sm goW := sm_w2

lemma goW_ne {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : goW x ≠ 0 := by
  unfold goW
  have : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  positivity

/-! ### Test functions -/

/-- antiderivative of a zero-mean smooth function vanishing for `|x| ≥ R`, supported in `[-R,R]`. -/
lemma exists_antideriv_loc {b : ℝ → ℝ} (hb : Lebesgue.Sm b) {R : ℝ} (hR : 0 < R)
    (hRb : ∀ x, R ≤ |x| → b x = 0) (h0 : ∫ x, b x = 0) :
    ∃ a : ℝ → ℝ, Lebesgue.Sm a ∧ tsupport a ⊆ Icc (-R) R ∧ ∀ x, HasDerivAt a (b x) x := by
  set a : ℝ → ℝ := fun x => ∫ y in (-R)..x, b y with ha
  have hder : ∀ x, HasDerivAt a (b x) x := fun x =>
    (hb.continuous.integral_hasStrictDerivAt (-R) x).hasDerivAt
  have hderiv : deriv a = b := funext fun x => (hder x).deriv
  have hSm : Lebesgue.Sm a := by
    refine contDiff_infty_iff_deriv.2 ⟨fun x => (hder x).differentiableAt, ?_⟩
    rw [hderiv]; exact hb
  refine ⟨a, hSm, ?_, hder⟩
  have hzero : ∀ x, x ∉ Icc (-R) R → a x = 0 := by
    intro x hx
    rw [mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hx | hx
    · simp only [ha]
      have : ∫ y in (-R)..x, b y = ∫ y in (-R)..x, (0:ℝ) := by
        refine intervalIntegral.integral_congr (fun y hy => ?_)
        rw [uIcc_of_ge hx.le] at hy
        exact hRb y (by rw [abs_of_nonpos (by linarith [hy.2])]; linarith [hy.2])
      rw [this]; simp
    · simp only [ha]
      have h1 : ∫ y in (-R)..x, b y = ∫ y, b y := by
        rw [intervalIntegral.integral_of_le (by linarith)]
        refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)
        rw [mem_Ioc, not_and_or, not_lt, not_le] at hy
        rcases hy with hy | hy
        · exact hRb y (by rw [abs_of_nonpos (by linarith)]; linarith)
        · exact hRb y (by rw [abs_of_nonneg (by linarith)]; linarith)
      rw [h1, h0]
  exact closure_minimal (fun y hy => by
    by_contra hy'; exact hy (hzero y hy')) isClosed_Icc

/-- an element of `C_c^∞((-1,1))` vanishes for `|x| ≥ R`, some `0 < R < 1`. -/
lemma exists_R_of_goA₀ {b : ℝ → ℝ} (hb : b ∈ goA₀) :
    ∃ R : ℝ, 0 < R ∧ R < 1 ∧ ∀ x, R ≤ |x| → b x = 0 := by
  obtain ⟨n, hn⟩ := exists_gocut_eq_one (K := tsupport b) (goA₀_cs hb) hb.2
  have hpos : 0 < 4 / ((n : ℝ) + 1) := by positivity
  refine ⟨max (1 - 4 / ((n : ℝ) + 1)) (1 / 2), lt_max_of_lt_right (by norm_num),
    max_lt (by linarith) (by norm_num), fun x hx => ?_⟩
  by_contra hne
  have hxs : x ∈ tsupport b := subset_tsupport _ (Function.mem_support.2 hne)
  have := hn hxs
  have h1 : 1 - 4 / ((n : ℝ) + 1) ≤ |x| := le_trans (le_max_left _ _) hx
  rcases abs_cases x with ⟨h2, _⟩ | ⟨h2, _⟩ <;> linarith [this.1, this.2]

/-- zero-mean elements of `C_c^∞((-1,1))` are derivatives of such. -/
lemma exists_antideriv_goA₀ {b : ℝ → ℝ} (hb : b ∈ goA₀) (h0 : ∫ x, b x = 0) :
    ∃ a ∈ goA₀, ∀ x, HasDerivAt a (b x) x := by
  obtain ⟨R, hR0, hR1, hRb⟩ := exists_R_of_goA₀ hb
  obtain ⟨a, haS, haT, had⟩ := exists_antideriv_loc hb.1 hR0 hRb h0
  exact ⟨a, ⟨haS, haT.trans (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)⟩, had⟩

lemma exists_bump_go : ∃ φ0 ∈ goA₀, ∫ x, φ0 x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hpos : 0 < ∫ x, b x := b.integral_pos
  have hb : (fun x => b x) ∈ goA₀ := by
    refine ⟨b.contDiff, ?_⟩
    have : tsupport (fun x => b x) = Metric.closedBall 0 (1 / 2) := b.tsupport_eq
    rw [this]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx
    have := abs_le.1 hx
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  refine ⟨fun x => (∫ x, b x)⁻¹ * b x, ?_, ?_⟩
  · have := goA₀.smul_mem (∫ x, b x)⁻¹ hb
    exact this
  · rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

local notation "𝕀" => Ioo (-1 : ℝ) 1

/-- local integrability on compact subsets of `(-1,1)`. -/
def LocInt (u : ℝ → ℝ) : Prop := ∀ K : Set ℝ, K ⊆ 𝕀 → IsCompact K → IntegrableOn u K

lemma LocInt.of_continuousOn {g : ℝ → ℝ} (hg : ContinuousOn g 𝕀) : LocInt g :=
  fun _ hK hKc => (hg.mono hK).integrableOn_compact hKc

lemma integrable_mul_T {g : ℝ → ℝ} (hg : LocInt g) {ψ : ℝ → ℝ} (hψ : ψ ∈ goA₀) :
    Integrable (fun x => g x * ψ x) := by
  have h1 : IntegrableOn (fun x => g x * ψ x) (tsupport ψ) :=
    (hg _ hψ.2 (goA₀_cs hψ)).mul_continuousOn hψ.1.continuous.continuousOn (goA₀_cs hψ)
  refine h1.integrable_of_forall_notMem_eq_zero fun x hx => ?_
  simp [image_eq_zero_of_notMem_tsupport hx]

lemma sm_mul_inv_W {φ : ℝ → ℝ} (hφ : φ ∈ goA₀) : (fun x => φ x * (goW x)⁻¹) ∈ goA₀ := by
  refine ⟨?_, (tsupport_mul_subset_left (f := φ) (g := fun x => (goW x)⁻¹)).trans hφ.2⟩
  show ContDiff ℝ _ _
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ 𝕀
  · exact (hφ.1.contDiffAt).mul ((goW_sm.contDiffAt).inv (goW_ne hx))
  · have hxs : x ∉ tsupport φ := fun h => hx (hφ.2 h)
    have hz : (fun x => φ x * (goW x)⁻¹) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxs] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    exact contDiffAt_const.congr_of_eventuallyEq hz

lemma W_mul_inv {φ : ℝ → ℝ} (hφ : φ ∈ goA₀) : (fun x => goW x * (φ x * (goW x)⁻¹)) = φ := by
  funext x
  by_cases hx : x ∈ 𝕀
  · field_simp [goW_ne hx]
  · simp [zero_off_go hφ hx]

/-- **local du Bois-Reymond lemma** on `(-1,1)`. -/
theorem du_bois_reymond_loc {g : ℝ → ℝ} (hg : LocInt g)
    (h : ∀ φ ∈ goA₀, ∫ x, g x * deriv φ x = 0) :
    ∃ c : ℝ, ∀ᵐ x, x ∈ 𝕀 → g x = c := by
  obtain ⟨φ0, hφ0, hφ0i⟩ := exists_bump_go
  set c : ℝ := ∫ x, g x * φ0 x with hcdef
  refine ⟨c, ?_⟩
  have hzero : ∀ ψ ∈ goA₀, ∫ x, ψ x • (g x - c) = 0 := by
    intro ψ hψ
    set m : ℝ := ∫ x, ψ x with hm
    have hb : (fun x => ψ x - m * φ0 x) ∈ goA₀ := by
      have := sub_mem hψ (goA₀.smul_mem m hφ0); exact this
    have hψi : Integrable ψ := hψ.1.continuous.integrable_of_hasCompactSupport (goA₀_cs hψ)
    have hφi : Integrable φ0 := hφ0.1.continuous.integrable_of_hasCompactSupport (goA₀_cs hφ0)
    have hb0 : ∫ x, (ψ x - m * φ0 x) = 0 := by
      rw [integral_sub hψi (hφi.const_mul m), integral_const_mul, hφ0i]; simp [hm]
    obtain ⟨a, ha, had⟩ := exists_antideriv_goA₀ hb hb0
    have hda : deriv a = fun x => ψ x - m * φ0 x := funext fun x => (had x).deriv
    have h1 := h a ha
    rw [hda] at h1
    have i1 := integrable_mul_T hg hψ
    have i2 := integrable_mul_T hg hφ0
    have e1 : ∫ x, g x * (ψ x - m * φ0 x) = (∫ x, g x * ψ x) - m * c := by
      have : ∀ x, g x * (ψ x - m * φ0 x) = g x * ψ x - m * (g x * φ0 x) := fun x => by ring
      simp_rw [this]
      rw [integral_sub i1 (i2.const_mul m), integral_const_mul]
    rw [e1] at h1
    have e2 : ∫ x, ψ x • (g x - c) = (∫ x, g x * ψ x) - c * m := by
      have : ∀ x, ψ x • (g x - c) = g x * ψ x - c * ψ x := fun x => by
        simp only [smul_eq_mul]; ring
      simp_rw [this]
      rw [integral_sub i1 (hψi.const_mul c), integral_const_mul]
    rw [e2]; linarith
  have hloc : LocallyIntegrableOn (fun x => g x - c) 𝕀 volume := by
    rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
    intro K hK hKc
    exact (hg K hK hKc).sub (continuousOn_const.integrableOn_compact hKc)
  have := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun ψ hψ hc hs => hzero ψ ⟨hψ, hs⟩)
  filter_upwards [this] with x hx hxI
  have := hx hxI
  linarith

/-- **Local regularity, first step**, `dx`-form. -/
theorem reg_loc_C1 {u F : ℝ → ℝ} (hu : LocInt u) (hF : Integrable F volume)
    (hweak : ∀ a ∈ goA₀, ∫ x, u x * deriv (fun x => goW x * deriv a x) x = ∫ x, F x * a x) :
    ∃ (U : ℝ → ℝ) (c : ℝ), ContDiffOn ℝ 1 U 𝕀 ∧ (∀ᵐ x, x ∈ 𝕀 → u x = U x) ∧
      ∀ x ∈ 𝕀, goW x * deriv U x = c + ∫ y in (0:ℝ)..x, F y := by
  set H : ℝ → ℝ := fun x => ∫ y in (0:ℝ)..x, F y with hH
  have hHc : Continuous H :=
    intervalIntegral.continuous_primitive (fun a b => hF.intervalIntegrable) 0
  have hWb : ∀ b ∈ goA₀, (fun x => goW x * b x) ∈ goA₀ := fun b hb => smul_mem_goA₀ goW_sm hb
  have hI2 : ∀ b ∈ goA₀, Integrable (fun x => H x * b x) :=
    fun b hb => (hHc.mul hb.1.continuous).integrable_of_hasCompactSupport (goA₀_cs hb).mul_left
  have step1 : ∀ b ∈ goA₀, ∫ x, b x = 0 →
      ∫ x, u x * deriv (fun x => goW x * b x) x = -∫ x, H x * b x := by
    intro b hb hb0
    obtain ⟨a, ha, had⟩ := exists_antideriv_goA₀ hb hb0
    have hda : deriv a = b := funext fun x => (had x).deriv
    have h1 := hweak a ha
    rw [Gibbs.integral_mul_eq_neg_integral_primitive hF ha.1 (goA₀_cs ha)] at h1
    simp only [hda] at h1
    exact h1
  obtain ⟨φ0, hφ0, hφ0i⟩ := exists_bump_go
  set c0 : ℝ := (∫ x, u x * deriv (fun x => goW x * φ0 x) x) + ∫ x, H x * φ0 x with hc0
  have step2 : ∀ b ∈ goA₀, (∫ x, u x * deriv (fun x => goW x * b x) x) + ∫ x, H x * b x =
      (∫ x, b x) * c0 := by
    intro b hb
    set m : ℝ := ∫ x, b x with hm
    have hbi : Integrable b := hb.1.continuous.integrable_of_hasCompactSupport (goA₀_cs hb)
    have hφi : Integrable φ0 := hφ0.1.continuous.integrable_of_hasCompactSupport (goA₀_cs hφ0)
    have hb' : (fun x => b x - m * φ0 x) ∈ goA₀ := by
      have := sub_mem hb (goA₀.smul_mem m hφ0); exact this
    have hb0 : ∫ x, (b x - m * φ0 x) = 0 := by
      rw [integral_sub hbi (hφi.const_mul m), integral_const_mul, hφ0i]; simp [hm]
    have h1 := step1 _ hb' hb0
    have hd : ∀ x, deriv (fun y => goW y * (b y - m * φ0 y)) x =
        deriv (fun y => goW y * b y) x - m * deriv (fun y => goW y * φ0 y) x := by
      intro x
      have e : (fun y => goW y * (b y - m * φ0 y)) =
          fun y => goW y * b y - m * (goW y * φ0 y) := by funext y; ring
      rw [e]
      have h1 := ((goW_sm.mul hb.1).differentiable (by simp) x).hasDerivAt
      have h2 := ((goW_sm.mul hφ0.1).differentiable (by simp) x).hasDerivAt
      exact (h1.sub (h2.const_mul m)).deriv
    simp_rw [hd] at h1
    have i1 := integrable_mul_T hu (deriv_mem_goA₀ (hWb b hb))
    have i2 := integrable_mul_T hu (deriv_mem_goA₀ (hWb φ0 hφ0))
    have j1 := hI2 b hb
    have j2 := hI2 φ0 hφ0
    have e1 : ∫ x, u x * (deriv (fun y => goW y * b y) x - m * deriv (fun y => goW y * φ0 y) x) =
        (∫ x, u x * deriv (fun y => goW y * b y) x) -
          m * ∫ x, u x * deriv (fun y => goW y * φ0 y) x := by
      have : ∀ x, u x * (deriv (fun y => goW y * b y) x - m * deriv (fun y => goW y * φ0 y) x) =
          u x * deriv (fun y => goW y * b y) x -
            m * (u x * deriv (fun y => goW y * φ0 y) x) := fun x => by ring
      simp_rw [this]
      rw [integral_sub i1 (i2.const_mul m), integral_const_mul]
    have e2 : ∫ x, H x * (b x - m * φ0 x) = (∫ x, H x * b x) - m * ∫ x, H x * φ0 x := by
      have : ∀ x, H x * (b x - m * φ0 x) = H x * b x - m * (H x * φ0 x) := fun x => by ring
      simp_rw [this]
      rw [integral_sub j1 (j2.const_mul m), integral_const_mul]
    rw [e1, e2] at h1
    rw [hc0]; linarith
  set v : ℝ → ℝ := fun x => (H x - c0) / goW x with hv
  have hvc : ContinuousOn v 𝕀 :=
    (hHc.continuousOn.sub continuousOn_const).div goW_sm.continuous.continuousOn
      (fun x hx => goW_ne hx)
  have step3 : ∀ φ ∈ goA₀, ∫ x, u x * deriv φ x = -∫ x, v x * φ x := by
    intro φ hφ
    set b : ℝ → ℝ := fun x => φ x * (goW x)⁻¹ with hb
    have hbT : b ∈ goA₀ := sm_mul_inv_W hφ
    have hwb : (fun x => goW x * b x) = φ := W_mul_inv hφ
    have h2 := step2 b hbT
    rw [hwb] at h2
    have hbi : Integrable b := hbT.1.continuous.integrable_of_hasCompactSupport (goA₀_cs hbT)
    have e : ∫ x, v x * φ x = (∫ x, H x * b x) - c0 * ∫ x, b x := by
      have : ∀ x, v x * φ x = H x * b x - c0 * b x := by
        intro x
        by_cases hx : x ∈ 𝕀
        · simp only [hv, hb]; field_simp [goW_ne hx]
        · simp [hv, hb, zero_off_go hφ hx]
      simp_rw [this]
      rw [integral_sub (hI2 b hbT) (hbi.const_mul c0), integral_const_mul]
    rw [e]; linarith
  set U0 : ℝ → ℝ := fun x => ∫ y in (0:ℝ)..x, v y with hU0
  have h0I : (0:ℝ) ∈ 𝕀 := ⟨by norm_num, by norm_num⟩
  have hU0d : ∀ x ∈ 𝕀, HasDerivAt U0 (v x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right
      ((hvc.mono (ordConnected_Ioo.uIcc_subset h0I hx)).intervalIntegrable)
      (hvc.stronglyMeasurableAtFilter isOpen_Ioo x hx) (hvc.continuousAt (isOpen_Ioo.mem_nhds hx))
  have hU0c : ContinuousOn U0 𝕀 := fun x hx => (hU0d x hx).continuousAt.continuousWithinAt
  have hgz : ∀ φ ∈ goA₀, ∫ x, (u x - U0 x) * deriv φ x = 0 := by
    intro φ hφ
    have hφd : ∀ x, HasDerivAt φ (deriv φ x) x :=
      fun x => (hφ.1.differentiable (by simp) x).hasDerivAt
    have hder : ∀ x, HasDerivAt (fun x => U0 x * φ x) (v x * φ x + U0 x * deriv φ x) x := by
      intro x
      by_cases hx : x ∈ 𝕀
      · exact (hU0d x hx).mul (hφd x)
      · have hxs : x ∉ tsupport φ := fun h => hx (hφ.2 h)
        have hz : (fun x => U0 x * φ x) =ᶠ[𝓝 x] fun _ => 0 := by
          filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hxs] with y hy
          simp [image_eq_zero_of_notMem_tsupport hy]
        have e : v x * φ x + U0 x * deriv φ x = 0 := by
          simp [zero_off_go hφ hx, zero_off_go (deriv_mem_goA₀ hφ) hx]
        rw [e]; exact (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq hz
    have iv : Integrable (fun x => v x * φ x) :=
      integrable_mul_T (LocInt.of_continuousOn hvc) hφ
    have iU : Integrable (fun x => U0 x * deriv φ x) :=
      integrable_mul_T (LocInt.of_continuousOn hU0c) (deriv_mem_goA₀ hφ)
    have iP : Integrable (fun x => U0 x * φ x) :=
      integrable_mul_T (LocInt.of_continuousOn hU0c) hφ
    have k1 : ∫ x, (v x * φ x + U0 x * deriv φ x) = 0 :=
      integral_eq_zero_of_hasDerivAt_of_integrable hder (iv.add iU) iP
    rw [integral_add iv iU] at k1
    have iu := integrable_mul_T hu (deriv_mem_goA₀ hφ)
    have : ∀ x, (u x - U0 x) * deriv φ x = u x * deriv φ x - U0 x * deriv φ x :=
      fun x => by ring
    simp_rw [this]
    rw [integral_sub iu iU, step3 φ hφ]
    linarith
  obtain ⟨c1, hc1⟩ := du_bois_reymond_loc (g := fun x => u x - U0 x)
    (fun K hK hKc => (hu K hK hKc).sub ((hU0c.mono hK).integrableOn_compact hKc)) hgz
  have hd : ∀ x ∈ 𝕀, HasDerivAt (fun x => U0 x + c1) (v x) x :=
    fun x hx => (hU0d x hx).add_const c1
  refine ⟨fun x => U0 x + c1, -c0, ?_, ?_, ?_⟩
  · have : ContDiffOn ℝ ((0 : WithTop ℕ∞) + 1) (fun x => U0 x + c1) 𝕀 := by
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨fun x hx => (hd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      rw [contDiffOn_zero]
      exact hvc.congr (fun x hx => (hd x hx).deriv)
    simpa using this
  · filter_upwards [hc1] with x hx hxI
    have := hx hxI
    show u x = U0 x + c1
    linarith
  · intro x hx
    rw [(hd x hx).deriv]
    simp only [hv]
    field_simp [goW_ne hx]
    ring

/-- **Local regularity gain**, `dx`-form. -/
theorem reg_loc_gain {u F Ft : ℝ → ℝ} (j : ℕ) (hu : LocInt u) (hF : Integrable F volume)
    (hweak : ∀ a ∈ goA₀, ∫ x, u x * deriv (fun x => goW x * deriv a x) x = ∫ x, F x * a x)
    (hFt : ContDiffOn ℝ (j : WithTop ℕ∞) Ft 𝕀) (hae : ∀ᵐ x, x ∈ 𝕀 → F x = Ft x) :
    ∃ U : ℝ → ℝ, ContDiffOn ℝ ((j : WithTop ℕ∞) + 2) U 𝕀 ∧ ∀ᵐ x, x ∈ 𝕀 → u x = U x := by
  obtain ⟨U, c, hU1, hUae, hw⟩ := reg_loc_C1 hu hF hweak
  set P : ℝ → ℝ := fun x => ∫ y in (0:ℝ)..x, Ft y with hP
  have h0I : (0:ℝ) ∈ 𝕀 := ⟨by norm_num, by norm_num⟩
  have hFtc : ContinuousOn Ft 𝕀 := hFt.continuousOn
  have hPd : ∀ x ∈ 𝕀, HasDerivAt P (Ft x) x := fun x hx =>
    intervalIntegral.integral_hasDerivAt_right
      ((hFtc.mono (ordConnected_Ioo.uIcc_subset h0I hx)).intervalIntegrable)
      (hFtc.stronglyMeasurableAtFilter isOpen_Ioo x hx) (hFtc.continuousAt (isOpen_Ioo.mem_nhds hx))
  have hP1 : ContDiffOn ℝ ((j : WithTop ℕ∞) + 1) P 𝕀 := by
    rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
    refine ⟨fun x hx => (hPd x hx).differentiableAt.differentiableWithinAt, by simp, ?_⟩
    exact hFt.congr (fun x hx => (hPd x hx).deriv)
  have hFeq : ∀ x ∈ 𝕀, ∫ y in (0:ℝ)..x, F y = P x := by
    intro x hx
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with y hy hyI
    exact hy ((ordConnected_Ioo.uIcc_subset h0I hx) (uIoc_subset_uIcc hyI))
  have hdU : ∀ x ∈ 𝕀, deriv U x = (c + P x) / goW x := by
    intro x hx
    have := hw x hx
    rw [hFeq x hx] at this
    field_simp [goW_ne hx]
    linarith
  have hdU2 : ContDiffOn ℝ ((j : WithTop ℕ∞) + 1) (deriv U) 𝕀 := by
    have : ContDiffOn ℝ ((j : WithTop ℕ∞) + 1) (fun x => (c + P x) / goW x) 𝕀 :=
      (contDiffOn_const.add hP1).div (goW_sm.of_le (by exact_mod_cast le_top)).contDiffOn
        (fun x hx => goW_ne hx)
    exact this.congr hdU
  refine ⟨U, ?_, hUae⟩
  have e : (j : WithTop ℕ∞) + 2 = ((j : WithTop ℕ∞) + 1) + 1 := by
    rw [add_assoc]; norm_num
  rw [e, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  exact ⟨(hU1.differentiableOn (by simp)), by simp, hdU2⟩

/-! ### Bridge from `goμ` -/

/-- the `dx`-version `1_{(-1,1)} (1-x²) h` of the right-hand side. -/
noncomputable def goF (h : ℝ → ℝ) : ℝ → ℝ := Set.indicator 𝕀 (fun x => (1 - x ^ 2) * h x)

lemma ae_go_of_vol {P : ℝ → Prop} (h : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ 𝕀 → P x) : ∀ᵐ x ∂goμ, P x :=
  (Measure.absolutelyContinuous_of_le goμ_le).ae_le
    ((ae_restrict_iff' measurableSet_Ioo).2 h)

lemma ae_vol_of_go {P : ℝ → Prop} (h : ∀ᵐ x ∂goμ, P x) : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ 𝕀 → P x := by
  have hac : volume.restrict 𝕀 ≪ goμ :=
    withDensity_absolutelyContinuous' (by fun_prop) (by
      refine (ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall fun x hx => ?_)
      have : 0 < 3 / 4 * (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
      exact (ENNReal.ofReal_pos.2 this).ne')
  exact (ae_restrict_iff' measurableSet_Ioo).1 (hac.ae_le h)

lemma integrableOn_w_mul {u : ℝ → ℝ} (hu : Integrable u goμ) :
    IntegrableOn (fun x => (1 - x ^ 2) * u x) 𝕀 := by
  have h := (integrable_withDensity_iff_integrable_smul'
    (f := fun x => ENNReal.ofReal (3 / 4 * (1 - x ^ 2))) (μ := volume.restrict 𝕀)
    (by fun_prop) (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).1 hu
  have h2 : IntegrableOn (fun x => (4 / 3 : ℝ) * ((ENNReal.ofReal (3 / 4 * (1 - x ^ 2))).toReal • u x)) 𝕀 :=
    h.const_mul _
  refine h2.congr_fun (fun x hx => ?_) measurableSet_Ioo
  have : 0 ≤ 3 / 4 * (1 - x ^ 2) := by nlinarith [hx.1, hx.2]
  simp only [ENNReal.toReal_ofReal this, smul_eq_mul]
  ring

lemma locInt_of_integrable_go {u : ℝ → ℝ} (hu : Integrable u goμ) : LocInt u := by
  intro K hK hKc
  have h1 : IntegrableOn (fun x => (1 - x ^ 2) * u x) K := (integrableOn_w_mul hu).mono_set hK
  have h2 : IntegrableOn (fun x => ((1 - x ^ 2))⁻¹ * ((1 - x ^ 2) * u x)) K :=
    IntegrableOn.continuousOn_mul (fun x hx => by
      have : 0 < 1 - x ^ 2 := by nlinarith [(hK hx).1, (hK hx).2]
      exact ((by fun_prop : Continuous fun x : ℝ => 1 - x ^ 2).continuousAt.inv₀
        this.ne').continuousWithinAt) h1 hKc
  refine h2.congr_fun (fun x hx => ?_) hKc.measurableSet
  have : 0 < 1 - x ^ 2 := by nlinarith [(hK hx).1, (hK hx).2]
  simp only
  rw [← mul_assoc, inv_mul_cancel₀ this.ne', one_mul]

lemma integrable_goF {h : ℝ → ℝ} (hh : Integrable h goμ) : Integrable (goF h) volume :=
  (integrable_indicator_iff measurableSet_Ioo).2 (integrableOn_w_mul hh)

lemma weak_to_vol {u h : ℝ → ℝ}
    (hweak : ∀ a ∈ goA₀, ∫ x, u x * goL a x ∂goμ = ∫ x, h x * a x ∂goμ) :
    ∀ a ∈ goA₀, ∫ x, u x * deriv (fun x => goW x * deriv a x) x = ∫ x, goF h x * a x := by
  intro a ha
  have h1 := hweak a ha
  rw [integral_goμ (h := fun x => u x * goL a x) (fun x hx => by
      simp [goL, zero_off_go (deriv_mem_goA₀ (deriv_mem_goA₀ ha)) hx,
        zero_off_go (deriv_mem_goA₀ ha) hx]),
    integral_goμ (h := fun x => h x * a x) (fun x hx => by simp [zero_off_go ha hx])] at h1
  have e1 : ∫ x, (3 / 4 * (1 - x ^ 2)) * (u x * goL a x) =
      (3 / 4) * ∫ x, u x * deriv (fun x => goW x * deriv a x) x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : deriv (fun x => goW x * deriv a x) x = (1 - x ^ 2) * goL a x := deriv_goP ha.1 x
    simp only [this]; ring
  have e2 : ∫ x, (3 / 4 * (1 - x ^ 2)) * (h x * a x) = (3 / 4) * ∫ x, goF h x * a x := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ 𝕀
    · simp [goF, hx]; ring
    · simp [zero_off_go ha hx]
  rw [e1, e2] at h1
  linarith

/-- **Weak solutions in `L¹(goμ)` of `goL u = h`: first regularity step.** -/
theorem go_reg_C1 {u h : ℝ → ℝ} (hu : Integrable u goμ) (hh : Integrable h goμ)
    (hweak : ∀ a ∈ goA₀, ∫ x, u x * goL a x ∂goμ = ∫ x, h x * a x ∂goμ) :
    ∃ (U : ℝ → ℝ) (c : ℝ), ContDiffOn ℝ 1 U (Ioo (-1 : ℝ) 1) ∧ (∀ᵐ x ∂goμ, u x = U x) ∧
      ∀ x ∈ Ioo (-1 : ℝ) 1, (1 - x ^ 2) ^ 2 * deriv U x = c + ∫ y in (0:ℝ)..x, (1 - y ^ 2) * h y := by
  obtain ⟨U, c, hU, hae, hf⟩ := reg_loc_C1 (locInt_of_integrable_go hu) (integrable_goF hh)
    (weak_to_vol hweak)
  refine ⟨U, c, hU, ae_go_of_vol hae, fun x hx => ?_⟩
  have h0I : (0:ℝ) ∈ 𝕀 := ⟨by norm_num, by norm_num⟩
  have e : ∫ y in (0:ℝ)..x, goF h y = ∫ y in (0:ℝ)..x, (1 - y ^ 2) * h y := by
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    simp [goF, ordConnected_Ioo.uIcc_subset h0I hx hy]
  rw [← e]
  exact hf x hx

/-- **Weak solutions: regularity gain** (`h ∈ C^j` on `(-1,1)` ⇒ `u ∈ C^{j+2}`). -/
theorem go_reg_gain {u h ht : ℝ → ℝ} (j : ℕ) (hu : Integrable u goμ) (hh : Integrable h goμ)
    (hweak : ∀ a ∈ goA₀, ∫ x, u x * goL a x ∂goμ = ∫ x, h x * a x ∂goμ)
    (hht : ContDiffOn ℝ (j : WithTop ℕ∞) ht (Ioo (-1 : ℝ) 1)) (hae : ∀ᵐ x ∂goμ, h x = ht x) :
    ∃ U : ℝ → ℝ, ContDiffOn ℝ ((j : WithTop ℕ∞) + 2) U (Ioo (-1 : ℝ) 1) ∧
      ∀ᵐ x ∂goμ, u x = U x := by
  have hFt : ContDiffOn ℝ (j : WithTop ℕ∞) (fun x => (1 - x ^ 2) * ht x) (Ioo (-1 : ℝ) 1) :=
    (sm_w1.of_le (by exact_mod_cast le_top)).contDiffOn.mul hht
  obtain ⟨U, hU, hUae⟩ := reg_loc_gain j (locInt_of_integrable_go hu) (integrable_goF hh)
    (weak_to_vol hweak) hFt ((ae_vol_of_go hae).mono fun x hx hxI => by
      simp [goF, hxI, hx hxI])
  exact ⟨U, hU, ae_go_of_vol hUae⟩

end MarkovTriple.BGL.Instances.GegenbauerOpen
