import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.FunctAlgebra
import MarkovTriple.BGL.Instances.Gibbs.RegAnalysis

/-!
# One-dimensional elliptic regularity for the Gibbs operator `L f = f'' - V' f'` (R15)

This is the classical theorem (BGL Sect. 1.12, pp. 49-50, quoted without proof) that weak solutions of
`L u = h` are as regular as `h` allows, in dimension one.  With `w = e^{-V}/Z` one has
`w L a = (w a')'` for smooth `a`, so the weak equation `∫ u L a dμ = ∫ h a dμ` (`a ∈ C_c^∞`) reads
`∫ u (w a')' dx = ∫ h w a dx`.

* `reg_core` (R0): if `w u`, `w h ∈ L¹(ℝ)` solve the weak equation then `u` agrees a.e. with a `C¹` function
  `U` and `w U' = c + ∫₀ˣ w h` (du Bois-Reymond lemma after one integration by parts for the absolutely
  continuous primitive `∫₀ˣ w h`).
* `reg_core_smooth` (R1): if moreover `h` agrees a.e. with a `C^j` function then `U` is `C^{j+2}`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm Lo Go)
open MarkovTriple.Sanity.OU hiding A₀ γ φ

namespace MarkovTriple.BGL.Instances.Gibbs

/-- a smooth compactly supported bump of integral one. -/
lemma exists_bump_integral_one :
    ∃ φ0 : ℝ → ℝ, Sm φ0 ∧ HasCompactSupport φ0 ∧ ∫ x, φ0 x = 1 := by
  let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hpos : 0 < ∫ x, b x := b.integral_pos
  refine ⟨fun x => (∫ x, b x)⁻¹ * b x, contDiff_const.mul b.contDiff, b.hasCompactSupport.mul_left, ?_⟩
  rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']

namespace GibbsData
variable (G : GibbsData)

/-- `w L a = (w a')'` for smooth `a`. -/
lemma w_mul_Lg {a : ℝ → ℝ} (ha : Sm a) (x : ℝ) :
    G.w x * Lg G.V a x = deriv (fun x => G.w x * deriv a x) x := by
  have h : HasDerivAt (fun x => G.w x * deriv a x) _ x :=
    (G.hasDerivAt_w x).mul (ha.deriv'.hasDerivAt x)
  rw [h.deriv]
  unfold Lg
  ring

lemma w_ne_zero (x : ℝ) : G.w x ≠ 0 := (G.w_pos x).ne'

lemma locInt_of_mul_w {u : ℝ → ℝ} (hu : Integrable (fun x => G.w x * u x) volume) :
    LocallyIntegrable u volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have h1 : IntegrableOn (fun x => (G.w x)⁻¹ * (G.w x * u x)) K volume :=
    IntegrableOn.continuousOn_mul
      (fun x _ => ((G.w_smooth.continuous.continuousAt).inv₀ (G.w_ne_zero x)).continuousWithinAt)
      hu.integrableOn hK
  refine h1.congr_fun (fun x _ => ?_) hK.measurableSet
  simp only
  rw [← mul_assoc, inv_mul_cancel₀ (G.w_ne_zero x), one_mul]

/-- `u ψ` is integrable for `ψ` continuous with compact support (when `w u ∈ L¹`). -/
lemma integrable_mul_cs {u : ℝ → ℝ} (hu : Integrable (fun x => G.w x * u x) volume) {ψ : ℝ → ℝ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) : Integrable (fun x => u x * ψ x) volume := by
  have := (G.locInt_of_mul_w hu).integrable_smul_right_of_hasCompactSupport hψ hc
  simpa using this

/-- **R0.  Elliptic regularity, first step (weak solution is `C¹`).**  Let `w = e^{-V}/Z`; if `w u, w h ∈ L¹(ℝ)`
and `∫ w u L a = ∫ w h a` for all `a ∈ C_c^∞` (the weak form of `L u = h` in `L²(μ)`), then `u` agrees a.e. with a
`C¹` function `U` and `w U' = c + ∫₀ˣ w h` for a constant `c`.  Classical 1-D elliptic regularity (BGL Sect. 1.12). -/
theorem reg_core {u h : ℝ → ℝ} (hu : Integrable (fun x => G.w x * u x) volume)
    (hh : Integrable (fun x => G.w x * h x) volume)
    (hweak : ∀ a : ℝ → ℝ, Sm a → HasCompactSupport a →
      ∫ x, G.w x * (u x * Lg G.V a x) = ∫ x, G.w x * (h x * a x)) :
    ∃ (U : ℝ → ℝ) (c : ℝ), ContDiff ℝ 1 U ∧ u =ᵐ[volume] U ∧
      ∀ x, G.w x * deriv U x = c + ∫ y in (0:ℝ)..x, G.w y * h y := by
  set f : ℝ → ℝ := fun x => G.w x * h x with hf
  set H : ℝ → ℝ := fun x => ∫ y in (0:ℝ)..x, f y with hH
  have hHc : Continuous H :=
    intervalIntegral.continuous_primitive (fun a b => hh.intervalIntegrable) 0
  -- integrability helpers
  have hD : ∀ b : ℝ → ℝ, Sm b → HasCompactSupport b →
      Continuous (deriv (fun x => G.w x * b x)) ∧ HasCompactSupport (deriv (fun x => G.w x * b x)) :=
    fun b hb hbc => ⟨(Sm.deriv' (G.w_smooth.mul hb)).continuous, (hbc.mul_left (f := G.w)).deriv⟩
  have hI1 : ∀ b : ℝ → ℝ, Sm b → HasCompactSupport b →
      Integrable (fun x => u x * deriv (fun x => G.w x * b x) x) volume :=
    fun b hb hbc => G.integrable_mul_cs hu (hD b hb hbc).1 (hD b hb hbc).2
  have hI2 : ∀ b : ℝ → ℝ, Sm b → HasCompactSupport b → Integrable (fun x => H x * b x) volume :=
    fun b hb hbc => (hHc.mul hb.continuous).integrable_of_hasCompactSupport hbc.mul_left
  -- Step 1: test functions with zero mean
  have step1 : ∀ b : ℝ → ℝ, Sm b → HasCompactSupport b → ∫ x, b x = 0 →
      ∫ x, u x * deriv (fun x => G.w x * b x) x = -∫ x, H x * b x := by
    intro b hb hbc hb0
    obtain ⟨a, haS, hac, had⟩ := exists_antideriv hb hbc hb0
    have hda : deriv a = b := funext fun x => (had x).deriv
    have h1 := hweak a haS hac
    have e1 : ∫ x, G.w x * (u x * Lg G.V a x) = ∫ x, u x * deriv (fun x => G.w x * b x) x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have := G.w_mul_Lg haS x
      rw [hda] at this
      show G.w x * (u x * Lg G.V a x) = u x * deriv (fun x => G.w x * b x) x
      rw [← this]; ring
    have e2 : ∫ x, G.w x * (h x * a x) = ∫ x, f x * a x :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only [hf]; ring)
    rw [e1, e2, integral_mul_eq_neg_integral_primitive hh haS hac, hda] at h1
    exact h1
  -- Step 2: arbitrary test functions, up to a constant
  obtain ⟨φ0, hφ0s, hφ0c, hφ0i⟩ := exists_bump_integral_one
  set c0 : ℝ := (∫ x, u x * deriv (fun x => G.w x * φ0 x) x) + ∫ x, H x * φ0 x with hc0
  have step2 : ∀ b : ℝ → ℝ, Sm b → HasCompactSupport b →
      (∫ x, u x * deriv (fun x => G.w x * b x) x) + ∫ x, H x * b x = (∫ x, b x) * c0 := by
    intro b hb hbc
    set m : ℝ := ∫ x, b x with hm
    have hbi : Integrable b volume := hb.continuous.integrable_of_hasCompactSupport hbc
    have hφi : Integrable φ0 volume := hφ0s.continuous.integrable_of_hasCompactSupport hφ0c
    have hb' : Sm (fun x => b x - m * φ0 x) := hb.sub (contDiff_const.mul hφ0s)
    have hbc' : HasCompactSupport (fun x => b x - m * φ0 x) := hbc.sub hφ0c.mul_left
    have hb0 : ∫ x, (b x - m * φ0 x) = 0 := by
      rw [integral_sub hbi (hφi.const_mul m), integral_const_mul, hφ0i]; simp [hm]
    have h1 := step1 _ hb' hbc' hb0
    have hd : ∀ x, deriv (fun y => G.w y * (b y - m * φ0 y)) x =
        deriv (fun y => G.w y * b y) x - m * deriv (fun y => G.w y * φ0 y) x := by
      intro x
      have e : (fun y => G.w y * (b y - m * φ0 y)) =
          fun y => G.w y * b y - m * (G.w y * φ0 y) := by funext y; ring
      rw [e]
      have h1 := Sm.hasDerivAt (G.w_smooth.mul hb) x
      have h2 := Sm.hasDerivAt (G.w_smooth.mul hφ0s) x
      exact (h1.sub (h2.const_mul m)).deriv
    simp_rw [hd] at h1
    have i1 := hI1 b hb hbc
    have i2 := hI1 φ0 hφ0s hφ0c
    have j1 := hI2 b hb hbc
    have j2 := hI2 φ0 hφ0s hφ0c
    have e1 : ∫ x, u x * (deriv (fun y => G.w y * b y) x - m * deriv (fun y => G.w y * φ0 y) x) =
        (∫ x, u x * deriv (fun y => G.w y * b y) x) -
          m * ∫ x, u x * deriv (fun y => G.w y * φ0 y) x := by
      have : ∀ x, u x * (deriv (fun y => G.w y * b y) x - m * deriv (fun y => G.w y * φ0 y) x) =
          u x * deriv (fun y => G.w y * b y) x -
            m * (u x * deriv (fun y => G.w y * φ0 y) x) := fun x => by ring
      simp_rw [this]
      rw [integral_sub i1 (i2.const_mul m), integral_const_mul]
    have e2 : ∫ x, H x * (b x - m * φ0 x) = (∫ x, H x * b x) - m * ∫ x, H x * φ0 x := by
      have : ∀ x, H x * (b x - m * φ0 x) = H x * b x - m * (H x * φ0 x) := fun x => by ring
      simp_rw [this]
      rw [integral_sub j1 (j2.const_mul m), integral_const_mul]
    rw [e1, e2] at h1
    rw [hc0]; linarith
  -- Step 3: the distributional derivative of `u` is the continuous function `v`
  set v : ℝ → ℝ := fun x => (H x - c0) / G.w x with hv
  have hvc : Continuous v :=
    (hHc.sub continuous_const).div G.w_smooth.continuous G.w_ne_zero
  have step3 : ∀ φ : ℝ → ℝ, Sm φ → HasCompactSupport φ →
      ∫ x, u x * deriv φ x = -∫ x, v x * φ x := by
    intro φ hφ hφc
    set b : ℝ → ℝ := fun x => φ x * (G.w x)⁻¹ with hb
    have hbS : Sm b := hφ.mul (G.w_smooth.inv G.w_ne_zero)
    have hbc : HasCompactSupport b := hφc.mul_right
    have hwb : (fun x => G.w x * b x) = φ := by
      funext x; simp only [hb]; field_simp [G.w_ne_zero x]
    have h2 := step2 b hbS hbc
    rw [hwb] at h2
    have hbi : Integrable b volume := hbS.continuous.integrable_of_hasCompactSupport hbc
    have e : ∫ x, v x * φ x = (∫ x, H x * b x) - c0 * ∫ x, b x := by
      have : ∀ x, v x * φ x = H x * b x - c0 * b x := fun x => by
        simp only [hv, hb]; field_simp [G.w_ne_zero x]
      simp_rw [this]
      rw [integral_sub (hI2 b hbS hbc) (hbi.const_mul c0), integral_const_mul]
    rw [e]; linarith
  -- Step 4: the primitive `U0` of `v` and du Bois-Reymond
  set U0 : ℝ → ℝ := fun x => ∫ y in (0:ℝ)..x, v y with hU0
  have hU0d : ∀ x, HasDerivAt U0 (v x) x := fun x =>
    (hvc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hU0c : Continuous U0 := continuous_iff_continuousAt.2 fun x => (hU0d x).continuousAt
  have hg : LocallyIntegrable (fun x => u x - U0 x) volume :=
    (G.locInt_of_mul_w hu).sub hU0c.locallyIntegrable
  have hgz : ∀ φ : ℝ → ℝ, Sm φ → HasCompactSupport φ → ∫ x, (u x - U0 x) * deriv φ x = 0 := by
    intro φ hφ hφc
    have hφd : ∀ x, HasDerivAt φ (deriv φ x) x := hφ.hasDerivAt
    have hdc : Continuous (deriv φ) := hφ.deriv'.continuous
    have hdcs : HasCompactSupport (deriv φ) := hφc.deriv
    have k1 := integral_deriv_mul_cs hU0d hφd hvc hdc hφc
    have iv : Integrable (fun x => v x * φ x) volume :=
      (hvc.mul hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left
    have iU : Integrable (fun x => U0 x * deriv φ x) volume :=
      (hU0c.mul hdc).integrable_of_hasCompactSupport hdcs.mul_left
    rw [integral_add iv iU] at k1
    have iu := G.integrable_mul_cs hu hdc hdcs
    have : ∀ x, (u x - U0 x) * deriv φ x = u x * deriv φ x - U0 x * deriv φ x := fun x => by ring
    simp_rw [this]
    rw [integral_sub iu iU, step3 φ hφ hφc]
    linarith
  obtain ⟨c1, hc1⟩ := du_bois_reymond hg (fun φ hφ hφc => hgz φ hφ hφc)
  refine ⟨fun x => U0 x + c1, -c0, ?_, ?_, ?_⟩
  · have hd : ∀ x, HasDerivAt (fun x => U0 x + c1) (v x) x := fun x => (hU0d x).add_const c1
    refine contDiff_one_iff_deriv.2 ⟨fun x => (hd x).differentiableAt, ?_⟩
    have : deriv (fun x => U0 x + c1) = v := funext fun x => (hd x).deriv
    rw [this]; exact hvc
  · filter_upwards [hc1] with x hx
    have hx' : u x - U0 x = c1 := hx
    show u x = U0 x + c1
    linarith
  · intro x
    have hd : HasDerivAt (fun x => U0 x + c1) (v x) x := (hU0d x).add_const c1
    rw [hd.deriv]
    simp only [hv]
    field_simp [G.w_ne_zero x]
    ring

/-- **R1.  Elliptic regularity, bootstrap.**  Under the hypotheses of `reg_core`, if `h` agrees a.e. with a `C^j`
function, then `u` agrees a.e. with a `C^{j+2}` function. -/
theorem reg_core_smooth {u h ht : ℝ → ℝ} (j : ℕ) (hu : Integrable (fun x => G.w x * u x) volume)
    (hh : Integrable (fun x => G.w x * h x) volume)
    (hweak : ∀ a : ℝ → ℝ, Sm a → HasCompactSupport a →
      ∫ x, G.w x * (u x * Lg G.V a x) = ∫ x, G.w x * (h x * a x))
    (hht : ContDiff ℝ (j : WithTop ℕ∞) ht) (hae : h =ᵐ[volume] ht) :
    ∃ U : ℝ → ℝ, ContDiff ℝ ((j : WithTop ℕ∞) + 2) U ∧ u =ᵐ[volume] U := by
  obtain ⟨U, c, hU1, hUae, hw⟩ := G.reg_core hu hh hweak
  set F : ℝ → ℝ := fun x => ∫ y in (0:ℝ)..x, G.w y * ht y with hF
  have hcont : Continuous (fun y => G.w y * ht y) := G.w_smooth.continuous.mul hht.continuous
  have hFd : ∀ x, HasDerivAt F (G.w x * ht x) x := fun x =>
    (hcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hFderiv : deriv F = fun x => G.w x * ht x := funext fun x => (hFd x).deriv
  have hF1 : ContDiff ℝ ((j : WithTop ℕ∞) + 1) F := by
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (hFd x).differentiableAt, by simp, ?_⟩
    rw [hFderiv]
    exact (G.w_smooth.of_le (by exact_mod_cast le_top)).mul hht
  have hFeq : ∀ x, ∫ y in (0:ℝ)..x, G.w y * h y = F x := by
    intro x
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with y hy _
    rw [hy]
  have hdU : deriv U = fun x => (c + F x) / G.w x := by
    funext x
    have := hw x
    rw [hFeq] at this
    field_simp [G.w_ne_zero x]
    linarith
  have hdU2 : ContDiff ℝ ((j : WithTop ℕ∞) + 1) (deriv U) := by
    rw [hdU]
    exact (contDiff_const.add hF1).div (G.w_smooth.of_le (by exact_mod_cast le_top)) G.w_ne_zero
  refine ⟨U, ?_, hUae⟩
  have : (j : WithTop ℕ∞) + 2 = ((j : WithTop ℕ∞) + 1) + 1 := by
    rw [add_assoc]; norm_num
  rw [this, contDiff_succ_iff_deriv]
  exact ⟨(hU1.differentiable (by simp)), by simp, hdU2⟩

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
