import Mathlib
import MarkovTriple.BGL.Analysis.OU.Basic

/-!
# Elementary one-dimensional distribution theory (R15, regularity of the Gibbs triple)

Measure-free (Lebesgue) lemmas used by `RegCore.lean`:

* `exists_antideriv`: a smooth compactly supported `b` with `∫ b = 0` is the derivative of a smooth compactly
  supported `a`;
* `du_bois_reymond`: a locally integrable `g` with `∫ g φ' = 0` for all `φ ∈ C_c^∞(ℝ)` is a.e. constant
  (du Bois-Reymond lemma; uses Mathlib's fundamental lemma of the calculus of variations
  `ae_eq_zero_of_integral_contDiff_smul_eq_zero`);
* `integral_mul_eq_neg_integral_primitive`: integration by parts `∫ f a = -∫ F a'` for `f ∈ L¹(ℝ)`,
  `F = ∫₀ˣ f` (absolutely continuous), `a ∈ C_c^∞` (Mathlib's AC integration by parts + Lebesgue
  differentiation);
* `integral_deriv_mul_cs`: `∫ (U' φ + U φ') = 0` for `C¹` `U`, `φ` with `φ` compactly supported.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.Gibbs

/-- a compactly supported function vanishes outside some `Icc (-R) R` with a margin. -/
lemma exists_support_Icc {b : ℝ → ℝ} (hc : HasCompactSupport b) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, R ≤ |x| → b x = 0 := by
  obtain ⟨R0, hR0⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R0| + 1, by positivity, fun x hx => ?_⟩
  by_contra hne
  have hx' : x ∈ tsupport b := subset_tsupport _ (Function.mem_support.2 hne)
  have := hR0 hx'
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  linarith [le_abs_self R0]

/-- `b ∈ C_c^∞`, `∫ b = 0` ⇒ `b = a'` with `a ∈ C_c^∞`. -/
lemma exists_antideriv {b : ℝ → ℝ} (hb : Sm b) (hc : HasCompactSupport b) (h0 : ∫ x, b x = 0) :
    ∃ a : ℝ → ℝ, Sm a ∧ HasCompactSupport a ∧ ∀ x, HasDerivAt a (b x) x := by
  obtain ⟨R, hR, hRb⟩ := exists_support_Icc hc
  set a : ℝ → ℝ := fun x => ∫ y in (-R)..x, b y with ha
  have hder : ∀ x, HasDerivAt a (b x) x := fun x =>
    (hb.continuous.integral_hasStrictDerivAt (-R) x).hasDerivAt
  have hderiv : deriv a = b := funext fun x => (hder x).deriv
  have hSm : Sm a := by
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
  exact HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) hzero

/-- the product rule integrated: `∫ (U' φ + U φ') = 0` for `C¹` `U` and `φ` of compact support. -/
lemma integral_deriv_mul_cs {U φ U' φ' : ℝ → ℝ} (hU : ∀ x, HasDerivAt U (U' x) x)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hU' : Continuous U') (hφ' : Continuous φ')
    (hc : HasCompactSupport φ) :
    ∫ x, (U' x * φ x + U x * φ' x) = 0 := by
  have hUc : Continuous U := continuous_iff_continuousAt.2 fun x => (hU x).continuousAt
  have hφc : Continuous φ := continuous_iff_continuousAt.2 fun x => (hφ x).continuousAt
  have hder : ∀ x, HasDerivAt (fun x => U x * φ x) (U' x * φ x + U x * φ' x) x :=
    fun x => (hU x).mul (hφ x)
  have hcs : HasCompactSupport (fun x => U x * φ x) := hc.mul_left
  have hφ'cs : HasCompactSupport φ' := by
    have : φ' = deriv φ := funext fun x => (hφ x).deriv.symm
    rw [this]; exact hc.deriv
  refine integral_eq_zero_of_hasDerivAt_of_integrable hder ?_ ?_
  · refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hU'.mul hφc).add (hUc.mul hφ')
    · exact (hc.mul_left (f := U')).add (hφ'cs.mul_left (f := U))
  · exact (hUc.mul hφc).integrable_of_hasCompactSupport hcs

/-- `HasCompactSupport` of the derivative of a smooth compactly supported function, as `Sm`. -/
lemma Sm.mul_cs {f g : ℝ → ℝ} (hf : Sm f) (hg : Sm g) : Sm (fun x => f x * g x) := hf.mul hg

/-- **du Bois-Reymond lemma**: `g ∈ L¹_loc(ℝ)` with `∫ g φ' = 0` for every `φ ∈ C_c^∞` is a.e. constant. -/
theorem du_bois_reymond {g : ℝ → ℝ} (hg : LocallyIntegrable g volume)
    (h : ∀ φ : ℝ → ℝ, Sm φ → HasCompactSupport φ → ∫ x, g x * deriv φ x = 0) :
    ∃ c : ℝ, g =ᵐ[volume] fun _ => c := by
  obtain ⟨φ0, hφ0s, hφ0c, hφ0i⟩ : ∃ φ0 : ℝ → ℝ, Sm φ0 ∧ HasCompactSupport φ0 ∧ ∫ x, φ0 x = 1 := by
    let b : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
    have hpos : 0 < ∫ x, b x := b.integral_pos
    refine ⟨fun x => (∫ x, b x)⁻¹ * b x, contDiff_const.mul b.contDiff, b.hasCompactSupport.mul_left,
      ?_⟩
    rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']
  have hint : ∀ ψ : ℝ → ℝ, Sm ψ → HasCompactSupport ψ → Integrable (fun x => g x * ψ x) volume := by
    intro ψ hψ hc
    exact (hg.integrable_smul_right_of_hasCompactSupport hψ.continuous hc)
  set c : ℝ := ∫ x, g x * φ0 x with hcdef
  refine ⟨c, ?_⟩
  have hzero : ∀ ψ : ℝ → ℝ, Sm ψ → HasCompactSupport ψ → ∫ x, ψ x • (g x - c) = 0 := by
    intro ψ hψ hc
    set m : ℝ := ∫ x, ψ x with hm
    -- `ψ - m φ0` has integral zero, hence is a derivative
    have hb : Sm (fun x => ψ x - m * φ0 x) := hψ.sub (contDiff_const.mul hφ0s)
    have hbc : HasCompactSupport (fun x => ψ x - m * φ0 x) := hc.sub (hφ0c.mul_left)
    have hψi : Integrable ψ volume := hψ.continuous.integrable_of_hasCompactSupport hc
    have hφi : Integrable φ0 volume := hφ0s.continuous.integrable_of_hasCompactSupport hφ0c
    have hb0 : ∫ x, (ψ x - m * φ0 x) = 0 := by
      rw [integral_sub hψi (hφi.const_mul m), integral_const_mul, hφ0i]; simp [hm]
    obtain ⟨a, haS, hac, had⟩ := exists_antideriv hb hbc hb0
    have hda : deriv a = fun x => ψ x - m * φ0 x := funext fun x => (had x).deriv
    have h1 := h a haS hac
    rw [hda] at h1
    have i1 := hint ψ hψ hc
    have i2 := hint φ0 hφ0s hφ0c
    have e1 : ∫ x, g x * (ψ x - m * φ0 x) = (∫ x, g x * ψ x) - m * c := by
      have : ∀ x, g x * (ψ x - m * φ0 x) = g x * ψ x - m * (g x * φ0 x) := fun x => by ring
      simp_rw [this]
      rw [integral_sub i1 (i2.const_mul m), integral_const_mul]
    rw [e1] at h1
    have e2 : ∫ x, ψ x • (g x - c) = (∫ x, g x * ψ x) - c * m := by
      have : ∀ x, ψ x • (g x - c) = g x * ψ x - c * ψ x := fun x => by simp only [smul_eq_mul]; ring
      simp_rw [this]
      rw [integral_sub i1 (hψi.const_mul c), integral_const_mul]
    rw [e2]; linarith
  have hloc : LocallyIntegrable (fun x => g x - c) volume :=
    hg.sub (locallyIntegrable_const c)
  have := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc (fun ψ hψ hc => hzero ψ hψ hc)
  filter_upwards [this] with x hx
  linarith

/-- **Integration by parts against a primitive** (absolutely continuous): for `f ∈ L¹(ℝ)`,
`F x = ∫₀ˣ f` and `a ∈ C_c^∞`: `∫ f a = -∫ F a'`. -/
theorem integral_mul_eq_neg_integral_primitive {f : ℝ → ℝ} (hf : Integrable f volume) {a : ℝ → ℝ}
    (ha : Sm a) (hc : HasCompactSupport a) :
    ∫ x, f x * a x = -∫ x, (∫ y in (0:ℝ)..x, f y) * deriv a x := by
  obtain ⟨R1, hR1, h1⟩ := exists_support_Icc hc
  obtain ⟨R2, hR2, h2⟩ := exists_support_Icc hc.deriv
  set R : ℝ := max R1 R2 with hR
  have hRpos : 0 < R := lt_max_of_lt_left hR1
  have ha0 : ∀ x, R ≤ |x| → a x = 0 := fun x hx => h1 x (le_trans (le_max_left _ _) hx)
  have hda0 : ∀ x, R ≤ |x| → deriv a x = 0 := fun x hx => h2 x (le_trans (le_max_right _ _) hx)
  set F : ℝ → ℝ := fun x => ∫ y in (0:ℝ)..x, f y with hF
  have hFi : ∀ s t : ℝ, IntervalIntegrable f volume s t := fun s t => hf.intervalIntegrable
  have hFac : AbsolutelyContinuousOnInterval F (-R) R :=
    (hFi (-R) R).absolutelyContinuousOnInterval_intervalIntegral (by
      rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩)
  have haac : AbsolutelyContinuousOnInterval a (-R) R :=
    (ha.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 a).contDiffOn.absolutelyContinuousOnInterval
  have hibp := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hFac haac
  have haR : a R = 0 := ha0 R (by rw [abs_of_pos hRpos])
  have haR' : a (-R) = 0 := ha0 (-R) (by rw [abs_neg, abs_of_pos hRpos])
  rw [haR, haR'] at hibp
  have hFd : ∀ᵐ x ∂volume, deriv F x = f x := by
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf.locallyIntegrable] with x hx
    exact (hx 0).deriv
  have e1 : ∫ x, f x * a x = ∫ x in (-R)..R, f x * a x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hy
    rcases hy with hy | hy
    · rw [ha0 y (by rw [abs_of_nonpos (by linarith)]; linarith)]; simp
    · rw [ha0 y (by rw [abs_of_nonneg (by linarith)]; linarith)]; simp
  have e2 : ∫ x, F x * deriv a x = ∫ x in (-R)..R, F x * deriv a x := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => ?_)).symm
    rw [mem_Ioc, not_and_or, not_lt, not_le] at hy
    rcases hy with hy | hy
    · rw [hda0 y (by rw [abs_of_nonpos (by linarith)]; linarith)]; simp
    · rw [hda0 y (by rw [abs_of_nonneg (by linarith)]; linarith)]; simp
  have e3 : ∫ x in (-R)..R, deriv F x * a x = ∫ x in (-R)..R, f x * a x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hFd] with x hx _
    rw [hx]
  rw [e1, e2, hibp, e3]
  ring

end MarkovTriple.BGL.Instances.Gibbs
