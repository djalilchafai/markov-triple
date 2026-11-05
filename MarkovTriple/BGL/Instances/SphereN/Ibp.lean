import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Polar

/-!
# Integration by parts on `S^{n-1}` (Round 28, stream L, group L2)

From the Euclidean integration by parts `LebesgueRd.ibp_L` with a radial cut-off `Φ(|y|²)` supported in the annulus
`1/4 ≤ |y|² ≤ 9/4`, the Euler relation `y·∇F̃ = 0` for the degree-0 extension (so that the radial cut-off
does not contribute) and the polar-coordinate formula `polar`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

/-- radial profile (as a function of `|y|²`), supported in `[1/4, 9/4]`. -/
noncomputable def Φ (s : ℝ) : ℝ :=
  Real.smoothTransition (4 * (s - 1 / 4)) * Real.smoothTransition (4 * (9 / 4 - s))

lemma Φ_smooth : ContDiff ℝ (⊤ : ℕ∞) Φ :=
  (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_id.sub contDiff_const))).mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.mul (contDiff_const.sub contDiff_id)))

lemma Φ_of_le {s : ℝ} (h : s ≤ 1 / 4) : Φ s = 0 := by
  unfold Φ
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), zero_mul]

lemma Φ_of_ge {s : ℝ} (h : 9 / 4 ≤ s) : Φ s = 0 := by
  unfold Φ
  rw [Real.smoothTransition.zero_of_nonpos (x := 4 * (9 / 4 - s)) (by linarith), mul_zero]

lemma Φ_nonneg (s : ℝ) : 0 ≤ Φ s :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

lemma Φ_one_pos : 0 < Φ 1 := by
  unfold Φ
  exact mul_pos (Real.smoothTransition.pos_of_pos (by norm_num))
    (Real.smoothTransition.pos_of_pos (by norm_num))

/-- radial weight `ψ(r) = Φ(r²)/r²`. -/
noncomputable def ψ (r : ℝ) : ℝ := Φ (r ^ 2) * (r ^ 2)⁻¹

lemma ψ_nonneg (r : ℝ) : 0 ≤ ψ r := mul_nonneg (Φ_nonneg _) (inv_nonneg.2 (sq_nonneg r))

lemma ψ_of_le {r : ℝ} (hr : r ^ 2 ≤ 1 / 4) : ψ r = 0 := by
  unfold ψ; rw [Φ_of_le hr, zero_mul]

lemma continuous_ψ : Continuous ψ := by
  rw [continuous_iff_continuousAt]
  intro r
  by_cases hr : r = 0
  · subst hr
    have : ψ =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
      have : ∀ᶠ s in 𝓝 (0 : ℝ), s ^ 2 < 1 / 4 :=
        (continuous_pow 2).continuousAt.eventually (gt_mem_nhds (by norm_num))
      filter_upwards [this] with s hs using ψ_of_le hs.le
    exact continuousAt_const.congr this.symm
  · exact (Φ_smooth.continuous.comp (continuous_pow 2)).continuousAt.mul
      (((continuous_pow 2).continuousAt).inv₀ (pow_ne_zero 2 hr))

/-- radial weight with the Jacobian `r^{n-1}`. -/
noncomputable def Θ (n : ℕ) (r : ℝ) : ℝ := r ^ (n - 1) * ψ r

lemma Θ_continuous (n : ℕ) : Continuous (Θ n) := (continuous_pow _).mul continuous_ψ

lemma Θ_nonneg (n : ℕ) {r : ℝ} (hr : 0 ≤ r) : 0 ≤ Θ n r := mul_nonneg (pow_nonneg hr _) (ψ_nonneg r)

lemma Θ_cs (n : ℕ) : HasCompactSupport (Θ n) := by
  refine HasCompactSupport.intro (K := Icc (-2) 2) isCompact_Icc fun r hr => ?_
  have : 9 / 4 ≤ r ^ 2 := by
    by_contra hcon
    apply hr
    constructor <;> nlinarith
  unfold Θ ψ; rw [Φ_of_ge this]; simp

lemma κ_pos (n : ℕ) : 0 < ∫ y in Ioi (0 : ℝ), Θ n y := by
  have hint : IntegrableOn (Θ n) (Ioi (0 : ℝ)) :=
    ((Θ_continuous n).integrable_of_hasCompactSupport (Θ_cs n)).integrableOn
  rw [setIntegral_pos_iff_support_of_nonneg_ae
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun r hr => Θ_nonneg n (le_of_lt hr))) hint]
  have h1 : Θ n 1 ≠ 0 := by
    unfold Θ ψ
    simp only [one_pow, inv_one, mul_one]
    rw [one_mul]; exact (Φ_one_pos).ne'
  have hopen : IsOpen ({r | Θ n r ≠ 0} ∩ Ioi (0 : ℝ)) :=
    (isOpen_ne_fun (Θ_continuous n) continuous_const).inter isOpen_Ioi
  refine lt_of_lt_of_le ?_ (measure_mono (s := {r | Θ n r ≠ 0} ∩ Ioi (0 : ℝ))
    (fun r hr => ⟨hr.1, hr.2⟩))
  exact hopen.measure_pos volume ⟨1, h1, by norm_num⟩


/-! ### the cut-off test function -/

lemma dd_sq (i : Fin n) (y : Fin n → ℝ) : dd i (LebesgueRd.sq : (Fin n → ℝ) → ℝ) y = 2 * y i := by
  have h : HasFDerivAt (fun z : Fin n → ℝ => ∑ j, z j * z j)
      (∑ j, (y j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ) +
        y j • (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ))) y := by
    refine HasFDerivAt.fun_sum fun j _ => ?_
    exact (hasFDerivAt_apply j y).mul (hasFDerivAt_apply j y)
  have e : (LebesgueRd.sq : (Fin n → ℝ) → ℝ) = fun z => ∑ j, z j * z j := by
    funext z; simp [LebesgueRd.sq, pow_two]
  unfold dd
  rw [e, h.fderiv]
  simp [Pi.single_apply, Finset.sum_add_distrib, two_mul]

/-- the radial factor `ρ(y) = Φ(|y|²)`. -/
noncomputable def rho (y : Fin n → ℝ) : ℝ := Φ (LebesgueRd.sq y)

lemma rho_sm : Sm (rho : (Fin n → ℝ) → ℝ) := Φ_smooth.comp sq_smooth

lemma dd_rho (i : Fin n) (y : Fin n → ℝ) :
    dd i (rho : (Fin n → ℝ) → ℝ) y = deriv Φ (LebesgueRd.sq y) * (2 * y i) := by
  have hs : HasFDerivAt (LebesgueRd.sq : (Fin n → ℝ) → ℝ) (fderiv ℝ LebesgueRd.sq y) y :=
    ((sq_smooth.differentiable (by simp)) y).hasFDerivAt
  have hΦ : HasDerivAt Φ (deriv Φ (LebesgueRd.sq y)) (LebesgueRd.sq y) :=
    ((Φ_smooth.differentiable (by simp)) _).hasDerivAt
  have h := hΦ.comp_hasFDerivAt y hs
  have : dd i (rho : (Fin n → ℝ) → ℝ) y = fderiv ℝ (Φ ∘ LebesgueRd.sq) y (Pi.single i 1) := rfl
  rw [this, h.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [show fderiv ℝ LebesgueRd.sq y (Pi.single i 1) = dd i (LebesgueRd.sq : (Fin n → ℝ) → ℝ) y from rfl, dd_sq]

lemma rho_zero_of_le {y : Fin n → ℝ} (h : LebesgueRd.sq y ≤ 1 / 4) : rho y = 0 := Φ_of_le h

/-- the compactly supported test function `u = ρ · G`. -/
noncomputable def utest (G : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ := fun y => rho y * G y

lemma isOpen_sq_lt (c : ℝ) : IsOpen {y : Fin n → ℝ | LebesgueRd.sq y < c} :=
  isOpen_lt sq_smooth.continuous continuous_const

lemma utest_sm {G : (Fin n → ℝ) → ℝ} (hG : SmO G) : Sm (utest G) := by
  refine Sm_of_SmO_of_zero (SmO.mul (SmO.of_sm rho_sm) hG) ?_
  have h0 : (0 : Fin n → ℝ) ∈ {y : Fin n → ℝ | LebesgueRd.sq y < 1 / 4} := by
    show LebesgueRd.sq (0 : Fin n → ℝ) < 1 / 4
    simp [LebesgueRd.sq]
  filter_upwards [(isOpen_sq_lt (1 / 4)).mem_nhds h0] with y hy
  show rho y * G y = 0
  rw [rho_zero_of_le (le_of_lt hy), zero_mul]

lemma utest_cs (G : (Fin n → ℝ) → ℝ) : HasCompactSupport (utest G) := by
  refine HasCompactSupport.intro (K := Metric.closedBall (0 : Fin n → ℝ) 2)
    (isCompact_closedBall _ _) fun y hy => ?_
  have hy' : 2 < ‖y‖ := by simpa using hy
  obtain ⟨i, hi⟩ : ∃ i, 2 < |y i| := by
    by_contra hcon
    have : ∀ i, |y i| ≤ 2 := fun i => by
      by_contra h; exact hcon ⟨i, lt_of_not_ge h⟩
    exact absurd hy' (not_lt.2 ((pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => by simpa using this i))
  have : 9 / 4 ≤ LebesgueRd.sq y := by
    have h1 : y i ^ 2 ≤ LebesgueRd.sq y :=
      Finset.single_le_sum (f := fun j => y j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : 4 < y i ^ 2 := by
      have := sq_abs (y i); nlinarith [abs_nonneg (y i)]
    linarith
  show rho y * G y = 0
  rw [show rho y = 0 from Φ_of_ge this, zero_mul]

lemma utest_mem {G : (Fin n → ℝ) → ℝ} (hG : SmO G) : utest G ∈ LebesgueRd.A₀ n :=
  LebesgueRd.mem_A₀.2 ⟨utest_sm hG, utest_cs G⟩


/-! ### the two integrands -/

lemma ψ_nrm (y : Fin n → ℝ) : ψ (nrm y) = Φ (LebesgueRd.sq y) * (LebesgueRd.sq y)⁻¹ := by
  unfold ψ; rw [nrm_sq]

lemma ne_zero_of_sq_gt {y : Fin n → ℝ} (h : 1 / 4 ≤ LebesgueRd.sq y) : y ≠ 0 := by
  intro h0
  subst h0
  have : LebesgueRd.sq (0 : Fin n → ℝ) = 0 := by simp [LebesgueRd.sq]
  linarith

lemma far_of_sq {y : Fin n → ℝ} (h : 1 / 4 ≤ LebesgueRd.sq y) : 3 / 10 < nrm y := by
  have h2 := nrm_sq y
  have h3 := nrm_nonneg y
  by_contra hcon
  push Not at hcon
  nlinarith

lemma integrand_L {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (y : Fin n → ℝ) :
    utest (ext g) y * Lf (hat (ext f)) y = ψ (nrm y) * ext (g * LS f) y := by
  by_cases h : LebesgueRd.sq y ≤ 1 / 4
  · show rho y * ext g y * _ = _
    rw [rho_zero_of_le h, ψ_nrm, Φ_of_le h]; simp
  · have h' : 1 / 4 ≤ LebesgueRd.sq y := (not_le.1 h).le
    have hy := ne_zero_of_sq_gt h'
    have hL : Lf (hat (ext f)) y = Lf (ext f) y :=
      Finset.sum_congr rfl fun i _ => dd_dd_congr (hat_eventuallyEq (far_of_sq h')) i i
    have hs : LebesgueRd.sq y ≠ 0 := by intro h0; rw [h0] at h'; linarith
    rw [hL, ext_mul, Pi.mul_apply, ext_LS hf hy, ψ_nrm]
    show rho y * ext g y * _ = _
    unfold rho
    field_simp

lemma integrand_Γ {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) (y : Fin n → ℝ) :
    Gf (hat (ext f)) (utest (ext g)) y = ψ (nrm y) * ext (ΓS f g) y := by
  by_cases h : LebesgueRd.sq y < 1 / 4
  · have hu : utest (ext g) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [(isOpen_sq_lt (1 / 4)).mem_nhds h] with z hz
      show rho z * _ = 0
      rw [rho_zero_of_le hz.le, zero_mul]
    have h0 : ∀ i, dd i (utest (ext g)) y = 0 := fun i => by
      rw [dd_congr hu i]; simp [dd]
    simp only [Gf, h0, mul_zero, Finset.sum_const_zero]
    rw [ψ_nrm, Φ_of_le h.le]; simp
  · have h' : 1 / 4 ≤ LebesgueRd.sq y := not_lt.1 h
    have hy := ne_zero_of_sq_gt h'
    have hs : LebesgueRd.sq y ≠ 0 := by intro h0; rw [h0] at h'; linarith
    have hd : ∀ i, dd i (hat (ext f)) y = dd i (ext f) y := fun i =>
      dd_congr (hat_eventuallyEq (far_of_sq h')) i
    have hdu : ∀ i, dd i (utest (ext g)) y
        = deriv Φ (LebesgueRd.sq y) * (2 * y i) * ext g y + rho y * dd i (ext g) y := fun i => by
      have := dd_mul_at (SmO.of_sm (rho_sm (n := n))) hg hy i
      rw [dd_rho] at this
      exact this
    have hE := euler hf (hom_ext f) hy
    simp only [Int.cast_zero, zero_mul] at hE
    rw [ext_ΓS hf hg hy, ψ_nrm]
    calc Gf (hat (ext f)) (utest (ext g)) y
        = ∑ i, dd i (ext f) y *
            (deriv Φ (LebesgueRd.sq y) * (2 * y i) * ext g y + rho y * dd i (ext g) y) := by
          simp only [Gf, hd, hdu]
      _ = deriv Φ (LebesgueRd.sq y) * 2 * ext g y * (∑ i, y i * dd i (ext f) y)
            + rho y * Gf (ext f) (ext g) y := by
          simp only [Gf, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = _ := by
          rw [hE]; unfold rho; field_simp; ring

/-- the unnormalised integration by parts. -/
theorem ibp_σ0 (hn : 1 ≤ n) {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) :
    ∫ x, g x * LS f x ∂σ0 n = -∫ x, ΓS f g x ∂σ0 n := by
  have key := LebesgueRd.ibp_L (Sm_hat hf) (utest_mem hg)
  have k1 : ∫ y, ψ (nrm y) * ext (g * LS f) y = ∫ y, utest (ext g) y * Lf (hat (ext f)) y :=
    integral_congr_ae (Eventually.of_forall fun y => (integrand_L hf y).symm)
  have k2 : ∫ y, ψ (nrm y) * ext (ΓS f g) y = ∫ y, Gf (hat (ext f)) (utest (ext g)) y :=
    integral_congr_ae (Eventually.of_forall fun y => (integrand_Γ hf hg y).symm)
  have e1 := polar hn ψ (g * LS f)
  have e2 := polar hn ψ (ΓS f g)
  have hκ : (∫ y in Ioi (0 : ℝ), y ^ (n - 1) * ψ y) ≠ 0 := (κ_pos n).ne'
  have key' : ∫ y, utest (ext g) y * Lf (hat (ext f)) y = -∫ y, Gf (hat (ext f)) (utest (ext g)) y := key
  rw [← k1, ← k2, e1, e2] at key'
  have : ((∫ x, g x * LS f x ∂σ0 n) + ∫ x, ΓS f g x ∂σ0 n) * ∫ y in Ioi (0 : ℝ), y ^ (n - 1) * ψ y = 0 := by
    simp only [Pi.mul_apply] at key'
    linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · exact absurd h hκ

/-- the normalised integration by parts. -/
theorem ibp_sphere (hn : 1 ≤ n) {f g : Sph n → ℝ} (hf : f ∈ A₀S n) (hg : g ∈ A₀S n) :
    ∫ x, g x * LS f x ∂σ n = -∫ x, ΓS f g x ∂σ n := by
  unfold σ
  rw [integral_smul_measure, integral_smul_measure, ibp_σ0 hn hf hg, smul_neg]

end MarkovTriple.BGL.SphereN
