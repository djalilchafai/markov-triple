import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Full.Sup

/-!
# Smoothness of series of harmonic homogeneous polynomials (Round 32, stream Y, step 2)

A series `Σ_k h_k(y)` with `h_k` harmonic homogeneous of degree `k` and `Σ_k c^k ‖h_k‖_{L²(σ)} < ∞` for every `c ≥ 0` defines
a `C^∞` function on `ℝ^n`: by `harm_sup` the terms are bounded on balls, and the partial derivatives `∂_i h_{k+1}` form a
series of the same class (`harm_grad_L2`), so the claim follows by induction on the order of differentiation.
-/

open MeasureTheory MvPolynomial

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

/-- the coordinate functionals as continuous linear maps. -/
noncomputable abbrev coordL (i : Fin n) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i

lemma hasFDerivAt_ev (p : Pn n) (y : Fin n → ℝ) :
    HasFDerivAt (ev p) (∑ i, (ev (MvPolynomial.pderiv i p) y) • coordL i) y := by
  have hd : DifferentiableAt ℝ (ev p) y := ((Sm_ev p).differentiable (by simp)).differentiableAt
  have h1 := hd.hasFDerivAt
  convert h1 using 1
  symm
  refine ContinuousLinearMap.coe_injective (LinearMap.pi_ext fun i x => ?_)
  simp only [ContinuousLinearMap.coe_coe, FunLike.coe_sum, Finset.sum_apply,
    smul_apply, coordL, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have e : (Pi.single i x : Fin n → ℝ) = x • Pi.single i 1 := by
    ext j; by_cases h : j = i <;> simp [h]
  rw [e, map_smul]
  have : fderiv ℝ (ev p) y (Pi.single i 1) = ev (MvPolynomial.pderiv i p) y := by
    rw [← dd_evP]; rfl
  rw [this, Finset.sum_eq_single i]
  · simp; ring
  · intro j _ hj; simp [hj]
  · simp

lemma norm_sum_coord_le (a : Fin n → ℝ) :
    ‖∑ i, a i • coordL i‖ ≤ ∑ i, |a i| := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Finset.sum_nonneg fun i _ => abs_nonneg _) fun v => ?_
  simp only [FunLike.coe_sum, Finset.sum_apply, smul_apply, coordL,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  calc ‖∑ i, a i * v i‖ ≤ ∑ i, ‖a i * v i‖ := norm_sum_le _ _
    _ ≤ ∑ i, |a i| * ‖v‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v i) (abs_nonneg _)
    _ = (∑ i, |a i|) * ‖v‖ := by rw [Finset.sum_mul]

/-- `|h(y)| ≤ (|y| √n)^k ‖h‖` for harmonic homogeneous `h` of degree `k`. -/
lemma harm_sup_abs (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm k h) (y : Fin n → ℝ) :
    |ev h y| ≤ (nrm y * Real.sqrt n) ^ k * Real.sqrt (Nn n h) := by
  have h1 := harm_sup hn hh y
  have h2 : (ev h y)^2 ≤ ((nrm y * Real.sqrt n) ^ k * Real.sqrt (Nn n h)) ^ 2 := by
    have : ((nrm y * Real.sqrt n) ^ k * Real.sqrt (Nn n h)) ^ 2
        = nrm y ^ (2 * k) * (n : ℝ) ^ k * Nn n h := by
      have hb : Real.sqrt n ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg n)
      have hc : Real.sqrt (Nn n h) ^ 2 = Nn n h := Real.sq_sqrt (Nn_nonneg h)
      calc ((nrm y * Real.sqrt n) ^ k * Real.sqrt (Nn n h)) ^ 2
          = nrm y ^ (2 * k) * (Real.sqrt n ^ 2) ^ k * Real.sqrt (Nn n h) ^ 2 := by ring
        _ = _ := by rw [hb, hc]
    rw [this]; exact h1
  exact abs_le_of_sq_le_sq h2 (mul_nonneg (pow_nonneg (mul_nonneg (nrm_nonneg y) (Real.sqrt_nonneg _)) _) (Real.sqrt_nonneg _))

/-- the class of series of harmonic homogeneous polynomials with super-exponentially summable `L²` norms. -/
def HCls (H : ℕ → Pn n) : Prop :=
  (∀ k, IsHarm k (H k)) ∧ ∀ c : ℝ, 0 ≤ c → Summable fun k => c ^ k * Real.sqrt (Nn n (H k))

/-- the sum of the series. -/
noncomputable def Fs (H : ℕ → Pn n) (y : Fin n → ℝ) : ℝ := ∑' k, ev (H k) y

/-- the series of `i`-th partial derivatives (shifted by one degree). -/
noncomputable def Hd (i : Fin n) (H : ℕ → Pn n) : ℕ → Pn n := fun k => MvPolynomial.pderiv i (H (k + 1))

lemma sqrtNn_pderiv_le (hn : 2 ≤ n) {k : ℕ} {h : Pn n} (hh : IsHarm (k + 1) h) (i : Fin n) :
    Real.sqrt (Nn n (MvPolynomial.pderiv i h)) ≤ 2 ^ (n + 2) * 2 ^ k * Real.sqrt (Nn n h) := by
  have hg := harm_grad_L2 hn hh
  have h1 : Nn n (MvPolynomial.pderiv i h) ≤ ∑ j, Nn n (MvPolynomial.pderiv j h) :=
    Finset.single_le_sum (f := fun j => Nn n (MvPolynomial.pderiv j h)) (fun j _ => Nn_nonneg _)
      (Finset.mem_univ i)
  have h2 : ∑ j, Nn n (MvPolynomial.pderiv j h)
      = ((k + 1 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + n - 2) * Nn n h := by simpa [Nn] using hg
  have hnat : (k + 1) * (2 * k + n) ≤ (2 * (k + n + 1)) ^ 2 := by nlinarith
  have hpow : k + n + 1 < 2 ^ (k + n + 1) := Nat.lt_two_pow_self
  have hm : 2 * (k + n + 1) ≤ 2 ^ (n + 2) * 2 ^ k := by
    have : 2 ^ (n + 2) * 2 ^ k = 2 * 2 ^ (k + n + 1) := by
      rw [← pow_add, ← pow_succ']; congr 1; omega
    rw [this]; omega
  have hreal : ((k + 1 : ℕ) : ℝ) * (2 * ((k + 1 : ℕ) : ℝ) + n - 2) ≤ ((2 : ℝ) ^ (n + 2) * 2 ^ k) ^ 2 := by
    have a : (((k + 1) * (2 * k + n) : ℕ) : ℝ) ≤ (((2 * (k + n + 1)) ^ 2 : ℕ) : ℝ) := by exact_mod_cast hnat
    have b : ((2 * (k + n + 1) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (n + 2) * 2 ^ k := by exact_mod_cast hm
    have c : (((2 * (k + n + 1)) ^ 2 : ℕ) : ℝ) ≤ ((2 : ℝ) ^ (n + 2) * 2 ^ k) ^ 2 := by
      push_cast at b ⊢
      exact pow_le_pow_left₀ (by positivity) b 2
    push_cast at a c ⊢
    nlinarith
  have h3 : Nn n (MvPolynomial.pderiv i h) ≤ ((2 : ℝ) ^ (n + 2) * 2 ^ k) ^ 2 * Nn n h :=
    h1.trans (h2 ▸ mul_le_mul_of_nonneg_right hreal (Nn_nonneg h))
  calc Real.sqrt (Nn n (MvPolynomial.pderiv i h))
      ≤ Real.sqrt (((2 : ℝ) ^ (n + 2) * 2 ^ k) ^ 2 * Nn n h) := Real.sqrt_le_sqrt h3
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

lemma HCls.deriv (hn : 2 ≤ n) {H : ℕ → Pn n} (hH : HCls H) (i : Fin n) : HCls (Hd i H) := by
  refine ⟨fun k => isHarm_pderiv (hH.1 (k + 1)) i, fun c hc => ?_⟩
  set d : ℝ := 2 * (c + 1) with hd
  have hd0 : 0 < d := by positivity
  have hs : Summable fun k => d ^ (k + 1) * Real.sqrt (Nn n (H (k + 1))) :=
    (summable_nat_add_iff 1).2 (hH.2 d hd0.le)
  refine Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => ?_) ((hs.mul_left (2 ^ (n + 2) / d)))
  have h1 := sqrtNn_pderiv_le hn (hH.1 (k + 1)) i
  have h2 : c ^ k * 2 ^ k ≤ d ^ k := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) (by rw [hd]; linarith) k
  calc c ^ k * Real.sqrt (Nn n (Hd i H k))
      ≤ c ^ k * (2 ^ (n + 2) * 2 ^ k * Real.sqrt (Nn n (H (k + 1)))) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 2 ^ (n + 2) * (c ^ k * 2 ^ k) * Real.sqrt (Nn n (H (k + 1))) := by ring
    _ ≤ 2 ^ (n + 2) * d ^ k * Real.sqrt (Nn n (H (k + 1))) := by gcongr
    _ = 2 ^ (n + 2) / d * (d ^ (k + 1) * Real.sqrt (Nn n (H (k + 1)))) := by
        field_simp; ring

lemma nrm_le_sup (z : Fin n → ℝ) : nrm z ≤ n * ‖z‖ := by
  rw [nrm_eq]
  have h1 : LebesgueRd.sq z ≤ n * ‖z‖ ^ 2 := by
    unfold LebesgueRd.sq
    calc ∑ i, z i ^ 2 ≤ ∑ _i : Fin n, ‖z‖ ^ 2 := Finset.sum_le_sum fun i _ => by
          have := norm_le_pi_norm z i
          rw [Real.norm_eq_abs] at this
          have h := abs_le.1 this
          exact sq_le_sq' h.1 h.2
      _ = n * ‖z‖ ^ 2 := by simp
  have h2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast Nat.le_self_pow (two_ne_zero) n
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  calc LebesgueRd.sq z ≤ n * ‖z‖ ^ 2 := h1
    _ ≤ (n : ℝ) ^ 2 * ‖z‖ ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
    _ = (n * ‖z‖) ^ 2 := by ring

lemma summable_ev (hn : 2 ≤ n) {H : ℕ → Pn n} (hH : HCls H) (y : Fin n → ℝ) :
    Summable fun k => ev (H k) y := by
  refine Summable.of_norm_bounded
    (g := fun k => (nrm y * Real.sqrt n) ^ k * Real.sqrt (Nn n (H k)))
    (hH.2 _ (mul_nonneg (nrm_nonneg y) (Real.sqrt_nonneg _))) fun k => ?_
  rw [Real.norm_eq_abs]
  exact harm_sup_abs hn (hH.1 k) y

lemma hasFDerivAt_Fs (hn : 2 ≤ n) {H : ℕ → Pn n} (hH : HCls H) (y : Fin n → ℝ) :
    HasFDerivAt (Fs H) (∑ i, (Fs (Hd i H) y) • coordL i) y := by
  set R : ℝ := ‖y‖ + 1 with hR
  set s : Set (Fin n → ℝ) := Metric.ball 0 R with hs
  set c0 : ℝ := n * R * Real.sqrt n with hc0
  have hR0 : 0 < R := by positivity
  have hc0n : 0 ≤ c0 := by positivity
  set u : ℕ → ℝ := fun k => ∑ i, c0 ^ k * Real.sqrt (Nn n (Hd i H k)) with hu_def
  have hu : Summable u := summable_sum fun i _ => (hH.deriv hn i).2 c0 hc0n
  have hfd : ∀ k x, x ∈ s → HasFDerivAt (fun z => ev (H (k + 1)) z)
      (∑ i, ev (Hd i H k) x • coordL i) x := fun k x _ => hasFDerivAt_ev (H (k + 1)) x
  have hbd : ∀ k x, x ∈ s → ‖∑ i, ev (Hd i H k) x • coordL i‖ ≤ u k := by
    intro k x hx
    refine (norm_sum_coord_le _).trans (Finset.sum_le_sum fun i _ => ?_)
    have hx' : ‖x‖ < R := by simpa [hs] using hx
    have hnrm : nrm x ≤ n * R :=
      (nrm_le_sup x).trans (mul_le_mul_of_nonneg_left hx'.le (Nat.cast_nonneg n))
    refine (harm_sup_abs hn ((hH.deriv hn i).1 k) x).trans ?_
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg (nrm_nonneg x) (Real.sqrt_nonneg _))
      (mul_le_mul_of_nonneg_right hnrm (Real.sqrt_nonneg _)) k) (Real.sqrt_nonneg _)
  have hy : y ∈ s := by simp [hs, hR]
  have h0 : (0 : Fin n → ℝ) ∈ s := by simp [hs, hR]; positivity
  have hG := hasFDerivAt_tsum_of_isPreconnected (f := fun k z => ev (H (k + 1)) z) hu
    Metric.isOpen_ball (convex_ball _ _).isPreconnected hfd hbd h0
    ((summable_nat_add_iff 1).2 (summable_ev hn hH 0)) hy
  have hT : ∑' k, ∑ i, ev (Hd i H k) y • coordL i = ∑ i, (Fs (Hd i H) y) • coordL i :=
    (hasSum_sum fun i _ => (summable_ev hn (hH.deriv hn i) y).hasSum.smul_const (coordL i)).tsum_eq
  rw [hT] at hG
  have hF : Fs H = fun z => ev (H 0) z + ∑' k, ev (H (k + 1)) z :=
    funext fun z => (summable_ev hn hH z).tsum_eq_zero_add
  rw [hF]
  have h2 := (hasFDerivAt_ev (H 0) y).add hG
  convert h2 using 1
  simp [pderiv_hom_zero (hH.1 0).1, ev]

theorem contDiff_Fs (hn : 2 ≤ n) (m : ℕ) : ∀ H : ℕ → Pn n, HCls H → ContDiff ℝ m (Fs H) := by
  induction m with
  | zero =>
    intro H hH
    refine contDiff_zero.2 (continuous_iff_continuousAt.2 fun y => ?_)
    exact (hasFDerivAt_Fs hn hH y).continuousAt
  | succ m ih =>
    intro H hH
    have e : ((m + 1 : ℕ) : WithTop ℕ∞) = (m : WithTop ℕ∞) + 1 := by push_cast; rfl
    rw [e, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun y => (hasFDerivAt_Fs hn hH y).differentiableAt, fun h => ?_, fun v => ?_⟩
    · exact absurd h (by simp)
    · have : (fun x => fderiv ℝ (Fs H) x v) = fun x => ∑ i, Fs (Hd i H) x * v i := by
        funext x
        rw [(hasFDerivAt_Fs hn hH x).fderiv]
        simp [coordL]
      rw [this]
      exact ContDiff.sum fun i _ => (ih (Hd i H) (hH.deriv hn i)).mul contDiff_const

theorem contDiff_top_Fs (hn : 2 ≤ n) {H : ℕ → Pn n} (hH : HCls H) : ContDiff ℝ (⊤ : ℕ∞) (Fs H) :=
  contDiff_infty.2 fun m => contDiff_Fs hn m H hH

end MarkovTriple.BGL.SphereN
