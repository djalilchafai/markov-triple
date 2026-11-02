import Mathlib

/-!
# Hadamard's lemma and smooth division by `sin`

* `hadamard`: `H` smooth with `H 0 = 0` ⇒ `H φ = φ * G φ` with `G` smooth.
* `Dq F = F'/sin` (extended by `F''/cos` at the zeros of `sin`) is smooth when `F'` vanishes at all
  `kπ` (in particular for `F` even and `2π`-periodic).
-/

open Real Filter Topology
open scoped Real

namespace MarkovTriple.BGL.Instances.Sphere

lemma smooth_deriv {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv h) := (contDiff_infty_iff_deriv.1 hh).2

/-- parametric integral `φ ↦ ∫₀¹ s^p h(sφ) ds`. -/
noncomputable def Psi (p : ℕ) (h : ℝ → ℝ) (φ : ℝ) : ℝ := ∫ s in (0:ℝ)..1, s ^ p * h (s * φ)

lemma continuous_Psi (p : ℕ) {h : ℝ → ℝ} (hh : Continuous h) : Continuous (Psi p h) := by
  unfold Psi
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun φ s => s ^ p * h (s * φ)) (by fun_prop) 0 1

lemma hasDerivAt_Psi (p : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (φ₀ : ℝ) :
    HasDerivAt (Psi p h) (Psi (p + 1) (deriv h) φ₀) φ₀ := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have hd' : Continuous (deriv h) := hh.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℝ) (|φ₀| + 1)).exists_bound_of_continuousOn
    hd'.continuousOn
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := MeasureTheory.volume) (a := 0) (b := 1)
    (F := fun φ s => s ^ p * h (s * φ)) (F' := fun φ s => s ^ (p + 1) * deriv h (s * φ))
    (x₀ := φ₀) (s := Metric.ball φ₀ 1) (bound := fun _ => C)
    (Metric.ball_mem_nhds _ one_pos)
    (Eventually.of_forall fun x => by
      exact (Continuous.aestronglyMeasurable (by fun_prop)))
    (by exact Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.aestronglyMeasurable (by fun_prop))
    (by
      refine Filter.Eventually.of_forall fun t ht x hx => ?_
      rw [Set.uIoc_of_le zero_le_one] at ht
      have h1 : ‖deriv h (t * x)‖ ≤ C := by
        apply hC
        rw [mem_closedBall_zero_iff, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos ht.1]
        have hx' : |x - φ₀| < 1 := by simpa [Real.dist_eq] using hx
        have : |x| ≤ |φ₀| + 1 := by
          calc |x| = |(x - φ₀) + φ₀| := by ring_nf
            _ ≤ |x - φ₀| + |φ₀| := abs_add_le _ _
            _ ≤ _ := by linarith
        nlinarith [abs_nonneg x, ht.1, ht.2]
      have h2 : ‖t ^ (p + 1)‖ ≤ 1 := by
        rw [norm_pow, Real.norm_eq_abs, abs_of_pos ht.1]
        exact pow_le_one₀ ht.1.le ht.2
      rw [norm_mul]
      calc ‖t ^ (p + 1)‖ * ‖deriv h (t * x)‖ ≤ 1 * C :=
            mul_le_mul h2 h1 (norm_nonneg _) zero_le_one
        _ = C := one_mul C)
    intervalIntegrable_const
    (by
      refine Filter.Eventually.of_forall fun t ht x hx => ?_
      have := ((hd (t * x)).hasDerivAt.comp x ((hasDerivAt_id x).const_mul t)).const_mul (t ^ p)
      simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using this)
  exact key.2

lemma contDiff_Psi (p : ℕ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) :
    ContDiff ℝ (⊤ : ℕ∞) (Psi p h) := by
  have : ∀ n : ℕ, ∀ p : ℕ, ∀ h : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) h → ContDiff ℝ n (Psi p h) := by
    intro n
    induction n with
    | zero =>
      intro p h hh
      exact contDiff_zero.2 (continuous_Psi p hh.continuous)
    | succ n ih =>
      intro p h hh
      have e : ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 := by push_cast; rfl
      rw [e, contDiff_succ_iff_deriv]
      refine ⟨fun x => (hasDerivAt_Psi p hh x).differentiableAt, by simp, ?_⟩
      have : deriv (Psi p h) = Psi (p + 1) (deriv h) :=
        funext fun x => (hasDerivAt_Psi p hh x).deriv
      rw [this]
      exact ih (p + 1) (deriv h) (smooth_deriv hh)
  exact contDiff_infty.2 fun n => this n p h hh

theorem hadamard {H : ℝ → ℝ} (hH : ContDiff ℝ (⊤ : ℕ∞) H) (h0 : H 0 = 0) :
    ∃ G : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) G ∧ (∀ φ, H φ = φ * G φ) ∧ G 0 = deriv H 0 := by
  have hd : Differentiable ℝ H := hH.differentiable (by simp)
  have hd' : Continuous (deriv H) := hH.continuous_deriv (by simp)
  refine ⟨Psi 0 (deriv H), contDiff_Psi 0 (smooth_deriv hH), fun φ => ?_, by simp [Psi]⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (f := fun s => H (s * φ)) (f' := fun s => φ * deriv H (s * φ))
    (fun s _ => by
      have := (hd (s * φ)).hasDerivAt.comp s ((hasDerivAt_id s).mul_const φ)
      have e : (fun s => H (s * φ)) = H ∘ fun y => id y * φ := rfl
      rw [e]
      convert this using 1
      simp [mul_comm])
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  simp only [one_mul, zero_mul, h0, sub_zero] at this
  rw [← this, Psi, ← intervalIntegral.integral_const_mul]
  simp

/-- `F'/sin`, extended by `F''/cos` at the zeros of `sin` (l'Hôpital). -/
noncomputable def Dq (F : ℝ → ℝ) (θ : ℝ) : ℝ :=
  if Real.sin θ = 0 then deriv (deriv F) θ / Real.cos θ else deriv F θ / Real.sin θ

lemma sin_ne_zero_of_abs_lt {φ : ℝ} (h0 : φ ≠ 0) (h : |φ| < π) : Real.sin φ ≠ 0 := by
  intro hs
  obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
  have : n ≠ 0 := by
    rintro rfl
    apply h0; rw [← hn]; simp
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    have : 1 ≤ |n| := Int.one_le_abs this
    exact_mod_cast this
  rw [← hn, abs_mul, abs_of_pos Real.pi_pos] at h
  nlinarith [Real.pi_pos]

lemma contDiffAt_Dq_kpi {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF0 : ∀ k : ℤ, deriv F (k * π) = 0) (k : ℤ) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Dq F) (k * π) := by
  set θ₀ : ℝ := k * π with hθ₀
  have hHk : ContDiff ℝ (⊤ : ℕ∞) (fun φ => deriv F (θ₀ + φ)) :=
    (smooth_deriv hF).comp (contDiff_const.add contDiff_id)
  have hHk0 : deriv F (θ₀ + 0) = 0 := by rw [add_zero]; exact hF0 k
  obtain ⟨G, hG, hGe, hG0⟩ := hadamard hHk hHk0
  obtain ⟨S, hS, hSe, hS0⟩ := hadamard (Real.contDiff_sin (n := (⊤ : ℕ∞))) Real.sin_zero
  have hS0' : S 0 = 1 := by rw [hS0, Real.deriv_sin]; simp
  have hSne : ∀ φ, |φ| < π → S φ ≠ 0 := by
    intro φ hφ
    by_cases h0 : φ = 0
    · rw [h0, hS0']; exact one_ne_zero
    · intro h
      exact sin_ne_zero_of_abs_lt h0 hφ (by rw [hSe, h, mul_zero])
  have hsign : ((-1 : ℝ) ^ k) ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hK : ContDiffAt ℝ (⊤ : ℕ∞) (fun φ => G φ / ((-1 : ℝ) ^ k * S φ)) 0 :=
    hG.contDiffAt.div (contDiffAt_const.mul hS.contDiffAt)
      (mul_ne_zero hsign (hSne 0 (by simpa using Real.pi_pos)))
  have hGd : G 0 = deriv (deriv F) θ₀ := by
    rw [hG0, deriv_comp_const_add]; simp
  have heq : Dq F =ᶠ[𝓝 θ₀] fun θ => (fun φ => G φ / ((-1 : ℝ) ^ k * S φ)) (θ - θ₀) := by
    filter_upwards [Metric.ball_mem_nhds θ₀ Real.pi_pos] with θ hθ
    have hφ : |θ - θ₀| < π := by simpa [Real.dist_eq] using hθ
    set φ := θ - θ₀ with hφdef
    have hθφ : θ = φ + k * π := by rw [hφdef, hθ₀]; ring
    have hsin : Real.sin θ = (-1) ^ k * Real.sin φ := by rw [hθφ]; exact Real.sin_add_int_mul_pi _ _
    by_cases h0 : φ = 0
    · have hθe : θ = θ₀ := by rw [hθφ, h0, zero_add]
      have hs0 : Real.sin θ = 0 := by rw [hθe, hθ₀]; exact Real.sin_int_mul_pi k
      have hc : Real.cos θ = (-1) ^ k := by rw [hθe, hθ₀]; exact Real.cos_int_mul_pi k
      unfold Dq; rw [if_pos hs0, hc]
      simp only [h0, hS0', mul_one, hGd, hθe, sub_self]
    · have hsne : Real.sin θ ≠ 0 := by
        rw [hsin]; exact mul_ne_zero hsign (sin_ne_zero_of_abs_lt h0 hφ)
      have hSφ := hSne φ hφ
      have h1 : deriv F θ = φ * G φ := by
        have := hGe φ
        rw [show θ = θ₀ + φ by rw [hθ₀]; linarith]; exact this
      unfold Dq; rw [if_neg hsne, h1, hsin, hSe]
      field_simp
  have hK' : ContDiffAt ℝ (⊤ : ℕ∞) (fun θ => (fun φ => G φ / ((-1 : ℝ) ^ k * S φ)) (θ - θ₀)) θ₀ := by
    have hsub : ContDiffAt ℝ (⊤ : ℕ∞) (fun θ : ℝ => θ - θ₀) θ₀ :=
      contDiffAt_id.sub contDiffAt_const
    have hK0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun φ => G φ / ((-1 : ℝ) ^ k * S φ))
        ((fun θ : ℝ => θ - θ₀) θ₀) := by simpa using hK
    exact ContDiffAt.comp (g := fun φ => G φ / ((-1 : ℝ) ^ k * S φ))
      (f := fun θ : ℝ => θ - θ₀) θ₀ hK0 hsub
  exact hK'.congr_of_eventuallyEq heq

theorem contDiff_Dq {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hF0 : ∀ k : ℤ, deriv F (k * π) = 0) : ContDiff ℝ (⊤ : ℕ∞) (Dq F) := by
  rw [contDiff_iff_contDiffAt]
  intro θ₁
  by_cases hs : Real.sin θ₁ = 0
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
    rw [← hn]; exact contDiffAt_Dq_kpi hF hF0 n
  · have hev : ∀ᶠ θ in 𝓝 θ₁, Real.sin θ ≠ 0 :=
      Real.continuous_sin.continuousAt.eventually_ne hs
    have : ContDiffAt ℝ (⊤ : ℕ∞) (fun θ => deriv F θ / Real.sin θ) θ₁ :=
      (smooth_deriv hF).contDiffAt.div (Real.contDiff_sin.contDiffAt) hs
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hev] with θ hθ
    simp [Dq, hθ]

lemma sin_mul_Dq {F : ℝ → ℝ} (hF0 : ∀ k : ℤ, deriv F (k * π) = 0) (θ : ℝ) :
    Real.sin θ * Dq F θ = deriv F θ := by
  by_cases hs : Real.sin θ = 0
  · obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 hs
    rw [hs, zero_mul, ← hn, hF0 n]
  · simp only [Dq, if_neg hs]; field_simp

/-! ### Even, periodic functions -/

lemma deriv_odd {F : ℝ → ℝ} (he : ∀ θ, F (-θ) = F θ) (θ : ℝ) : deriv F (-θ) = -deriv F θ := by
  have h : F = fun x => F (-x) := funext fun x => (he x).symm
  have := congrArg (fun g => deriv g θ) h
  simp only [deriv_comp_neg] at this
  linarith

lemma deriv_periodic {F : ℝ → ℝ} (hp : ∀ θ, F (θ + 2 * π) = F θ) (θ : ℝ) :
    deriv F (θ + 2 * π) = deriv F θ := by
  have h : F = fun x => F (x + 2 * π) := funext fun x => (hp x).symm
  have := congrArg (fun g => deriv g θ) h
  simp only [deriv_comp_add_const] at this
  exact this.symm

lemma deriv_even_of_odd {G : ℝ → ℝ} (ho : ∀ θ, G (-θ) = -G θ) (θ : ℝ) :
    deriv G (-θ) = deriv G θ := by
  have h : (fun x => G (-x)) = fun x => -G x := funext ho
  have := congrArg (fun g => deriv g θ) h
  simp only [deriv_comp_neg, deriv.fun_neg] at this
  linarith

lemma deriv_zero_of_even_periodic {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (he : ∀ θ, F (-θ) = F θ) (hp : ∀ θ, F (θ + 2 * π) = F θ) (k : ℤ) :
    deriv F (k * π) = 0 := by
  have ho := deriv_odd he
  have hper : Function.Periodic (deriv F) (2 * π) := deriv_periodic hp
  have h0 : deriv F 0 = 0 := by have := ho 0; simp at this; linarith
  have hpi : deriv F π = 0 := by
    have h1 : deriv F π = deriv F (-π) := by
      have := hper (-π); rw [show -π + 2 * π = π by ring] at this; exact this
    have := ho π; linarith
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · have := hper.int_mul m 0
    rw [zero_add] at this
    rw [show ((2 * m : ℤ) : ℝ) * π = m * (2 * π) by push_cast; ring, this, h0]
  · have := hper.int_mul m π
    rw [show ((2 * m + 1 : ℤ) : ℝ) * π = π + m * (2 * π) by push_cast; ring, this, hpi]

lemma Dq_even {F : ℝ → ℝ} (he : ∀ θ, F (-θ) = F θ) (θ : ℝ) : Dq F (-θ) = Dq F θ := by
  have h1 := deriv_odd he θ
  have h2 := deriv_even_of_odd (deriv_odd he) θ
  by_cases hs : Real.sin θ = 0
  · have hs' : Real.sin (-θ) = 0 := by rw [Real.sin_neg, hs, neg_zero]
    unfold Dq; rw [if_pos hs, if_pos hs', h2, Real.cos_neg]
  · have hs' : Real.sin (-θ) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.2 hs
    unfold Dq; rw [if_neg hs, if_neg hs', h1, Real.sin_neg, neg_div_neg_eq]

lemma Dq_periodic {F : ℝ → ℝ} (he : ∀ θ, F (-θ) = F θ) (hp : ∀ θ, F (θ + 2 * π) = F θ)
    (θ : ℝ) : Dq F (θ + 2 * π) = Dq F θ := by
  have h1 := deriv_periodic hp θ
  have h2 := deriv_periodic (fun x => deriv_periodic hp x) θ
  have hs : Real.sin (θ + 2 * π) = Real.sin θ := Real.sin_add_two_pi θ
  have hc : Real.cos (θ + 2 * π) = Real.cos θ := Real.cos_add_two_pi θ
  simp only [Dq, hs, hc, h1, h2]

end MarkovTriple.BGL.Instances.Sphere
