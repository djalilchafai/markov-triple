import Mathlib

/-!
# The regularised square root `ψ_ε(r) = √(r + ε²) − ε` (BGL, proof of Thm 3.3.18), globally smooth form

`psiS ε` is smooth on all of `ℝ`, vanishes at `0`, and coincides with `√(r+ε²) − ε` on `(-ε²/4, ∞)`
(so on `[0,∞)` with a neighbourhood); it is needed because the `𝒜`-stability F3 is for globally smooth maps.
-/

open Filter Topology Set

namespace MarkovTriple.BGL

/-- the gluing `s(r) = r` for `r ≥ -δ`, `s > -2δ`. -/
noncomputable def gluS (δ : ℝ) (r : ℝ) : ℝ := r * Real.smoothTransition ((r + 2 * δ) / δ)

lemma gluS_smooth (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (gluS δ) :=
  contDiff_id.mul (Real.smoothTransition.contDiff.comp ((contDiff_id.add contDiff_const).div_const δ))

lemma gluS_eq {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : -δ ≤ r) : gluS δ r = r := by
  unfold gluS
  rw [Real.smoothTransition.one_of_one_le, mul_one]
  rw [le_div_iff₀ hδ]; linarith

lemma gluS_ge {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : -(2 * δ) ≤ gluS δ r := by
  unfold gluS
  by_cases h : r ≤ -(2 * δ)
  · rw [Real.smoothTransition.zero_of_nonpos, mul_zero]; linarith
    rw [div_nonpos_iff]; right; exact ⟨by linarith, hδ.le⟩
  · push Not at h
    have h0 := Real.smoothTransition.nonneg ((r + 2 * δ) / δ)
    have h1 := Real.smoothTransition.le_one ((r + 2 * δ) / δ)
    by_cases hr : 0 ≤ r
    · nlinarith
    · push Not at hr
      nlinarith

/-- `ψ_ε`, globally smooth. -/
noncomputable def psiS (ε : ℝ) (r : ℝ) : ℝ := Real.sqrt (gluS (ε ^ 2 / 4) r + ε ^ 2) - ε

lemma gluS_pos {ε : ℝ} (hε : 0 < ε) (r : ℝ) : 0 < gluS (ε ^ 2 / 4) r + ε ^ 2 := by
  have := gluS_ge (by positivity : (0 : ℝ) < ε ^ 2 / 4) r
  nlinarith [sq_pos_of_pos hε]

lemma psiS_smooth {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (psiS ε) := by
  unfold psiS
  refine ContDiff.sub (ContDiff.sqrt ((gluS_smooth _).add contDiff_const) fun r => (gluS_pos hε r).ne')
    contDiff_const

lemma psiS_eq {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : -(ε ^ 2 / 4) ≤ r) :
    psiS ε r = Real.sqrt (r + ε ^ 2) - ε := by
  unfold psiS; rw [gluS_eq (by positivity) hr]

lemma psiS_eventuallyEq {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    psiS ε =ᶠ[𝓝 r] fun r' => Real.sqrt (r' + ε ^ 2) - ε := by
  have : Ioi (-(ε ^ 2 / 4)) ∈ 𝓝 r := Ioi_mem_nhds (by nlinarith [sq_pos_of_pos hε])
  filter_upwards [this] with r' hr' using psiS_eq hε (le_of_lt hr')

lemma psiS_zero {ε : ℝ} (hε : 0 < ε) : psiS ε 0 = 0 := by
  rw [psiS_eq hε (by nlinarith [sq_pos_of_pos hε]), zero_add, Real.sqrt_sq hε.le]; ring

lemma hasDerivAt_sqrt_shift {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    HasDerivAt (fun r' => Real.sqrt (r' + ε ^ 2) - ε) (1 / (2 * Real.sqrt (r + ε ^ 2))) r := by
  have h := ((hasDerivAt_id r).add_const (ε ^ 2)).sqrt (by simp; nlinarith [sq_pos_of_pos hε])
  have := h.sub_const ε
  simpa using this

/-- `ψ_ε'(r) = 1/(2 √(r+ε²))` for `r ≥ 0`. -/
lemma deriv_psiS {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    deriv (psiS ε) r = 1 / (2 * Real.sqrt (r + ε ^ 2)) := by
  rw [(psiS_eventuallyEq hε hr).deriv_eq]
  exact (hasDerivAt_sqrt_shift hε hr).deriv

lemma deriv_psiS_eventuallyEq {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    deriv (psiS ε) =ᶠ[𝓝 r] fun r' => 1 / (2 * Real.sqrt (r' + ε ^ 2)) := by
  have : Ioi (-(ε ^ 2 / 4)) ∈ 𝓝 r := Ioi_mem_nhds (by nlinarith [sq_pos_of_pos hε])
  filter_upwards [this] with r' hr'
  have hr'' : -(ε ^ 2 / 4) < r' := hr'
  have e : psiS ε =ᶠ[𝓝 r'] fun r'' => Real.sqrt (r'' + ε ^ 2) - ε := by
    have : Ioi (-(ε ^ 2 / 4)) ∈ 𝓝 r' := Ioi_mem_nhds hr''
    filter_upwards [this] with r'' hr''' using psiS_eq hε (le_of_lt hr''')
  rw [e.deriv_eq]
  have h := ((hasDerivAt_id r').add_const (ε ^ 2)).sqrt (by simp; nlinarith [sq_pos_of_pos hε])
  have := h.sub_const ε
  simpa using this.deriv

/-- `ψ_ε''(r) = -1/(4 (r+ε²)^{3/2})` for `r ≥ 0`. -/
lemma deriv2_psiS {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    deriv (deriv (psiS ε)) r = -1 / (4 * (Real.sqrt (r + ε ^ 2)) ^ 3) := by
  rw [(deriv_psiS_eventuallyEq hε hr).deriv_eq]
  have hpos : 0 < r + ε ^ 2 := by nlinarith [sq_pos_of_pos hε]
  have hs : 0 < Real.sqrt (r + ε ^ 2) := Real.sqrt_pos.2 hpos
  have h1 : HasDerivAt (fun r' => Real.sqrt (r' + ε ^ 2)) (1 / (2 * Real.sqrt (r + ε ^ 2))) r := by
    have h := ((hasDerivAt_id r).add_const (ε ^ 2)).sqrt hpos.ne'
    simpa using h
  have h2 := (h1.const_mul 2).inv (by positivity)
  have e : (fun r' => 1 / (2 * Real.sqrt (r' + ε ^ 2))) = (fun y => (2 * Real.sqrt (y + ε ^ 2))⁻¹) := by
    funext y; simp [one_div]
  have h2' : HasDerivAt (fun y => (2 * Real.sqrt (y + ε ^ 2))⁻¹)
      (-(2 * (1 / (2 * Real.sqrt (r + ε ^ 2)))) / (2 * Real.sqrt (r + ε ^ 2)) ^ 2) r := h2
  rw [e, h2'.deriv]
  field_simp
  norm_num

lemma contDiff_deriv_psiS {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (deriv (psiS ε)) :=
  (contDiff_infty_iff_deriv.1 (psiS_smooth hε)).2

lemma contDiff_deriv2_psiS {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv (psiS ε))) :=
  (contDiff_infty_iff_deriv.1 (contDiff_deriv_psiS hε)).2

/-- local bounds for `ψ_ε, ψ_ε', ψ_ε''`. -/
lemma psiS_bounds {ε : ℝ} (hε : 0 < ε) (M : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : ℝ, |y| ≤ M →
    |psiS ε y| ≤ B ∧ |deriv (psiS ε) y| ≤ B ∧ |deriv (deriv (psiS ε)) y| ≤ B := by
  obtain ⟨C0, h0⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    (psiS_smooth hε).continuous.continuousOn
  obtain ⟨C1, h1⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    (contDiff_deriv_psiS hε).continuous.continuousOn
  obtain ⟨C2, h2⟩ := (isCompact_Icc (a := -M) (b := M)).exists_bound_of_continuousOn
    (contDiff_deriv2_psiS hε).continuous.continuousOn
  refine ⟨max (max |C0| |C1|) |C2|, by positivity, fun y hy => ?_⟩
  have hy' : y ∈ Icc (-M) M := abs_le.1 hy
  refine ⟨?_, ?_, ?_⟩
  · have := h0 y hy'; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  · have := h1 y hy'; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans ((le_max_right _ _).trans (le_max_left _ _)))
  · have := h2 y hy'; rw [Real.norm_eq_abs] at this
    exact this.trans ((le_abs_self _).trans (le_max_right _ _))

end MarkovTriple.BGL
