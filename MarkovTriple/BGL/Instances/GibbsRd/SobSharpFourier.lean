import MarkovTriple.BGL.Instances.GibbsRd.SobSharpML2

/-!
# Plancherel with derivatives for `C_c^∞` functions (R17 SobSharp)

`E = EuclideanSpace ℝ (Fin d)`.  A real function `F` on `Fin d → ℝ` is lifted to the complex function
`lft F = (↑) ∘ F ∘ ofLp` on `E`; if `F ∈ C_c^∞` the lift is a Schwartz function, and Mathlib's Plancherel theorem
(`SchwartzMap.integral_norm_sq_fourier`) and the derivative rule (`SchwartzMap.fourier_lineDerivOp_eq`) give

`∫ (2π ξ_i)^{2k} |𝓕 (lft F) ξ|² dξ = ∫ |∂_i^k F|² dx`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff FourierTransform
open LineDeriv

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

/-- lift of a real function on `Fin d → ℝ` to a complex function on `EuclideanSpace ℝ (Fin d)`. -/
noncomputable def lft (F : (Fin d → ℝ) → ℝ) : EuclideanSpace ℝ (Fin d) → ℂ :=
  fun x => ((F (WithLp.ofLp x) : ℝ) : ℂ)

/-- the continuous linear equivalence `E ≃ ℝ^d`. -/
noncomputable abbrev eqv (d : ℕ) : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (Fin d → ℝ) :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)

theorem lft_contDiff {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (lft F) :=
  Complex.ofRealCLM.contDiff.comp (h.comp (eqv d).contDiff)

theorem lft_compact {F : (Fin d → ℝ) → ℝ} (h : HasCompactSupport F) : HasCompactSupport (lft F) := by
  have : HasCompactSupport (F ∘ (eqv d)) := h.comp_homeomorph (eqv d).toHomeomorph
  exact this.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)

/-- the Schwartz function associated with `F ∈ C_c^∞`. -/
noncomputable def sch {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    SchwartzMap (EuclideanSpace ℝ (Fin d)) ℂ :=
  (lft_compact hc).toSchwartzMap (lft_contDiff h)

theorem sch_apply {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ⇑(sch h hc) = lft F := rfl

theorem fderiv_lft {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (x v : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (lft F) x v = ((fderiv ℝ F (WithLp.ofLp x) (WithLp.ofLp v) : ℝ) : ℂ) := by
  have h1 : HasFDerivAt F (fderiv ℝ F (eqv d x)) (eqv d x) :=
    (h.differentiable (by simp) _).hasFDerivAt
  have h2 : HasFDerivAt (lft F) (Complex.ofRealCLM.comp ((fderiv ℝ F (eqv d x)).comp (eqv d : _ →L[ℝ] _))) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (h1.comp x (eqv d).hasFDerivAt)
  rw [h2.fderiv]
  rfl

theorem lineDerivOp_sch {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (i : Fin d) :
    ∂_{(EuclideanSpace.single i (1 : ℝ))} (sch h hc)
      = sch (contDiff_pd i h) (hasCompactSupport_pd i hc) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  show fderiv ℝ (lft F) x _ = lft (pd i F) x
  rw [fderiv_lft h]
  simp [lft, pd]

/-- `𝓕 (∂_i F) ξ = 2π i ξ_i 𝓕 F ξ`. -/
theorem fourier_lft_pd {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (i : Fin d)
    (ξ : EuclideanSpace ℝ (Fin d)) :
    𝓕 (lft (pd i F)) ξ = (2 * Real.pi * Complex.I * ((ξ i : ℝ) : ℂ)) * 𝓕 (lft F) ξ := by
  have e := DFunLike.congr_fun
    (SchwartzMap.fourier_lineDerivOp_eq (sch h hc) (EuclideanSpace.single i (1 : ℝ))) ξ
  simp only [lineDerivOp_sch h hc i] at e
  have hg : Function.HasTemperateGrowth (fun x : EuclideanSpace ℝ (Fin d) =>
      inner ℝ x (EuclideanSpace.single i (1 : ℝ))) := ((innerSL ℝ).flip _).hasTemperateGrowth
  rw [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hg, SchwartzMap.fourier_coe,
    SchwartzMap.fourier_coe] at e
  rw [sch_apply, sch_apply] at e
  rw [e]
  simp [EuclideanSpace.inner_single_right, Complex.real_smul, mul_assoc]

theorem fourier_lft_iterD {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (i : Fin d) :
    ∀ (k : ℕ) (ξ : EuclideanSpace ℝ (Fin d)),
      𝓕 (lft (iterD (List.replicate k i) F)) ξ
        = (2 * Real.pi * Complex.I * ((ξ i : ℝ) : ℂ)) ^ k * 𝓕 (lft F) ξ
  | 0, ξ => by simp [iterD]
  | k + 1, ξ => by
    have := fourier_lft_pd (contDiff_iterD (List.replicate k i) h)
      (hasCompactSupport_iterD (List.replicate k i) hc) i ξ
    rw [List.replicate_succ]
    show 𝓕 (lft (pd i (iterD (List.replicate k i) F))) ξ = _
    rw [this, fourier_lft_iterD h hc i k ξ]
    ring

theorem integral_lft_sq (F : (Fin d → ℝ) → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin d), ‖lft F x‖ ^ 2 = ∫ y, F y ^ 2 := by
  have := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp'
    (g := fun y : Fin d → ℝ => F y ^ 2)
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [lft]

/-- Plancherel for `C_c^∞` functions. -/
theorem integral_sq_fourier_lft {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    ∫ ξ : EuclideanSpace ℝ (Fin d), ‖𝓕 (lft F) ξ‖ ^ 2 = ∫ y, F y ^ 2 := by
  have := SchwartzMap.integral_norm_sq_fourier (sch h hc)
  rw [SchwartzMap.fourier_coe, sch_apply] at this
  rw [this, integral_lft_sq]

theorem pow_sq_fourier_lft {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (i : Fin d) (k : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    (2 * Real.pi * ξ i) ^ (2 * k) * ‖𝓕 (lft F) ξ‖ ^ 2
      = ‖𝓕 (lft (iterD (List.replicate k i) F)) ξ‖ ^ 2 := by
  have h0 : ‖2 * (Real.pi : ℂ) * Complex.I * ((ξ i : ℝ) : ℂ)‖ = |2 * Real.pi * ξ i| := by
    simp [Complex.norm_I, abs_mul, abs_of_pos Real.pi_pos]
  rw [fourier_lft_iterD h hc i k ξ, norm_mul, norm_pow, h0]
  have habs : (|2 * Real.pi * ξ i| ^ k) ^ 2 = (2 * Real.pi * ξ i) ^ (2 * k) := by
    rw [← pow_mul, mul_comm k 2, pow_mul, sq_abs, ← pow_mul]
  calc (2 * Real.pi * ξ i) ^ (2 * k) * ‖𝓕 (lft F) ξ‖ ^ 2
      = (|2 * Real.pi * ξ i| ^ k) ^ 2 * ‖𝓕 (lft F) ξ‖ ^ 2 := by rw [habs]
    _ = _ := (mul_pow _ _ _).symm

/-- Plancherel with `k` derivatives in direction `i`. -/
theorem integral_pow_sq_fourier_lft {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (i : Fin d) (k : ℕ) :
    ∫ ξ : EuclideanSpace ℝ (Fin d), (2 * Real.pi * ξ i) ^ (2 * k) * ‖𝓕 (lft F) ξ‖ ^ 2
      = ∫ y, iterD (List.replicate k i) F y ^ 2 := by
  rw [← integral_sq_fourier_lft (contDiff_iterD _ h) (hasCompactSupport_iterD _ hc)]
  exact integral_congr_ae (Eventually.of_forall fun ξ => pow_sq_fourier_lft h hc i k ξ)

end MarkovTriple.BGL.Instances.GibbsRd.Sob
