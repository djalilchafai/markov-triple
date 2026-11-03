import MarkovTriple.BGL.Instances.GibbsRd.SobWeak

/-!
# Mollification and weak derivatives (R16 Sob, S2)

`mol f ρ x = ∫ f(t) ρ(x - t) dt`; `∂_i (h ⋆ ρ) = g ⋆ ρ` when `g` is the weak `∂_i h`
(Evans §5.3 Thm 1(ii)).  A fixed sequence of normalised bumps `rho n` supported in `ball 0 (1/(n+1))`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff Convolution

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

/-- mollification (plain integral). -/
noncomputable def mol (f ρ : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ := fun x => ∫ t, f t * ρ (x - t)

theorem mol_eq_conv (f ρ : (Fin d → ℝ) → ℝ) :
    mol f ρ = f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ := by
  funext x; simp [mol, convolution_def]

theorem contDiff_mol {f ρ : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) : ContDiff ℝ ∞ (mol f ρ) := by
  rw [mol_eq_conv]
  exact hρc.contDiff_convolution_right _ hf hρ

theorem pd_mol {f ρ : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) (hρ : ContDiff ℝ ∞ ρ)
    (hρc : HasCompactSupport ρ) (i : Fin d) (x : Fin d → ℝ) :
    pd i (mol f ρ) x = ∫ t, f t * pd i ρ (x - t) := by
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  have h := hρc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hf hρ1 x
  rw [← mol_eq_conv] at h
  have hint : Integrable (fun t => (ContinuousLinearMap.lsmul ℝ ℝ).precompR (Fin d → ℝ) (f t)
      (fderiv ℝ ρ (x - t))) volume :=
    (hρc.fderiv ℝ).convolutionExists_right _ hf (hρ.continuous_fderiv (by simp)) x
  simp only [pd]
  rw [h.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp

theorem pd_mol_weak {h g ρ : (Fin d → ℝ) → ℝ} {i : Fin d} (hw : WeakDeriv h g i)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) : pd i (mol h ρ) = mol g ρ := by
  funext x
  rw [pd_mol hw.1 hρ hρc]
  set φ : (Fin d → ℝ) → ℝ := fun t => ρ (x - t) with hφdef
  have hφ : ContDiff ℝ ∞ φ := hρ.comp (contDiff_const.sub contDiff_id)
  have hφc : HasCompactSupport φ := hρc.comp_homeomorph (Homeomorph.subLeft x)
  have hpd : ∀ t, pd i φ t = - pd i ρ (x - t) := by
    intro t
    have h1 : HasFDerivAt φ ((fderiv ℝ ρ (x - t)).comp (0 - ContinuousLinearMap.id ℝ _)) t :=
      (hρ.differentiable (by simp) (x - t)).hasFDerivAt.comp t
        ((hasFDerivAt_const x t).sub (hasFDerivAt_id t))
    simp only [pd]
    rw [h1.fderiv]
    simp
  have e : ∫ t, h t * pd i φ t = -∫ t, g t * φ t := hw.2.2 φ hφ hφc
  simp only [hpd, mul_neg, integral_neg] at e
  have : ∫ t, h t * pd i ρ (x - t) = ∫ t, g t * φ t := by linarith
  rw [this]
  rfl

theorem iterD_mol {ρ : (Fin d → ℝ) → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    ∀ (l : List (Fin d)) {f g : (Fin d → ℝ) → ℝ}, WeakIter l f g → iterD l (mol f ρ) = mol g ρ
  | [], _, _, h => by subst h; rfl
  | i :: l, _, _, ⟨h, hh, hg⟩ => by
    show pd i (iterD l (mol _ ρ)) = _
    rw [iterD_mol hρ hρc l hh]
    exact pd_mol_weak hg hρ hρc

theorem iterD_sub (l : List (Fin d)) {a b : (Fin d → ℝ) → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) : iterD l (fun x => a x - b x) = fun x => iterD l a x - iterD l b x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    show pd i (iterD l (fun x => a x - b x)) = _
    rw [ih]
    funext x
    have h1 := contDiff_iterD l ha
    have h2 := contDiff_iterD l hb
    have : fderiv ℝ (fun y => iterD l a y - iterD l b y) x
        = fderiv ℝ (iterD l a) x - fderiv ℝ (iterD l b) x :=
      fderiv_sub (h1.differentiable (by simp) x) (h2.differentiable (by simp) x)
    simp only [pd]
    rw [this]
    simp [iterD, pd]

/-! ### the mollifier sequence -/

/-- bump of outer radius `1/(n+1)`. -/
noncomputable def bump (n : ℕ) : ContDiffBump (0 : Fin d → ℝ) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]; nlinarith⟩

/-- the mollifier `ρ_n`: smooth, `≥ 0`, `∫ = 1`, supported in the ball of radius `1/(n+1)`. -/
noncomputable def rho (n : ℕ) : (Fin d → ℝ) → ℝ := (bump n).normed volume

theorem contDiff_rho (n : ℕ) : ContDiff ℝ ∞ (rho (d := d) n) := (bump n).contDiff_normed
theorem hasCompactSupport_rho (n : ℕ) : HasCompactSupport (rho (d := d) n) :=
  (bump n).hasCompactSupport_normed
theorem rho_nonneg (n : ℕ) (x : Fin d → ℝ) : 0 ≤ rho n x := (bump n).nonneg_normed x
theorem integral_rho (n : ℕ) : ∫ x, rho (d := d) n x = 1 := (bump n).integral_normed
theorem integrable_rho (n : ℕ) : Integrable (rho (d := d) n) := (bump n).integrable_normed
theorem support_rho (n : ℕ) : Function.support (rho (d := d) n) = Metric.ball 0 (1 / ((n : ℝ) + 1)) :=
  (bump n).support_normed_eq

end MarkovTriple.BGL.Instances.GibbsRd.Sob
