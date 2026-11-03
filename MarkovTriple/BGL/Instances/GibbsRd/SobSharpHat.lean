import MarkovTriple.BGL.Instances.GibbsRd.SobSharpFourier

/-!
# Fourier transform of mollified functions (R17 SobSharp)

Bridge `Fin d → ℝ ↔ EuclideanSpace ℝ (Fin d)` for integrals and convolutions, the convolution theorem for
`lft (mol F ρ_n)` and the bound `|𝓕 (lft (F ⋆ ρ_n))| ≤ |𝓕 (lft F)|`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff FourierTransform Convolution

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem integral_ofLp {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β] (H : (Fin d → ℝ) → β) :
    ∫ x : EuclideanSpace ℝ (Fin d), H (WithLp.ofLp x) = ∫ y, H y :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integral_comp' (g := H)

theorem integrable_lft {F : (Fin d → ℝ) → ℝ} (hF : Integrable F) : Integrable (lft F) := by
  have h := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin d)).integrable_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (g := fun y : Fin d → ℝ => ((F y : ℝ) : ℂ))
  exact h.2 hF.ofReal

/-- `lft` of a mollification is the convolution of the lifts. -/
theorem lft_mol (F ρ : (Fin d → ℝ) → ℝ) :
    lft (mol F ρ) = lft F ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] lft ρ := by
  funext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  have := integral_ofLp (fun t : Fin d → ℝ => ((F t * ρ (WithLp.ofLp x - t) : ℝ) : ℂ))
  have h2 : ∫ y : EuclideanSpace ℝ (Fin d), lft F y * lft ρ (x - y)
      = ∫ y : EuclideanSpace ℝ (Fin d), ((F (WithLp.ofLp y) * ρ (WithLp.ofLp x - WithLp.ofLp y) : ℝ) : ℂ) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp [lft]
  rw [h2, this, integral_complex_ofReal]
  rfl

theorem norm_fourier_sub_le {f g : EuclideanSpace ℝ (Fin d) → ℂ} (hf : Integrable f) (hg : Integrable g)
    (ξ : EuclideanSpace ℝ (Fin d)) : ‖𝓕 f ξ - 𝓕 g ξ‖ ≤ ∫ v, ‖f v - g v‖ := by
  rw [Real.fourier_eq, Real.fourier_eq, ← integral_sub]
  · refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp [← smul_sub]
  · exact (Real.fourierIntegral_convergent_iff _).2 hf
  · exact (Real.fourierIntegral_convergent_iff _).2 hg

theorem norm_fourier_le {f : EuclideanSpace ℝ (Fin d) → ℂ} (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖𝓕 f ξ‖ ≤ ∫ v, ‖f v‖ := by
  rw [Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp

theorem integral_norm_lft_sub (F G : (Fin d → ℝ) → ℝ) :
    ∫ v : EuclideanSpace ℝ (Fin d), ‖lft F v - lft G v‖ = ∫ y, |F y - G y| := by
  rw [← integral_ofLp (fun y : Fin d → ℝ => |F y - G y|)]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [lft, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

theorem norm_hat_rho_le (n : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : ‖𝓕 (lft (rho (d := d) n)) ξ‖ ≤ 1 := by
  refine (norm_fourier_le ξ).trans (le_of_eq ?_)
  have : ∀ v : EuclideanSpace ℝ (Fin d), ‖lft (rho (d := d) n) v‖ = rho n (WithLp.ofLp v) := fun v => by
    simp [lft, abs_of_nonneg (rho_nonneg n _)]
  simp_rw [this]
  rw [integral_ofLp (rho (d := d) n), integral_rho]

theorem hat_mol {F : (Fin d → ℝ) → ℝ} (hF : Integrable F) (n : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    𝓕 (lft (mol F (rho n))) ξ = 𝓕 (lft (rho n)) ξ * 𝓕 (lft F) ξ := by
  rw [lft_mol, Real.fourier_mul_convolution_eq (integrable_lft hF)
    (integrable_lft (integrable_rho n))]
  ring

theorem norm_hat_mol_le {F : (Fin d → ℝ) → ℝ} (hF : Integrable F) (n : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) :
    ‖𝓕 (lft (mol F (rho n))) ξ‖ ≤ ‖𝓕 (lft F) ξ‖ := by
  rw [hat_mol hF, norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (norm_hat_rho_le n ξ)

theorem tendsto_hat_mol {F : (Fin d → ℝ) → ℝ} (hF : Integrable F) (ξ : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => 𝓕 (lft (mol F (rho n))) ξ) atTop (𝓝 (𝓕 (lft F) ξ)) := by
  have h0 := tendsto_integral_abs_mol_sub hF
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h0
  refine (norm_fourier_sub_le (integrable_lft (integrable_mol hF n)) (integrable_lft hF) ξ).trans
    (le_of_eq ?_)
  exact integral_norm_lft_sub _ _

end MarkovTriple.BGL.Instances.GibbsRd.Sob
