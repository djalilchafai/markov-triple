import MarkovTriple.BGL.Instances.GibbsRd.SobSharpHat
import MarkovTriple.BGL.Instances.GibbsRd.SobCore

/-!
# Weighted `L²` bound for the Fourier transform (R17 SobSharp)

`wgt k ξ = 1 + Σ_i (2π ξ_i)^{2k}`.  For `F` compactly supported, `F ∈ L²`, with iterated weak derivatives
`G_i = ∂_i^k F ∈ L²`:   `∫ wgt k |𝓕 F|² ≤ ‖F‖₂² + Σ_i ‖G_i‖₂²`
(Plancherel for the mollifications `F ⋆ ρ_n`, `L²`-contraction of mollification, pointwise convergence of the
transforms and Fatou's lemma).
-/

open MeasureTheory Filter Topology
open scoped ContDiff FourierTransform ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

/-- the weight `1 + Σ_i (2π ξ_i)^{2k}`. -/
noncomputable def wgt (d k : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : ℝ := 1 + ∑ i, (2 * Real.pi * ξ i) ^ (2 * k)

theorem wgt_pos (k : ℕ) (ξ : EuclideanSpace ℝ (Fin d)) : 0 < wgt d k ξ := by
  unfold wgt
  have : 0 ≤ ∑ i, (2 * Real.pi * ξ i) ^ (2 * k) :=
    Finset.sum_nonneg fun i _ => (even_two_mul k).pow_nonneg _
  linarith

theorem continuous_hat {F : (Fin d → ℝ) → ℝ} (hF : Integrable F) : Continuous (𝓕 (lft F)) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂
    (integrable_lft hF)

theorem integrable_sq_hat {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => ‖𝓕 (lft F) ξ‖ ^ 2) := by
  have := ((𝓕 (sch h hc)).memLp 2 volume).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  simpa [SchwartzMap.fourier_coe, sch_apply] using this

/-- energy identity for `C_c^∞` functions. -/
theorem hat_energy {F : (Fin d → ℝ) → ℝ} (h : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (k : ℕ) :
    Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2) ∧
    ∫ ξ : EuclideanSpace ℝ (Fin d), wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2
      = (∫ y, F y ^ 2) + ∑ i, ∫ y, iterD (List.replicate k i) F y ^ 2 := by
  have hi : ∀ i, Integrable (fun ξ : EuclideanSpace ℝ (Fin d) =>
      (2 * Real.pi * ξ i) ^ (2 * k) * ‖𝓕 (lft F) ξ‖ ^ 2) := by
    intro i
    have := integrable_sq_hat (contDiff_iterD (List.replicate k i) h)
      (hasCompactSupport_iterD (List.replicate k i) hc)
    exact this.congr (Eventually.of_forall fun ξ => (pow_sq_fourier_lft h hc i k ξ).symm)
  have e : (fun ξ : EuclideanSpace ℝ (Fin d) => wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2)
      = fun ξ => ‖𝓕 (lft F) ξ‖ ^ 2 + ∑ i, (2 * Real.pi * ξ i) ^ (2 * k) * ‖𝓕 (lft F) ξ‖ ^ 2 := by
    funext ξ; simp [wgt, add_mul, Finset.sum_mul]
  rw [e]
  refine ⟨(integrable_sq_hat h hc).add (integrable_finsetSum _ fun i _ => hi i), ?_⟩
  rw [integral_add (integrable_sq_hat h hc) (integrable_finsetSum _ fun i _ => hi i),
    integral_finsetSum _ fun i _ => hi i, integral_sq_fourier_lft h hc]
  simp_rw [integral_pow_sq_fourier_lft h hc]

theorem wgt_hat_lintegral_le {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0) {F : (Fin d → ℝ) → ℝ}
    (hF0 : ∀ᵐ x, x ∉ K0 → F x = 0) (hF2 : MemLp F 2) (hF1 : Integrable F) (k : ℕ)
    {G : Fin d → (Fin d → ℝ) → ℝ} (hW : ∀ i, WeakIter (List.replicate k i) F (G i))
    (hG2 : ∀ i, MemLp (G i) 2) (hG1 : ∀ i, Integrable (G i)) :
    ∫⁻ ξ : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2)
      ≤ ENNReal.ofReal ((∫ y, F y ^ 2) + ∑ i, ∫ y, G i y ^ 2) := by
  set M : ℝ := (∫ y, F y ^ 2) + ∑ i, ∫ y, G i y ^ 2 with hM
  have hsm : ∀ n, ContDiff ℝ ∞ (mol F (rho n)) := fun n =>
    contDiff_mol hF1.locallyIntegrable (contDiff_rho n) (hasCompactSupport_rho n)
  have hcs : ∀ n, HasCompactSupport (mol F (rho n)) := hasCompactSupport_mol hK0 hF0
  set Φ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n ξ => wgt d k ξ * ‖𝓕 (lft (mol F (rho n))) ξ‖ ^ 2 with hΦ
  have hbound : ∀ n, Integrable (Φ n) ∧ ∫ ξ, Φ n ξ ≤ M := by
    intro n
    obtain ⟨hi, he⟩ := hat_energy (hsm n) (hcs n) k
    refine ⟨hi, ?_⟩
    show ∫ ξ, wgt d k ξ * ‖𝓕 (lft (mol F (rho n))) ξ‖ ^ 2 ≤ M
    rw [he]
    have hit : ∀ i, iterD (List.replicate k i) (mol F (rho n)) = mol (G i) (rho n) := fun i =>
      iterD_mol (contDiff_rho n) (hasCompactSupport_rho n) _ (hW i)
    simp_rw [hit]
    exact add_le_add (integral_sq_mol_le hF2 hF1 n)
      (Finset.sum_le_sum fun i _ => integral_sq_mol_le (hG2 i) (hG1 i) n)
  have hlint : ∀ n, ∫⁻ ξ, ENNReal.ofReal (Φ n ξ) ≤ ENNReal.ofReal M := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hbound n).1
      (Eventually.of_forall fun ξ => mul_nonneg (wgt_pos k ξ).le (sq_nonneg _))]
    exact ENNReal.ofReal_le_ofReal (hbound n).2
  have hlim : ∀ ξ, Tendsto (fun n => ENNReal.ofReal (Φ n ξ)) atTop
      (𝓝 (ENNReal.ofReal (wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2))) := by
    intro ξ
    refine (ENNReal.tendsto_ofReal ?_)
    exact (((continuous_const.mul (continuous_norm.pow 2)).tendsto _).comp (tendsto_hat_mol hF1 ξ))
  calc ∫⁻ ξ, ENNReal.ofReal (wgt d k ξ * ‖𝓕 (lft F) ξ‖ ^ 2)
      = ∫⁻ ξ, liminf (fun n => ENNReal.ofReal (Φ n ξ)) atTop := by
        refine lintegral_congr fun ξ => ?_
        exact ((hlim ξ).liminf_eq).symm
    _ ≤ liminf (fun n => ∫⁻ ξ, ENNReal.ofReal (Φ n ξ)) atTop :=
        lintegral_liminf_le' fun n => (hbound n).1.aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal M := by
        refine liminf_le_of_frequently_le' (Eventually.of_forall hlint).frequently

end MarkovTriple.BGL.Instances.GibbsRd.Sob
