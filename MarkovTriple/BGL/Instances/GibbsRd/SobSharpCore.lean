import MarkovTriple.BGL.Instances.GibbsRd.SobSharpWgt
import MarkovTriple.BGL.Instances.GibbsRd.SobSharpWeak
import MarkovTriple.BGL.Instances.GibbsRd.SobMain

/-!
# Sharp `C^m` representative for compactly supported `F` with `HasSobL2 k F`, `d + 2m < 2k` (R17 SobSharp)

`g = 𝓕⁻ (𝓕 F)` is `C^m` because `(1+|ξ|)^m 𝓕F ∈ L¹` (`integrable_weighted_hat`), and `F = g` a.e. since
`F ⋆ ρ_n = 𝓕⁻ (𝓕 (F ⋆ ρ_n)) → 𝓕⁻ (𝓕 F)` (dominated convergence, `|𝓕(F ⋆ ρ_n)| ≤ |𝓕 F|`) while `F ⋆ ρ_n → F` a.e.
-/

open MeasureTheory Filter Topology
open scoped ContDiff FourierTransform

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem contDiff_fourierInv_of_integrable (m : ℕ) {H : EuclideanSpace ℝ (Fin d) → ℂ} (hHc : Continuous H)
    (hH : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖) ^ m * ‖H ξ‖)) :
    ContDiff ℝ (m : WithTop ℕ∞) (𝓕⁻ H) := by
  rw [Real.fourierInv_eq_fourier_comp_neg]
  have h1 : Integrable (fun ξ : EuclideanSpace ℝ (Fin d) => (1 + ‖ξ‖) ^ m * ‖H (-ξ)‖) := by
    have := hH.comp_neg
    simpa using this
  have := Real.contDiff_fourier (N := (m : ℕ∞)) (f := fun x : EuclideanSpace ℝ (Fin d) => H (-x)) (by
    intro n hn
    have hn' : n ≤ m := by exact_mod_cast hn
    refine h1.mono' ?_ (Eventually.of_forall fun v => ?_)
    · exact ((continuous_norm.pow n).mul (hHc.comp continuous_neg).norm).aestronglyMeasurable
    · have h0 : 0 ≤ ‖v‖ ^ n * ‖H (-v)‖ := by positivity
      rw [Real.norm_of_nonneg h0]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      calc ‖v‖ ^ n ≤ (1 + ‖v‖) ^ n := pow_le_pow_left₀ (norm_nonneg _) (by linarith) _
        _ ≤ (1 + ‖v‖) ^ m := pow_le_pow_right₀ (by linarith [norm_nonneg v]) hn')
  exact_mod_cast this

theorem ae_eq_fourierInv_hat {F : (Fin d → ℝ) → ℝ} (hF1 : Integrable F) (hI : Integrable (𝓕 (lft F))) :
    ∀ᵐ y : Fin d → ℝ, ((F y : ℝ) : ℂ) = 𝓕⁻ (𝓕 (lft F)) (WithLp.toLp 2 y) := by
  have hsm : ∀ n, ContDiff ℝ ∞ (mol F (rho n)) := fun n =>
    contDiff_mol hF1.locallyIntegrable (contDiff_rho n) (hasCompactSupport_rho n)
  have hdom : ∀ n, Integrable (𝓕 (lft (mol F (rho n)))) := by
    intro n
    refine hI.norm.mono' (continuous_hat (integrable_mol hF1 n)).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    simpa using norm_hat_mol_le hF1 n ξ
  have hinv : ∀ n, 𝓕⁻ (𝓕 (lft (mol F (rho n)))) = lft (mol F (rho n)) := fun n =>
    Continuous.fourierInv_fourier_eq (lft_contDiff (hsm n)).continuous
      (integrable_lft (integrable_mol hF1 n)) (hdom n)
  have key : ∀ x : EuclideanSpace ℝ (Fin d),
      Tendsto (fun n => lft (mol F (rho n)) x) atTop (𝓝 (𝓕⁻ (𝓕 (lft F)) x)) := by
    intro x
    have e : (fun n => lft (mol F (rho n)) x) = fun n => 𝓕⁻ (𝓕 (lft (mol F (rho n)))) x := by
      funext n; rw [hinv]
    rw [e]
    simp only [Real.fourierInv_eq]
    refine tendsto_integral_of_dominated_convergence (fun v => ‖𝓕 (lft F) v‖) ?_ hI.norm ?_ ?_
    · intro n
      exact ((Real.continuous_fourierChar.comp (by fun_prop : Continuous fun v : EuclideanSpace ℝ (Fin d) =>
          inner ℝ v x)).smul (continuous_hat (integrable_mol hF1 n))).aestronglyMeasurable
    · intro n
      refine Eventually.of_forall fun v => ?_
      simpa [norm_smul] using norm_hat_mol_le hF1 n v
    · refine Eventually.of_forall fun v => ?_
      exact ((continuous_const.smul continuous_id).tendsto _).comp (tendsto_hat_mol hF1 v)
  have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin d), ((F (WithLp.ofLp x) : ℝ) : ℂ) = 𝓕⁻ (𝓕 (lft F)) x := by
    have h1 := ae_tendsto_mol hF1.locallyIntegrable
    have h2 := (PiLp.volume_preserving_ofLp (Fin d)).quasiMeasurePreserving.ae h1
    filter_upwards [h2] with x hx
    have hx' : Tendsto (fun n => lft (mol F (rho n)) x) atTop (𝓝 ((F (WithLp.ofLp x) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp hx
    exact tendsto_nhds_unique hx' (key x)
  exact (PiLp.volume_preserving_toLp (Fin d)).quasiMeasurePreserving.ae hae

/-- **Sharp core**: compactly supported `F` with iterated weak derivatives of order `≤ k` in `L²_loc`,
`d + 2m < 2k` (i.e. `k > m + d/2`), has a `C^m` representative. -/
theorem sob_core_sharp {K0 : Set (Fin d → ℝ)} (hK0 : IsCompact K0) {F : (Fin d → ℝ) → ℝ}
    (hF0 : ∀ᵐ x, x ∉ K0 → F x = 0) (m k : ℕ) (hk : d + 2 * m < 2 * k) (hF : HasSobL2 k F) :
    ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ (m : WithTop ℕ∞) g ∧ F =ᵐ[volume] g := by
  have hF2 : MemLp F 2 := memLp_of_locL2 hK0 (HasSobL2.locL2 k hF) hF0
  have hF1 : Integrable F := integrable_of_locL2 hK0 (HasSobL2.locL2 k hF) hF0
  have hex : ∀ i : Fin d, ∃ G, WeakIter (List.replicate k i) F G ∧ LocL2 G := fun i => by
    obtain ⟨G, hW, hG⟩ := exists_weakIter_L2 (List.replicate k i) k (by simp) hF
    refine ⟨G, hW, ?_⟩
    have : k - (List.replicate k i).length = 0 := by simp
    rw [this] at hG
    exact hG
  choose G hW hGL using hex
  have hG0 : ∀ i, ∀ᵐ x, x ∉ K0 → G i x = 0 := fun i => by
    have := WeakIter.ae_zero_of_open (List.replicate k i) (hW i) hK0.isClosed.isOpen_compl
      (by filter_upwards [hF0] with x hx h using hx h)
    filter_upwards [this] with x hx h using hx h
  have hG2 : ∀ i, MemLp (G i) 2 := fun i => memLp_of_locL2 hK0 (hGL i) (hG0 i)
  have hG1 : ∀ i, Integrable (G i) := fun i => integrable_of_locL2 hK0 (hGL i) (hG0 i)
  have hint := integrable_wgt_hat hK0 hF0 hF2 hF1 k hW hG2 hG1
  have hweighted := integrable_weighted_hat hF1 m k hk hint
  have hI : Integrable (𝓕 (lft F)) := by
    have h0 := integrable_weighted_hat hF1 0 k (by omega) hint
    simp only [pow_zero, one_mul] at h0
    exact (integrable_norm_iff (continuous_hat hF1).aestronglyMeasurable).1 h0
  set gE : EuclideanSpace ℝ (Fin d) → ℂ := 𝓕⁻ (𝓕 (lft F)) with hgE
  have hgc : ContDiff ℝ (m : WithTop ℕ∞) gE :=
    contDiff_fourierInv_of_integrable m (continuous_hat hF1) hweighted
  refine ⟨fun y => (gE ((eqv d).symm y)).re, ?_, ?_⟩
  · exact Complex.reCLM.contDiff.comp (hgc.comp (eqv d).symm.contDiff)
  · filter_upwards [ae_eq_fourierInv_hat hF1 hI] with y hy
    have := congrArg Complex.re hy
    simpa using this

end MarkovTriple.BGL.Instances.GibbsRd.Sob
