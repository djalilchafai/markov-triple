import MarkovTriple.BGL.Instances.GibbsRd.SobMollify

/-!
# `L¹` convergence of mollifications (R16 Sob)

`G ∈ L¹(ℝ^d) ⇒ ‖G ⋆ ρ_n − G‖_{L¹} → 0`.  Proof: Lebesgue differentiation (Mathlib:
`ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable`) gives a.e. convergence; for `G ≥ 0`
Scheffé's lemma (proved here by dominated convergence applied to `min(G⋆ρ_n, G)`, using `∫ G⋆ρ_n = ∫ G`)
upgrades it to `L¹`; the general case splits `G = G⁺ − G⁻`.  (Evans App. C Thm 7 (iii), via a different route.)
-/

open MeasureTheory Filter Topology
open scoped ContDiff Convolution

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem integrable_mol_integrand {f ρ : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (x : Fin d → ℝ) :
    Integrable (fun t => f t * ρ (x - t)) :=
  integrable_mul_test hf (hρ.continuous.comp (continuous_const.sub continuous_id))
    (hρc.comp_homeomorph (Homeomorph.subLeft x))

theorem mol_sub {f₁ f₂ ρ : (Fin d → ℝ) → ℝ} (h₁ : LocallyIntegrable f₁) (h₂ : LocallyIntegrable f₂)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    mol (fun x => f₁ x - f₂ x) ρ = fun x => mol f₁ ρ x - mol f₂ ρ x := by
  funext x
  simp only [mol, sub_mul]
  exact integral_sub (integrable_mol_integrand h₁ hρ hρc x) (integrable_mol_integrand h₂ hρ hρc x)

theorem integrable_mol {f : (Fin d → ℝ) → ℝ} (hf : Integrable f) (n : ℕ) :
    Integrable (mol f (rho n)) := by
  rw [mol_eq_conv]
  exact hf.integrable_convolution _ (integrable_rho n)

theorem integral_mol {f : (Fin d → ℝ) → ℝ} (hf : Integrable f) (n : ℕ) :
    ∫ x, mol f (rho n) x = ∫ x, f x := by
  rw [mol_eq_conv, integral_convolution _ hf (integrable_rho n), integral_rho]
  simp

theorem ae_tendsto_mol {f : (Fin d → ℝ) → ℝ} (hf : LocallyIntegrable f) :
    ∀ᵐ x, Tendsto (fun n => mol f (rho n) x) atTop (𝓝 (f x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
    (φ := fun n : ℕ => (bump n : ContDiffBump (0 : Fin d → ℝ))) (l := atTop) (K := 2)
    (by
      show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
      exact tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    (Eventually.of_forall fun n => by
      show 1 / ((n : ℝ) + 1) ≤ 2 * (1 / (2 * ((n : ℝ) + 1)))
      apply le_of_eq; field_simp)
    hf
  filter_upwards [h] with x hx
  refine hx.congr (fun n => ?_)
  simp only [mol, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, rho]
  rw [← integral_sub_left_eq_self (fun t => f t * (bump n).normed volume (x - t)) volume x]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [sub_sub_cancel]
  ring

/-- Scheffé's lemma (version needed). -/
theorem tendsto_integral_abs_sub_of_scheffe {a : ℕ → (Fin d → ℝ) → ℝ} {b : (Fin d → ℝ) → ℝ}
    (ha : ∀ n, Integrable (a n)) (hb : Integrable b) (ha0 : ∀ n x, 0 ≤ a n x) (hb0 : ∀ x, 0 ≤ b x)
    (hae : ∀ᵐ x, Tendsto (fun n => a n x) atTop (𝓝 (b x)))
    (hint : ∀ n, ∫ x, a n x = ∫ x, b x) :
    Tendsto (fun n => ∫ x, |a n x - b x|) atTop (𝓝 0) := by
  have hmin : Tendsto (fun n => ∫ x, min (a n x) (b x)) atTop (𝓝 (∫ x, b x)) := by
    refine tendsto_integral_of_dominated_convergence b (fun n => ?_) hb (fun n => ?_) ?_
    · exact continuous_min.comp_aestronglyMeasurable₂ (ha n).1 hb.1
    · exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (le_min (ha0 n x) (hb0 x))]
        exact min_le_right _ _
    · filter_upwards [hae] with x hx
      simpa using hx.min (tendsto_const_nhds (x := b x))
  have key : ∀ n, ∫ x, |a n x - b x| = (∫ x, a n x) + (∫ x, b x) - 2 * (∫ x, min (a n x) (b x)) := by
    intro n
    have h1 : (fun x => |a n x - b x|) = fun x => (a n x + b x) - 2 * min (a n x) (b x) := by
      funext x
      rcases le_total (a n x) (b x) with h | h
      · rw [min_eq_left h, abs_of_nonpos (by linarith)]; ring
      · rw [min_eq_right h, abs_of_nonneg (by linarith)]; ring
    have hm : Integrable (fun x => min (a n x) (b x)) :=
      hb.mono' (continuous_min.comp_aestronglyMeasurable₂ (ha n).1 hb.1)
        (Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (le_min (ha0 n x) (hb0 x))]
          exact min_le_right _ _)
    rw [h1]
    rw [integral_sub (f := fun x => a n x + b x) (g := fun x => 2 * min (a n x) (b x))
      ((ha n).add hb) (hm.const_mul 2)]
    rw [integral_add (ha n) hb, integral_const_mul]
  simp_rw [key, hint]
  have := (tendsto_const_nhds (x := ∫ x, b x) |>.add (tendsto_const_nhds (x := ∫ x, b x))).sub
    (hmin.const_mul 2)
  convert this using 2
  ring

theorem tendsto_integral_abs_mol_nonneg {G : (Fin d → ℝ) → ℝ} (hG : Integrable G) (hG0 : ∀ x, 0 ≤ G x) :
    Tendsto (fun n => ∫ x, |mol G (rho n) x - G x|) atTop (𝓝 0) := by
  refine tendsto_integral_abs_sub_of_scheffe (fun n => integrable_mol hG n) hG
    (fun n x => ?_) hG0 (ae_tendsto_mol hG.locallyIntegrable) (fun n => integral_mol hG n)
  exact integral_nonneg fun t => mul_nonneg (hG0 t) (rho_nonneg n _)

/-- `L¹` convergence of the mollifications of an integrable function. -/
theorem tendsto_integral_abs_mol_sub {G : (Fin d → ℝ) → ℝ} (hG : Integrable G) :
    Tendsto (fun n => ∫ x, |mol G (rho n) x - G x|) atTop (𝓝 0) := by
  have hp : Integrable (fun x => max (G x) 0) := hG.pos_part
  have hm : Integrable (fun x => max (-G x) 0) := hG.neg_part
  have h1 := tendsto_integral_abs_mol_nonneg hp (fun x => le_max_right _ _)
  have h2 := tendsto_integral_abs_mol_nonneg hm (fun x => le_max_right _ _)
  have hGeq : G = fun x => max (G x) 0 - max (-G x) 0 := by
    funext x; exact (max_zero_sub_max_neg_zero_eq_self (G x)).symm
  have hmol : ∀ n, mol G (rho n) = fun x => mol (fun x => max (G x) 0) (rho n) x
      - mol (fun x => max (-G x) 0) (rho n) x := fun n => by
    conv_lhs => rw [hGeq]
    exact mol_sub hp.locallyIntegrable hm.locallyIntegrable (contDiff_rho n) (hasCompactSupport_rho n)
  refine squeeze_zero (fun n => integral_nonneg fun x => abs_nonneg _) (fun n => ?_) (by simpa using h1.add h2)
  have i1 : Integrable (fun x => |mol (fun x => max (G x) 0) (rho n) x - max (G x) 0|) :=
    ((integrable_mol hp n).sub hp).abs
  have i2 : Integrable (fun x => |mol (fun x => max (-G x) 0) (rho n) x - max (-G x) 0|) :=
    ((integrable_mol hm n).sub hm).abs
  rw [← integral_add i1 i2]
  refine integral_mono (((integrable_mol hG n).sub hG).abs) (i1.add i2) fun x => ?_
  simp only [hmol n]
  have : G x = max (G x) 0 - max (-G x) 0 := (max_zero_sub_max_neg_zero_eq_self (G x)).symm
  conv_lhs => rw [this]
  set A := mol (fun x => max (G x) 0) (rho n) x
  set B := mol (fun x => max (-G x) 0) (rho n) x
  calc |A - B - (max (G x) 0 - max (-G x) 0)|
      = |(A - max (G x) 0) - (B - max (-G x) 0)| := by ring_nf
    _ ≤ _ := abs_sub _ _

end MarkovTriple.BGL.Instances.GibbsRd.Sob
