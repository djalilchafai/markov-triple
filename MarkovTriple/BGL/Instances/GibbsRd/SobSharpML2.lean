import MarkovTriple.BGL.Instances.GibbsRd.SobConv

/-!
# Mollification is an `L²` contraction (R17 SobSharp)

For `G ∈ L²(ℝ^d)`, `‖G ⋆ ρ_n‖₂ ≤ ‖G‖₂`: Cauchy–Schwarz for the probability density `ρ_n(x - ·)` gives
`(G ⋆ ρ_n)(x)² ≤ (G² ⋆ ρ_n)(x)`, and `∫ G² ⋆ ρ_n = ∫ G²` (`integral_convolution`).
-/

open MeasureTheory Filter Topology
open scoped ContDiff Convolution

namespace MarkovTriple.BGL.Instances.GibbsRd.Sob

variable {d : ℕ}

theorem rho_bdd (n : ℕ) : ∃ C, ∀ y : Fin d → ℝ, ‖rho (d := d) n y‖ ≤ C := by
  obtain ⟨C, hC⟩ := (contDiff_rho (d := d) n).continuous.bounded_above_of_compact_support
    (hasCompactSupport_rho n)
  exact ⟨C, fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (rho_nonneg n y)] using hC y⟩

theorem mol_sq_le {G : (Fin d → ℝ) → ℝ} (hG : MemLp G 2) (hG1 : Integrable G) (n : ℕ) (x : Fin d → ℝ) :
    (mol G (rho n) x) ^ 2 ≤ mol (fun t => G t ^ 2) (rho n) x := by
  set u : (Fin d → ℝ) → ℝ := fun t => rho n (x - t) with hu
  have hu0 : ∀ t, 0 ≤ u t := fun t => rho_nonneg n _
  have huc : Continuous u := (contDiff_rho (d := d) n).continuous.comp (continuous_const.sub continuous_id)
  have hui : Integrable u := (integrable_rho n).comp_sub_left x
  have hu1 : ∫ t, u t = 1 := by
    simp only [hu]
    rw [integral_sub_left_eq_self (fun t => rho (d := d) n t) volume x]
    exact integral_rho n
  obtain ⟨C, hC⟩ := rho_bdd (d := d) n
  have hub : ∀ t, ‖u t‖ ≤ C := fun t => hC _
  have hGu : Integrable (fun t => G t * u t) :=
    hG1.mul_bdd huc.aestronglyMeasurable (Eventually.of_forall hub)
  have hG2 : Integrable (fun t => G t ^ 2) := hG.integrable_sq
  have hG2u : Integrable (fun t => G t ^ 2 * u t) := hG2.mul_bdd huc.aestronglyMeasurable
    (Eventually.of_forall hub)
  set c := mol G (rho n) x with hc
  have hc' : c = ∫ t, G t * u t := rfl
  have hs : mol (fun t => G t ^ 2) (rho n) x = ∫ t, G t ^ 2 * u t := rfl
  have key : 0 ≤ ∫ t, (G t - c) ^ 2 * u t :=
    integral_nonneg fun t => mul_nonneg (sq_nonneg _) (hu0 t)
  have e : ∫ t, (G t - c) ^ 2 * u t = (∫ t, G t ^ 2 * u t) - 2 * c * c + c ^ 2 := by
    have : ∀ t, (G t - c) ^ 2 * u t = G t ^ 2 * u t - (2 * c) * (G t * u t) + c ^ 2 * u t :=
      fun t => by ring
    simp_rw [this]
    have h1 : Integrable (fun t => G t ^ 2 * u t - (2 * c) * (G t * u t)) :=
      hG2u.sub (hGu.const_mul _)
    have h2 := integral_add h1 (hui.const_mul (c ^ 2))
    have h3 := integral_sub hG2u (hGu.const_mul (2 * c))
    rw [integral_const_mul] at h2 h3
    rw [h2, h3, hu1, ← hc']
    ring
  rw [hs]
  nlinarith [key, e]

theorem integral_sq_mol_le {G : (Fin d → ℝ) → ℝ} (hG : MemLp G 2) (hG1 : Integrable G) (n : ℕ) :
    ∫ x, (mol G (rho n) x) ^ 2 ≤ ∫ x, G x ^ 2 := by
  have hG2 : Integrable (fun t => G t ^ 2) := hG.integrable_sq
  have hI : Integrable (mol (fun t => G t ^ 2) (rho n)) := integrable_mol hG2 n
  have hcont : Continuous (mol G (rho n)) := by
    have := contDiff_mol hG1.locallyIntegrable (contDiff_rho n)
      (hasCompactSupport_rho n)
    exact this.continuous
  calc ∫ x, (mol G (rho n) x) ^ 2 ≤ ∫ x, mol (fun t => G t ^ 2) (rho n) x := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hI
          (Eventually.of_forall fun x => mol_sq_le hG hG1 n x)
    _ = ∫ x, G x ^ 2 := integral_mol hG2 n

end MarkovTriple.BGL.Instances.GibbsRd.Sob
