import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAPI
import MarkovTriple.BGL.Instances.Lebesgue.Heat

/-!
# Gaussian integration by parts on `ℝ^d` (Round 24, stream A, part H-b)

`E[z_i g(z)] = E[∂_i g(z)]` for `z ~ gam d`, `g` `C¹` with `g`, `∂_i g` bounded.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

lemma integral_gam_split {n : ℕ} (i : Fin (n + 1)) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : Integrable F (gam (n + 1))) :
    ∫ z, F z ∂(gam (n + 1)) =
      ∫ w, ∫ t, F (Fin.insertNth i t w) ∂(gaussianReal 0 1)
        ∂(Measure.pi fun _ : Fin n => gaussianReal 0 1) := by
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) i
  have mps := mp.symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i)
  have h1 : ∫ z, F z ∂(gam (n + 1)) =
      ∫ p, F ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm p)
        ∂((gaussianReal 0 1).prod (Measure.pi fun _ : Fin n => gaussianReal 0 1)) := by
    rw [← mp.integral_comp' (g := fun p => F ((MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) i).symm p))]
    simp [Fin.insertNthEquiv]
    rfl
  rw [h1, integral_prod_symm]
  · rfl
  · exact (mps.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF

lemma gam_ibp (i : Fin d) {g : (Fin d → ℝ) → ℝ} (hg : ContDiff ℝ 1 g) {B B' : ℝ}
    (hB : ∀ z, |g z| ≤ B) (hB' : ∀ z, |fderiv ℝ g z (Pi.single i 1)| ≤ B') :
    ∫ z, z i * g z ∂(gam d) = ∫ z, fderiv ℝ g z (Pi.single i 1) ∂(gam d) := by
  cases d with
  | zero => exact i.elim0
  | succ n =>
    have hgc : Continuous g := hg.continuous
    have hg'c : Continuous (fun z => fderiv ℝ g z (Pi.single i 1)) :=
      (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    have I1 : Integrable (fun z : Fin (n + 1) → ℝ => z i * g z) (gam (n + 1)) := by
      have hid : Integrable (fun z : Fin (n + 1) → ℝ => z i) (gam (n + 1)) :=
        ((measurePreserving_eval (fun _ : Fin (n + 1) => gaussianReal 0 1) i).integrable_comp
          (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable).2 MarkovTriple.BGL.Lebesgue.integrable_id_gauss
      exact hid.mul_bdd hgc.aestronglyMeasurable (c := B) (ae_of_all _ fun z => by simpa using hB z)
    have I2 : Integrable (fun z => fderiv ℝ g z (Pi.single i 1)) (gam (n + 1)) :=
      Integrable.of_bound (C := B') hg'c.aestronglyMeasurable
        (ae_of_all _ fun z => by simpa using hB' z)
    rw [integral_gam_split i I1, integral_gam_split i I2]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [Fin.insertNth_apply_same]
    have hl : ∀ t : ℝ, Fin.insertNth i t w = Fin.insertNth i 0 w + t • (Pi.single i 1 : Fin (n + 1) → ℝ) := by
      intro t
      ext j
      refine Fin.succAboveCases i ?_ ?_ j
      · simp only [Fin.insertNth_apply_same, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same]
        simp
      · intro k
        simp [Fin.succAbove_ne]
    obtain ⟨c, hc⟩ : ∃ c : Fin (n + 1) → ℝ, ∀ t : ℝ,
        Fin.insertNth i t w = c + t • (Pi.single i 1 : Fin (n + 1) → ℝ) := ⟨_, hl⟩
    simp only [hc]
    refine MarkovTriple.BGL.Lebesgue.gauss_ibp (g := fun t : ℝ => g (c + t • (Pi.single i 1 : Fin (n + 1) → ℝ)))
      (g' := fun t => fderiv ℝ g (c + t • (Pi.single i 1 : Fin (n + 1) → ℝ))
        (Pi.single i 1)) (fun t => ?_) ?_ ?_ (B := B) (B' := B') (fun t => hB _) (fun t => hB' _)
    · have h1 : HasDerivAt (fun t : ℝ => c + t • (Pi.single i 1 : Fin (n + 1) → ℝ))
          (Pi.single i 1) t := by
        simpa using ((hasDerivAt_id t).smul_const (Pi.single i 1 : Fin (n + 1) → ℝ)).const_add c
      exact (((hg.differentiable (by simp)) _).hasFDerivAt).comp_hasDerivAt t h1
    · exact hgc.comp (by fun_prop)
    · exact hg'c.comp (by fun_prop)

end MarkovTriple.BGL.LebesgueRd
