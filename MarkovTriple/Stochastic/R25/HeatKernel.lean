import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAux

/-!
# Round 25 (E), part 1: the explicit heat kernel `κ_t(x, ·) = N(x, 2t I_d)` on `ℝ^d`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R25

open MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

/-- **The heat kernel on `ℝ^d`**: `κ_t(x, ·) = N(x, 2t I_d)`, as the image of `N(0, I_d)` under `z ↦ x + √(2t) z`. -/
noncomputable def heatKernelRd (d : ℕ) (t : ℝ≥0) : Kernel (Fin d → ℝ) (Fin d → ℝ) where
  toFun x := (gam d).map (fun z => x + Real.sqrt (2 * t) • z)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
    have h : ∀ x : Fin d → ℝ, ((gam d).map (fun z => x + Real.sqrt (2 * t) • z)) s
        = gam d {z | x + Real.sqrt (2 * t) • z ∈ s} := fun x => by
      rw [Measure.map_apply (by fun_prop) hs]; rfl
    simp_rw [h]
    exact measurable_measure_prodMk_left (ν := gam d)
      (s := {p : (Fin d → ℝ) × (Fin d → ℝ) | p.1 + Real.sqrt (2 * t) • p.2 ∈ s})
      (hs.preimage (by fun_prop))

lemma heatKernelRd_apply (t : ℝ≥0) (x : Fin d → ℝ) :
    heatKernelRd d t x = (gam d).map (fun z => x + Real.sqrt (2 * t) • z) := rfl

instance (t : ℝ≥0) (x : Fin d → ℝ) : IsProbabilityMeasure (heatKernelRd d t x) := by
  rw [heatKernelRd_apply]
  infer_instance

instance (t : ℝ≥0) : IsMarkovKernel (heatKernelRd d t) := ⟨fun _ => inferInstance⟩

theorem integral_heatKernelRd (t : ℝ≥0) (x : Fin d → ℝ) (g : (Fin d → ℝ) → ℝ) (hg : Continuous g) :
    ∫ y, g y ∂(heatKernelRd d t x) = heatRd (Real.sqrt (2 * t)) g x := by
  rw [heatKernelRd_apply, integral_map (by fun_prop) hg.aestronglyMeasurable]
  unfold heatRd
  rw [← integral_gam_neg (fun z => g (x - Real.sqrt (2 * t) • z))]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp [sub_eq_add_neg]

/-- **`κ_t(x, ·) = N(x, 2t I_d)`** as a product of one-dimensional Gaussians of variance `2t`. -/
theorem heatKernelRd_apply_pi (t : ℝ≥0) (x : Fin d → ℝ) :
    heatKernelRd d t x = Measure.pi (fun i => gaussianReal (x i) (2 * t)) := by
  rw [heatKernelRd_apply]
  have h1 : (fun z : Fin d → ℝ => x + Real.sqrt (2 * t) • z)
      = fun z i => (fun (i : Fin d) (w : ℝ) => x i + Real.sqrt (2 * t) * w) i (z i) := by
    funext z i; simp
  have h0 := Measure.pi_map_pi (μ := fun _ : Fin d => gaussianReal 0 1)
    (f := fun (i : Fin d) (w : ℝ) => x i + Real.sqrt (2 * t) * w) (fun i => by fun_prop)
  rw [h1, gam, h0]
  congr 1
  funext i
  have h2 : (fun w : ℝ => x i + Real.sqrt (2 * t) * w)
      = (fun w => w + x i) ∘ (fun w => Real.sqrt (2 * t) * w) := by
    funext w; simp [add_comm]
  rw [h2, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_const_mul,
    gaussianReal_map_add_const]
  congr 1
  · simp [add_comm]
  · rw [mul_one]
    ext
    show Real.sqrt (2 * t) ^ 2 = 2 * t
    exact Real.sq_sqrt (by positivity)

end MarkovTriple.Stochastic.R25
