import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDerivAux3

/-!
# The Gaussian mean of the remainder (Round 24, stream A, part H-b)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ : (Fin d → ℝ) → ℝ}

lemma exists_bound {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : ∃ C, 0 ≤ C ∧ ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (smooth hf).continuous.bounded_above_of_compact_support (cs hf)
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

lemma integrable_comp_gam_A0 {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) (a : ℝ) (x : Fin d → ℝ) :
    Integrable (fun z => f (x - a • z)) (gam d) := by
  obtain ⟨C, -, hC⟩ := exists_bound hf
  exact Integrable.of_bound (C := C) ((smooth hf).continuous.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa using hC _)

lemma fderiv_eq_sum (f : (Fin d → ℝ) → ℝ) (y z : Fin d → ℝ) :
    fderiv ℝ f y z = ∑ i, z i * dd i f y := by
  have : z = ∑ i, z i • (Pi.single i 1 : Fin d → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [this]
  simp [map_sum, dd]

lemma gam_ibp_dd (hφ : φ ∈ A₀ d) (a : ℝ) (x : Fin d → ℝ) (i : Fin d) :
    ∫ z, z i * dd i φ (x - a • z) ∂(gam d) = ∫ z, (-a) * dd i (dd i φ) (x - a • z) ∂(gam d) := by
  obtain ⟨B, -, hB⟩ := exists_bound (dd_mem hφ i)
  obtain ⟨B', -, hB'⟩ := exists_bound (dd_mem (dd_mem hφ i) i)
  have hder : ∀ z, HasFDerivAt (fun z : Fin d → ℝ => dd i φ (x - a • z))
      ((fderiv ℝ (dd i φ) (x - a • z)).comp (-(a • ContinuousLinearMap.id ℝ (Fin d → ℝ)))) z := fun z => by
    have h1 : HasFDerivAt (fun z : Fin d → ℝ => x - a • z) (-(a • ContinuousLinearMap.id ℝ (Fin d → ℝ))) z :=
      ((hasFDerivAt_id z).const_smul a).const_sub x
    exact (hasFDerivAt_of (smooth (dd_mem hφ i)) (x - a • z)).comp z h1
  have hcomp : ∀ z, fderiv ℝ (fun z : Fin d → ℝ => dd i φ (x - a • z)) z (Pi.single i 1) =
      (-a) * dd i (dd i φ) (x - a • z) := fun z => by
    rw [(hder z).fderiv]
    simp [dd]
  have hg : ContDiff ℝ 1 (fun z : Fin d → ℝ => dd i φ (x - a • z)) :=
    (((smooth (dd_mem hφ i))).comp (by fun_prop : ContDiff ℝ (⊤ : ℕ∞) fun z : Fin d → ℝ => x - a • z)).of_le
      (by simp)
  rw [gam_ibp i hg (B := B) (B' := |a| * B') (fun z => hB _) (fun z => by
    rw [hcomp z, abs_mul, abs_neg]
    exact mul_le_mul_of_nonneg_left (hB' _) (abs_nonneg _))]
  exact integral_congr_ae (ae_of_all _ fun z => hcomp z)

lemma integral_rhoD (hφ : φ ∈ A₀ d) (a : ℝ) {h : ℝ} (x : Fin d → ℝ) :
    ∫ z, rhoD φ a h x z ∂(gam d) =
      (heatRd (a + h) φ x - heatRd a φ x) / h - a * heatRd a (Lf φ) x := by
  have i1 := integrable_comp_gam_A0 hφ (a + h) x
  have i2 := integrable_comp_gam_A0 hφ a x
  have hi : ∀ i : Fin d, Integrable (fun z : Fin d → ℝ => z i * dd i φ (x - a • z)) (gam d) := fun i => by
    obtain ⟨B, -, hB⟩ := exists_bound (dd_mem hφ i)
    have hid : Integrable (fun z : Fin d → ℝ => z i) (gam d) :=
      ((measurePreserving_eval (fun _ : Fin d => gaussianReal 0 1) i).integrable_comp
        (g := fun x : ℝ => x) measurable_id.aestronglyMeasurable).2
        MarkovTriple.BGL.Lebesgue.integrable_id_gauss
    exact hid.mul_bdd ((smooth (dd_mem hφ i)).continuous.comp (by fun_prop)).aestronglyMeasurable
      (c := B) (ae_of_all _ fun z => by simpa using hB _)
  have i3 : Integrable (fun z => fderiv ℝ φ (x - a • z) z) (gam d) := by
    simp_rw [fderiv_eq_sum]
    exact integrable_finsetSum _ fun i _ => hi i
  have e1 : Integrable (fun z => (φ (x - (a + h) • z) - φ (x - a • z)) / h) (gam d) :=
    (i1.sub i2).div_const h
  have hL : ∫ z, Lf φ (x - a • z) ∂(gam d) = ∑ i, ∫ z, dd i (dd i φ) (x - a • z) ∂(gam d) := by
    unfold Lf
    exact integral_finsetSum _ fun i _ => integrable_comp_gam_A0 (dd_mem (dd_mem hφ i) i) a x
  have hS : ∫ z, fderiv ℝ φ (x - a • z) z ∂(gam d) = -a * ∫ z, Lf φ (x - a • z) ∂(gam d) := by
    simp_rw [fderiv_eq_sum]
    rw [integral_finsetSum _ fun i _ => hi i, hL, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gam_ibp_dd hφ a x i, integral_const_mul]
  unfold rhoD
  rw [integral_add e1 i3, integral_div, integral_sub i1 i2, hS]
  unfold heatRd
  ring

end MarkovTriple.BGL.LebesgueRd
