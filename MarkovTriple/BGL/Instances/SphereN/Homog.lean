import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Smooth

/-!
# Homogeneity and the Euler relation (Round 28, stream L)
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

/-- positive homogeneity of degree `k` off the origin. -/
def Hom (k : ℤ) (F : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ y : Fin n → ℝ, y ≠ 0 → F (t • y) = t ^ k * F y

lemma hom_ext (f : Sph n → ℝ) : Hom 0 (ext f) := by
  intro t ht y _
  simp [ext_smul f ht y]

lemma hom_dd {k : ℤ} {F : (Fin n → ℝ) → ℝ} (hF : SmO F) (h : Hom k F) (i : Fin n) :
    Hom (k - 1) (dd i F) := by
  intro t ht y hy
  have hty : t • y ≠ 0 := smul_ne_zero ht.ne' hy
  have hd1 : HasFDerivAt F (fderiv ℝ F (t • y)) (t • y) := (hF.differentiableAt hty).hasFDerivAt
  have hd2 : HasFDerivAt (fun z : Fin n → ℝ => t • z) (t • ContinuousLinearMap.id ℝ (Fin n → ℝ)) y :=
    (hasFDerivAt_id y).const_smul t
  have hc := HasFDerivAt.comp y hd1 hd2
  have hr : HasFDerivAt (fun z => t ^ k * F z) (t ^ k • fderiv ℝ F y) y :=
    ((hF.differentiableAt hy).hasFDerivAt).const_mul (t ^ k)
  have ev : (F ∘ fun z : Fin n → ℝ => t • z) =ᶠ[𝓝 y] fun z => t ^ k * F z := by
    filter_upwards [isOpen_ne0.mem_nhds hy] with z hz
    exact h t ht z hz
  have heq := congrArg (fun L => L (Pi.single i 1)) (hc.fderiv.symm.trans (ev.fderiv_eq.trans hr.fderiv))
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply] at heq
  have h3 : fderiv ℝ F (t • y) (t • Pi.single i 1) = t * dd i F (t • y) := by
    rw [map_smul]; rfl
  show dd i F (t • y) = t ^ (k - 1) * dd i F y
  have h4 : t * dd i F (t • y) = t ^ k * dd i F y := by
    rw [← h3]; exact (by simpa [dd] using heq.symm.symm)
  rw [zpow_sub_one₀ ht.ne']
  field_simp
  linarith

lemma euler {k : ℤ} {F : (Fin n → ℝ) → ℝ} (hF : SmO F) (h : Hom k F) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ∑ i, y i * dd i F y = k * F y := by
  have hd1 : HasFDerivAt F (fderiv ℝ F y) ((1 : ℝ) • y) := by
    rw [one_smul]; exact (hF.differentiableAt hy).hasFDerivAt
  have hg : HasDerivAt (fun s : ℝ => s • y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const y
  have hc : HasDerivAt (fun s : ℝ => F (s • y)) (fderiv ℝ F y y) 1 := by
    have := hd1.comp_hasDerivAt (1 : ℝ) hg
    exact this
  have hz : HasDerivAt (fun s : ℝ => s ^ k * F y) ((k : ℝ) * (1 : ℝ) ^ (k - 1) * F y) 1 := by
    have := hasDerivAt_zpow k (1 : ℝ) (Or.inl one_ne_zero)
    exact this.mul_const (F y)
  have ev : (fun s : ℝ => F (s • y)) =ᶠ[𝓝 1] fun s => s ^ k * F y := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with s hs using h s hs y hy
  have := hc.unique (hz.congr_of_eventuallyEq ev)
  have hy' : y = ∑ i, y i • (Pi.single i (1 : ℝ) : Fin n → ℝ) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  have h5 : fderiv ℝ F y y = ∑ i, y i * dd i F y := by
    have h6 : fderiv ℝ F y y = fderiv ℝ F y (∑ i, y i • (Pi.single i (1 : ℝ) : Fin n → ℝ)) :=
      congrArg _ hy'
    rw [h6, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]; rfl
  rw [← h5, this]
  simp

end MarkovTriple.BGL.SphereN
