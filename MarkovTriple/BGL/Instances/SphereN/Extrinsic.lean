import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Curv2

/-!
# Extrinsic formulas for `Γ` on the sphere (Round 28, stream L, group L1)

For `F ∈ C^∞(ℝ^n)` and `f = F|_{S^{n-1}}`: `∇F̃ = ∇F − x (x·∇F)` on the sphere, whence
`Γ(f,g) = ∇F·∇G − (x·∇F)(x·∇G)` independently of the extensions.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma dd_nrm {y : Fin n → ℝ} (hy : y ≠ 0) (i : Fin n) :
    dd i (nrm : (Fin n → ℝ) → ℝ) y = y i / nrm y := by
  have hpos := nrm_pos hy
  have hs : HasFDerivAt (LebesgueRd.sq : (Fin n → ℝ) → ℝ) (fderiv ℝ LebesgueRd.sq y) y :=
    ((sq_smooth.differentiable (by simp)) y).hasFDerivAt
  have hsq : LebesgueRd.sq y ≠ 0 := by rw [← nrm_sq]; exact pow_ne_zero 2 hpos.ne'
  have hr := (Real.hasDerivAt_sqrt hsq).comp_hasFDerivAt y hs
  have e : (nrm : (Fin n → ℝ) → ℝ) = Real.sqrt ∘ LebesgueRd.sq := funext nrm_eq
  have hf : fderiv ℝ (nrm : (Fin n → ℝ) → ℝ) y =
      (1 / (2 * Real.sqrt (LebesgueRd.sq y))) • fderiv ℝ LebesgueRd.sq y := by
    rw [e]; exact hr.fderiv
  unfold dd
  rw [hf]
  simp only [smul_apply, smul_eq_mul]
  rw [show fderiv ℝ LebesgueRd.sq y (Pi.single i 1) = dd i (LebesgueRd.sq : (Fin n → ℝ) → ℝ) y from rfl,
    dd_sq, ← nrm_eq y]
  field_simp

lemma dd_inv_nrm {y : Fin n → ℝ} (hy : y ≠ 0) (i : Fin n) :
    dd i (fun z : Fin n → ℝ => (nrm z)⁻¹) y = -(nrm y ^ 2)⁻¹ * (y i / nrm y) := by
  have hpos := nrm_pos hy
  have hn : HasFDerivAt (nrm : (Fin n → ℝ) → ℝ) (fderiv ℝ nrm y) y :=
    (smO_nrm.differentiableAt hy).hasFDerivAt
  have hr := (hasDerivAt_inv hpos.ne').comp_hasFDerivAt y hn
  have e : (fun z : Fin n → ℝ => (nrm z)⁻¹) = Inv.inv ∘ nrm := rfl
  unfold dd
  rw [e, hr.fderiv]
  simp only [smul_apply, smul_eq_mul]
  rw [show fderiv ℝ nrm y (Pi.single i 1) = dd i (nrm : (Fin n → ℝ) → ℝ) y from rfl, dd_nrm hy]

lemma ext_extr {F : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} (hz : z ≠ 0) :
    ext (fun x : Sph n => F (cv (x : Ee n))) z = F (fun j => (nrm z)⁻¹ * z j) := by
  rw [ext_of_ne _ hz]
  have := cv_proj z hz
  show F (cv ((proj z hz : Sph n) : Ee n)) = _
  rw [this]
  rfl

/-- `∂_i F̃ = ∂_i F − y_i (y·∇F)` at a point `y` of the unit sphere. -/
lemma dd_ext_extr' {F : (Fin n → ℝ) → ℝ} (hF : Sm F) {y : Fin n → ℝ} (hy0 : y ≠ 0) (h1 : nrm y = 1)
    (i : Fin n) :
    dd i (ext fun z : Sph n => F (cv (z : Ee n))) y =
      dd i F y - y i * ∑ k, y k * dd k F y := by
  have hf : ∀ j, SmO (fun z : Fin n → ℝ => (nrm z)⁻¹ * z j) := fun j =>
    SmO.mul (smO_nrm.inv fun z hz => (nrm_pos hz).ne') (SmO.of_sm (contDiff_apply ℝ ℝ j))
  have hev : (ext fun z : Sph n => F (cv (z : Ee n))) =ᶠ[𝓝 y]
      fun z => F (fun j => (nrm z)⁻¹ * z j) := by
    filter_upwards [isOpen_ne0.mem_nhds hy0] with z hz using ext_extr hz
  rw [dd_congr hev i]
  rw [dd_comp_at F hF (fun j z => (nrm z)⁻¹ * z j) hf hy0 i]
  have hv : (fun l => (nrm y)⁻¹ * y l) = y := by funext l; rw [h1]; simp
  rw [hv]
  have hk : ∀ k, dd i (fun z : Fin n → ℝ => (nrm z)⁻¹ * z k) y =
      (if i = k then 1 else 0) - y i * y k := fun k => by
    rw [dd_mul_at (F := fun z : Fin n → ℝ => (nrm z)⁻¹) (G := fun z : Fin n → ℝ => z k)
      (smO_nrm.inv fun z hz => (nrm_pos hz).ne') (SmO.of_sm (contDiff_apply ℝ ℝ k)) hy0 i]
    rw [dd_inv_nrm hy0, dd_coord, h1]
    simp
    ring
  simp only [hk]
  have e1 : ∀ k, MarkovTriple.BGL.pderiv F k y * ((if i = k then (1 : ℝ) else 0) - y i * y k) =
      (if i = k then dd k F y else 0) - y i * (y k * dd k F y) := fun k => by
    by_cases h : i = k
    · subst h; simp [MarkovTriple.BGL.pderiv, dd]; ring
    · simp [h, MarkovTriple.BGL.pderiv, dd]; ring
  simp only [e1, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp

theorem ΓS_extrinsic {F G : (Fin n → ℝ) → ℝ} (hF : Sm F) (hG : Sm G) (x : Sph n) :
    ΓS (fun z : Sph n => F (cv (z : Ee n))) (fun z : Sph n => G (cv (z : Ee n))) x
      = ∑ i, dd i F (cv (x : Ee n)) * dd i G (cv (x : Ee n))
        - (∑ i, cv (x : Ee n) i * dd i F (cv (x : Ee n))) *
          (∑ i, cv (x : Ee n) i * dd i G (cv (x : Ee n))) := by
  have hy0 := cv_ne_zero x
  have h1 := nrm_cv_sph x
  have hy1 : ∑ i, cv (x : Ee n) i * cv (x : Ee n) i = 1 := by
    have := sq_cv x
    simpa [LebesgueRd.sq, pow_two] using this
  unfold ΓS Gf
  simp only [dd_ext_extr' hF hy0 h1, dd_ext_extr' hG hy0 h1]
  generalize cv (x : Ee n) = y at hy1 ⊢
  have e : ∀ i, (dd i F y - y i * ∑ k, y k * dd k F y) * (dd i G y - y i * ∑ k, y k * dd k G y) =
      dd i F y * dd i G y - (∑ k, y k * dd k G y) * (y i * dd i F y)
        - (∑ k, y k * dd k F y) * (y i * dd i G y)
        + (∑ k, y k * dd k F y) * (∑ k, y k * dd k G y) * (y i * y i) := fun i => by ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hy1]
  ring

end MarkovTriple.BGL.SphereN
