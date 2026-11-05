import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Extrinsic

/-!
# Extrinsic formula for `L` on the sphere (Round 28, stream L, group L1)

`L f = ΔF − Σ_{ij} x_i x_j ∂_i∂_j F − (n−1) x·∇F` at points of the unit sphere, for `f = F|_{S^{n-1}}`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma dd_sum_at {k : ℕ} {h : Fin k → (Fin n → ℝ) → ℝ} (hh : ∀ j, SmO (h j)) {y : Fin n → ℝ}
    (hy : y ≠ 0) (i : Fin n) : dd i (fun z => ∑ j, h j z) y = ∑ j, dd i (h j) y := by
  have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => ((hh j).differentiableAt hy).hasFDerivAt)
  unfold dd
  rw [this.fderiv]
  simp

/-- pure algebra of the final summation. -/
lemma extr_alg (H : Fin n → Fin n → ℝ) (g y : Fin n → ℝ) (hy : ∑ i, y i * y i = 1) :
    ∑ i, ∑ k, ((∑ j, H j k * ((if i = j then 1 else 0) - y i * y j)) *
        ((if i = k then 1 else 0) - y i * y k) +
      g k * (-((if i = k then 1 else 0) * y i) - (y k + y i * (if i = k then 1 else 0))
        + 3 * (y i * y i * y k))) =
    ∑ k, H k k - ∑ j, ∑ k, y j * y k * H j k - ((n : ℝ) - 1) * ∑ k, y k * g k := by
  let δ : Fin n → Fin n → ℝ := fun i j => if i = j then 1 else 0
  have hP : ∀ j k, ∑ i, (δ i j - y i * y j) * (δ i k - y i * y k) = δ j k - y j * y k := by
    intro j k
    have e : ∀ i, (δ i j - y i * y j) * (δ i k - y i * y k) =
        δ i j * δ i k - (δ i j * y i) * y k - (δ i k * y i) * y j + (y i * y i) * (y j * y k) := fun i => by ring
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hy]
    have a1 : ∑ i, δ i j * δ i k = δ j k := by
      simp only [δ]
      by_cases h : j = k
      · subst h; simp
      · simp [h]
        intro hjk
        exact absurd hjk.symm h
    have a2 : ∑ i, δ i j * y i = y j := by simp [δ, Finset.sum_ite_eq']
    have a3 : ∑ i, δ i k * y i = y k := by simp [δ, Finset.sum_ite_eq']
    rw [a1, a2, a3]; ring
  have t1 : ∑ i, ∑ k, (∑ j, H j k * (δ i j - y i * y j)) * (δ i k - y i * y k) =
      ∑ k, H k k - ∑ j, ∑ k, y j * y k * H j k := by
    have : ∀ i k, (∑ j, H j k * (δ i j - y i * y j)) * (δ i k - y i * y k) =
        ∑ j, H j k * ((δ i j - y i * y j) * (δ i k - y i * y k)) := fun i k => by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
    simp only [this]
    rw [Finset.sum_comm]
    have : ∀ k, ∑ i, ∑ j, H j k * ((δ i j - y i * y j) * (δ i k - y i * y k)) =
        ∑ j, H j k * (δ j k - y j * y k) := fun k => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => by rw [← Finset.mul_sum, hP]
    simp only [this]
    have e2 : ∀ k, ∑ j, H j k * (δ j k - y j * y k) = H k k - ∑ j, y j * y k * H j k := fun k => by
      simp only [mul_sub, Finset.sum_sub_distrib]
      congr 1
      · simp [δ]
      · exact Finset.sum_congr rfl fun j _ => by ring
    simp only [e2, Finset.sum_sub_distrib]
    congr 1
    exact Finset.sum_comm
  have t2 : ∑ i, ∑ k, g k * (-(δ i k * y i) - (y k + y i * δ i k) + 3 * (y i * y i * y k)) =
      -((n : ℝ) - 1) * ∑ k, y k * g k := by
    have : ∀ i k, g k * (-(δ i k * y i) - (y k + y i * δ i k) + 3 * (y i * y i * y k)) =
        -2 * (δ i k * (y i * g k)) - (y k * g k) + 3 * ((y i * y i) * (y k * g k)) := fun i k => by ring
    have hc : ∀ (c : ℝ) (F : Fin n → Fin n → ℝ), ∑ i, ∑ k, c * F i k = c * ∑ i, ∑ k, F i k := by
      intro c F; simp [Finset.mul_sum]
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, hc]
    have b1 : ∑ i, ∑ k, δ i k * (y i * g k) = ∑ k, y k * g k := by
      simp [δ, Finset.sum_ite_eq]
    have b2 : ∑ _i : Fin n, ∑ k, y k * g k = (n : ℝ) * ∑ k, y k * g k := by simp
    have b3 : ∑ i, ∑ k, (y i * y i) * (y k * g k) = ∑ k, y k * g k := by
      rw [← Finset.sum_mul_sum, hy, one_mul]
    rw [b1, b2, b3]
    ring
  simp only [Finset.sum_add_distrib]
  simp only [δ] at t1 t2
  rw [t1, t2]
  ring

end MarkovTriple.BGL.SphereN

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma smO_u : SmO (fun z : Fin n → ℝ => (nrm z)⁻¹) := smO_nrm.inv fun _ hz => (nrm_pos hz).ne'

/-- `C i k z = ∂_i (z_k / |z|)`. -/
noncomputable def Cc (i k : Fin n) (z : Fin n → ℝ) : ℝ :=
  (if i = k then 1 else 0) * (nrm z)⁻¹ +
    (-1) * ((z i * z k) * ((nrm z)⁻¹ * (nrm z)⁻¹ * (nrm z)⁻¹))

lemma smO_Cc (i k : Fin n) : SmO (Cc i k) := by
  have hc : ∀ j, SmO (fun z : Fin n → ℝ => z j) := fun j => SmO.of_sm (contDiff_apply ℝ ℝ j)
  unfold Cc
  exact SmO.add (SmO.mul (SmO.const _) smO_u)
    (SmO.mul (SmO.const _) (SmO.mul (SmO.mul (hc i) (hc k)) (SmO.mul (SmO.mul smO_u smO_u) smO_u)))

lemma dd_N {z : Fin n → ℝ} (hz : z ≠ 0) (i k : Fin n) :
    dd i (fun w : Fin n → ℝ => (nrm w)⁻¹ * w k) z = Cc i k z := by
  rw [dd_mul_at smO_u (SmO.of_sm (contDiff_apply ℝ ℝ k)) hz i, dd_inv_nrm hz, dd_coord]
  have := (nrm_pos hz).ne'
  unfold Cc
  field_simp
  ring

lemma ext_extr_ev {F : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (hy0 : y ≠ 0) :
    (ext fun z : Sph n => F (cv (z : Ee n))) =ᶠ[𝓝 y] fun z => F (fun j => (nrm z)⁻¹ * z j) := by
  filter_upwards [isOpen_ne0.mem_nhds hy0] with z hz using ext_extr hz

lemma hN (j : Fin n) : SmO (fun z : Fin n → ℝ => (nrm z)⁻¹ * z j) :=
  SmO.mul smO_u (SmO.of_sm (contDiff_apply ℝ ℝ j))

lemma dd_ext_gen {F : (Fin n → ℝ) → ℝ} (hF : Sm F) {z : Fin n → ℝ} (hz : z ≠ 0) (i : Fin n) :
    dd i (ext fun w : Sph n => F (cv (w : Ee n))) z =
      ∑ k, dd k F (fun j => (nrm z)⁻¹ * z j) * Cc i k z := by
  rw [dd_congr (ext_extr_ev hz) i, dd_comp_at F hF (fun j w => (nrm w)⁻¹ * w j) hN hz i]
  exact Finset.sum_congr rfl fun k _ => by rw [dd_N hz]; rfl

lemma Cc_at {y : Fin n → ℝ} (h1 : nrm y = 1) (i k : Fin n) :
    Cc i k y = (if i = k then 1 else 0) - y i * y k := by
  unfold Cc; rw [h1]; ring

lemma dd_Cc_at {y : Fin n → ℝ} (hy0 : y ≠ 0) (h1 : nrm y = 1) (i k : Fin n) :
    dd i (Cc i k) y = -((if i = k then 1 else 0) * y i) - (y k + y i * (if i = k then 1 else 0))
      + 3 * (y i * y i * y k) := by
  have hc : ∀ j, SmO (fun z : Fin n → ℝ => z j) := fun j => SmO.of_sm (contDiff_apply ℝ ℝ j)
  have hdu : dd i (fun z : Fin n → ℝ => (nrm z)⁻¹) y = -y i := by
    rw [dd_inv_nrm hy0, h1]; simp
  have hu2 : dd i (fun z : Fin n → ℝ => (nrm z)⁻¹ * (nrm z)⁻¹) y = -2 * y i := by
    rw [dd_mul_at smO_u smO_u hy0 i, hdu, h1]; simp; ring
  have hu3 : dd i (fun z : Fin n → ℝ => (nrm z)⁻¹ * (nrm z)⁻¹ * (nrm z)⁻¹) y = -3 * y i := by
    rw [dd_mul_at (F := fun z : Fin n → ℝ => (nrm z)⁻¹ * (nrm z)⁻¹) (G := fun z : Fin n → ℝ => (nrm z)⁻¹)
      (SmO.mul smO_u smO_u) smO_u hy0 i, hu2, hdu, h1]
    simp; ring
  have hp : dd i (fun z : Fin n → ℝ => z i * z k) y = y k + y i * (if i = k then 1 else 0) := by
    rw [dd_mul_at (hc i) (hc k) hy0 i, dd_coord, dd_coord]; simp
  have hw : dd i (fun z : Fin n → ℝ => (z i * z k) * ((nrm z)⁻¹ * (nrm z)⁻¹ * (nrm z)⁻¹)) y =
      (y k + y i * (if i = k then 1 else 0)) * 1 + (y i * y k) * (-3 * y i) := by
    rw [dd_mul_at (F := fun z : Fin n → ℝ => z i * z k)
      (G := fun z : Fin n → ℝ => (nrm z)⁻¹ * (nrm z)⁻¹ * (nrm z)⁻¹)
      (SmO.mul (hc i) (hc k)) (SmO.mul (SmO.mul smO_u smO_u) smO_u) hy0 i, hp, hu3, h1]
    simp
  unfold Cc
  rw [dd_add_at (F := fun z : Fin n → ℝ => (if i = k then (1 : ℝ) else 0) * (nrm z)⁻¹)
    (G := fun z : Fin n → ℝ => (-1) * ((z i * z k) * ((nrm z)⁻¹ * (nrm z)⁻¹ * (nrm z)⁻¹)))
    (SmO.mul (SmO.const _) smO_u)
    (SmO.mul (SmO.const _) (SmO.mul (SmO.mul (hc i) (hc k)) (SmO.mul (SmO.mul smO_u smO_u) smO_u))) hy0 i]
  rw [dd_smul_at (c := (if i = k then (1 : ℝ) else 0)) smO_u hy0 i,
    dd_smul_at (c := (-1 : ℝ)) (SmO.mul (SmO.mul (hc i) (hc k)) (SmO.mul (SmO.mul smO_u smO_u) smO_u)) hy0 i,
    hdu, hw]
  ring

/-- extrinsic formula for the Laplacian of the degree-0 extension at a point of the unit sphere. -/
lemma Lf_ext_extr {F : (Fin n → ℝ) → ℝ} (hF : Sm F) {y : Fin n → ℝ} (hy0 : y ≠ 0) (h1 : nrm y = 1) :
    Lf (ext fun z : Sph n => F (cv (z : Ee n))) y =
      Lf F y - ∑ i, ∑ j, y i * y j * dd i (dd j F) y - ((n : ℝ) - 1) * ∑ i, y i * dd i F y := by
  have hy1 : ∑ i, y i * y i = 1 := by
    have h2 := nrm_sq y
    rw [h1] at h2
    have : LebesgueRd.sq y = ∑ i, y i * y i := by simp [LebesgueRd.sq, pow_two]
    rw [← this, ← h2]; norm_num
  have hev : ∀ i, dd i (ext fun z : Sph n => F (cv (z : Ee n))) =ᶠ[𝓝 y]
      fun z => ∑ k, dd k F (fun j => (nrm z)⁻¹ * z j) * Cc i k z := fun i => by
    filter_upwards [isOpen_ne0.mem_nhds hy0] with z hz using dd_ext_gen hF hz i
  have hSm : ∀ i k, SmO (fun z : Fin n → ℝ => dd k F (fun j => (nrm z)⁻¹ * z j) * Cc i k z) :=
    fun i k => SmO.mul (SmO.comp (dd k F) (hF.dd k) (fun j z => (nrm z)⁻¹ * z j) hN) (smO_Cc i k)
  have step : ∀ i, dd i (dd i (ext fun z : Sph n => F (cv (z : Ee n)))) y =
      ∑ k, ((∑ j, dd j (dd k F) y * ((if i = j then 1 else 0) - y i * y j)) *
          ((if i = k then 1 else 0) - y i * y k) +
        dd k F y * (-((if i = k then 1 else 0) * y i) - (y k + y i * (if i = k then 1 else 0))
          + 3 * (y i * y i * y k))) := fun i => by
    rw [dd_congr (hev i) i, dd_sum_at (hSm i) hy0 i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dd_mul_at (SmO.comp (dd k F) (hF.dd k) (fun j z => (nrm z)⁻¹ * z j) hN) (smO_Cc i k) hy0 i,
      dd_comp_at (dd k F) (hF.dd k) (fun j z => (nrm z)⁻¹ * z j) hN hy0 i, dd_Cc_at hy0 h1,
      Cc_at h1]
    have hv : (fun l => (nrm y)⁻¹ * y l) = y := by funext l; rw [h1]; simp
    rw [hv]
    have : ∀ j, MarkovTriple.BGL.pderiv (dd k F) j y * dd i (fun z : Fin n → ℝ => (nrm z)⁻¹ * z j) y =
        dd j (dd k F) y * ((if i = j then 1 else 0) - y i * y j) := fun j => by
      rw [dd_N hy0, Cc_at h1]; rfl
    simp only [this]
  unfold Lf
  simp only [step]
  rw [extr_alg (fun j k => dd j (dd k F) y) (fun k => dd k F y) y hy1]


theorem LS_extrinsic {F : (Fin n → ℝ) → ℝ} (hF : Sm F) (x : Sph n) :
    LS (fun z : Sph n => F (cv (z : Ee n))) x =
      Lf F (cv (x : Ee n)) - ∑ i, ∑ j, cv (x : Ee n) i * cv (x : Ee n) j * dd i (dd j F) (cv (x : Ee n))
        - ((n : ℝ) - 1) * ∑ i, cv (x : Ee n) i * dd i F (cv (x : Ee n)) :=
  Lf_ext_extr hF (cv_ne_zero x) (nrm_cv_sph x)

end MarkovTriple.BGL.SphereN
