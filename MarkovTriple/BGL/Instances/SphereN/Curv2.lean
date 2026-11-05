import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Curv

/-!
# `Γ₂` on the genuine sphere and `CD(n-2, n-1)` (Round 28, stream L, group L3)
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma sq_cv (x : Sph n) : LebesgueRd.sq (cv (x : Ee n)) = 1 := by
  rw [← nrm_sq, nrm_cv_sph]; norm_num

lemma ΓS_eq (f g : Sph n → ℝ) (x : Sph n) :
    ΓS f g x = Gf (hat (ext f)) (hat (ext g)) (cv (x : Ee n)) :=
  Gf_congr (hat_ev (sphere_far x)).symm (hat_ev (sphere_far x)).symm

lemma LS_eq (f : Sph n → ℝ) (x : Sph n) :
    LS f x = Lf (hat (ext f)) (cv (x : Ee n)) :=
  Lf_congr (hat_ev (sphere_far x)).symm

/-- `LS (ΓS f f) = Δ W + (2n-8) |∇F̃|²` with `W = |∇F̂|²`. -/
lemma LS_ΓS {f : Sph n → ℝ} (hf : f ∈ A₀S n) (x : Sph n) :
    LS (ΓS f f) x = Lf (Gf (hat (ext f)) (hat (ext f))) (cv (x : Ee n))
      + (2 * n - 8) * ΓS f f x := by
  have hfar := sphere_far x
  set y := cv (x : Ee n) with hy
  have hy0 := cv_ne_zero x
  have hF : Sm (hat (ext f)) := Sm_hat hf
  have hW : Sm (Gf (hat (ext f)) (hat (ext f))) := by
    have : Gf (hat (ext f)) (hat (ext f)) = fun z => ∑ i, dd i (hat (ext f)) z * dd i (hat (ext f)) z := rfl
    rw [this]; exact ContDiff.sum fun i _ => (hF.dd i).mul (hF.dd i)
  -- local form of `ext (ΓS f f)`
  have e1 : ext (ΓS f f) =ᶠ[𝓝 y] fun z => LebesgueRd.sq z * Gf (hat (ext f)) (hat (ext f)) z := by
    filter_upwards [isOpen_far.mem_nhds hfar] with z hz
    have hz0 : z ≠ 0 := by
      intro h0; subst h0
      have : nrm (0 : Fin n → ℝ) = 0 := by simp [nrm]
      have hz' : (3 : ℝ) / 10 < nrm 0 := hz
      linarith
    rw [ext_ΓS hf hf hz0]
    congr 1
    exact Gf_congr (hat_ev hz).symm (hat_ev hz).symm
  show Lf (ext (ΓS f f)) y = _
  rw [Lf_congr e1]
  have hprod := Lf_mul (sq_smooth (d := n)) hW y
  have hprod' : Lf (fun z => LebesgueRd.sq z * Gf (hat (ext f)) (hat (ext f)) z) y =
      LebesgueRd.sq y * Lf (Gf (hat (ext f)) (hat (ext f))) y
        + Gf (hat (ext f)) (hat (ext f)) y * Lf LebesgueRd.sq y
        + 2 * Gf LebesgueRd.sq (Gf (hat (ext f)) (hat (ext f))) y := hprod
  rw [hprod', sq_cv x, Lf_sq]
  have hEu : ∑ i, y i * dd i (Gf (hat (ext f)) (hat (ext f))) y = -2 * Gf (hat (ext f)) (hat (ext f)) y := by
    have hGff : SmO (Gf (ext f) (ext f)) := smO_Gf hf hf
    have hh : Hom (-2) (Gf (ext f) (ext f)) := hom_Gf hf (hom_ext f)
    have := euler hGff hh hy0
    have hev : Gf (hat (ext f)) (hat (ext f)) =ᶠ[𝓝 y] Gf (ext f) (ext f) :=
      Gf_ev (hat_ev hfar) (hat_ev hfar)
    have hv : Gf (hat (ext f)) (hat (ext f)) y = Gf (ext f) (ext f) y := hev.self_of_nhds
    rw [hv]
    push_cast at this
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dd_congr hev i]
  have hGs : Gf LebesgueRd.sq (Gf (hat (ext f)) (hat (ext f))) y =
      2 * ∑ i, y i * dd i (Gf (hat (ext f)) (hat (ext f))) y := by
    unfold Gf
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [dd_sq]; ring
  rw [hGs, hEu, ΓS_eq]
  ring

/-- `ΓS f (LS f) = ∇F̂ · ∇ΔF̂` at points of the sphere. -/
lemma ΓS_LS {f : Sph n → ℝ} (hf : f ∈ A₀S n) (x : Sph n) :
    ΓS f (LS f) x = Gf (hat (ext f)) (Lf (hat (ext f))) (cv (x : Ee n)) := by
  have hfar := sphere_far x
  set y := cv (x : Ee n) with hy
  have hy0 := cv_ne_zero x
  have hLS : SmO (Lf (ext f)) := smO_Lf hf
  have e1 : ext (LS f) =ᶠ[𝓝 y] fun z => LebesgueRd.sq z * Lf (ext f) z := by
    filter_upwards [isOpen_far.mem_nhds hfar] with z hz
    have hz0 : z ≠ 0 := by
      intro h0; subst h0
      have : nrm (0 : Fin n → ℝ) = 0 := by simp [nrm]
      have hz' : (3 : ℝ) / 10 < nrm 0 := hz
      linarith
    exact ext_LS hf hz0
  have hd : ∀ i, dd i (ext (LS f)) y =
      2 * y i * Lf (ext f) y + dd i (Lf (ext f)) y := fun i => by
    rw [dd_congr e1 i, dd_mul_at (SmO.of_sm (sq_smooth (d := n))) hLS hy0 i, dd_sq, sq_cv x]
    ring
  have hEu : ∑ i, y i * dd i (ext f) y = 0 := by
    have := euler hf (hom_ext f) hy0
    simpa using this
  show Gf (ext f) (ext (LS f)) y = _
  have hL : Lf (hat (ext f)) =ᶠ[𝓝 y] Lf (ext f) := Lf_ev (hat_ev hfar)
  have hR : Gf (hat (ext f)) (Lf (hat (ext f))) y = Gf (ext f) (Lf (ext f)) y :=
    Gf_congr (hat_ev hfar) hL
  rw [hR]
  unfold Gf
  simp only [hd, mul_add]
  rw [Finset.sum_add_distrib]
  have : ∑ i, dd i (ext f) y * (2 * y i * Lf (ext f) y) = 2 * Lf (ext f) y * ∑ i, y i * dd i (ext f) y := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, hEu]
  simp

/-- `Γ₂(f) = |Hess F̂|² + (n-4) Γ(f)` at points of the sphere. -/
theorem Γ₂_formula (hn : 2 ≤ n) {f : Sph n → ℝ} (hf : f ∈ A₀S n) (x : Sph n) :
    (sphereDiffusion n hn).Γ₂ f f x =
      ∑ i, ∑ j, (dd i (dd j (hat (ext f))) (cv (x : Ee n))) ^ 2 + ((n : ℝ) - 4) * ΓS f f x := by
  have hF : Sm (hat (ext f)) := Sm_hat hf
  have hLSf : LS f ∈ A₀S n := LS_mem hf
  show (LS ((sphereDiffusion n hn).ΓA f f) x - (sphereDiffusion n hn).ΓA f (LS f) x
      - (sphereDiffusion n hn).ΓA (LS f) f x) / 2 = _
  rw [ΓA_eq_ΓS hn hf hf, ΓA_eq_ΓS hn hf hLSf, ΓA_eq_ΓS hn hLSf hf, ΓS_symm (LS f) f,
    LS_ΓS hf x, ΓS_LS hf x, ← bochner_flat (by omega) hF]
  ring

/-- **`CD(n-2, n-1)` on the round sphere `S^{n-1}`** (BGL Appendix C.5), pointwise for all `f ∈ 𝒜₀`. -/
theorem sphere_CD (hn : 2 ≤ n) {f : Sph n → ℝ} (hf : f ∈ A₀S n) (x : Sph n) :
    ((n : ℝ) - 2) * ΓS f f x + (1 / ((n : ℝ) - 1)) * (LS f x) ^ 2 ≤
      (sphereDiffusion n hn).Γ₂ f f x := by
  have hF : Sm (hat (ext f)) := Sm_hat hf
  set y := cv (x : Ee n) with hy
  rw [Γ₂_formula hn hf x]
  set H : Fin n → Fin n → ℝ := fun i j => dd i (dd j (hat (ext f))) y with hH
  set w : Fin n → ℝ := fun i => -dd i (hat (ext f)) y with hw
  have hsym : ∀ i j, H i j = H j i := fun i j => dd_dd_symm hF i j y
  have hHy : ∀ i, ∑ j, H i j * y j = w i := fun i => by
    have := hess_euler hf x i
    simp only [hH, hw]
    have e : ∑ j, dd i (dd j (hat (ext f))) y * y j = ∑ j, y j * dd i (dd j (hat (ext f))) y :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [e]; linarith
  have hy1 : ∑ i, y i ^ 2 = 1 := by
    have := sq_cv x
    simpa [LebesgueRd.sq] using this
  have hwy : ∑ i, w i * y i = 0 := by
    have h1 : ∑ i, w i * y i = -(∑ j, y j * dd j (hat (ext f)) y) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by simp only [hw]; ring
    rw [h1, euler_hat hf x]; simp
  have key := hess_ineq hn H y w hsym hHy hy1 hwy
  have hΓ : ΓS f f x = ∑ i, w i ^ 2 := by
    rw [ΓS_eq]
    unfold Gf
    exact Finset.sum_congr rfl fun i _ => by simp only [hw]; ring
  have hT : LS f x = ∑ i, H i i := by
    rw [LS_eq]; rfl
  have hnn : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  rw [hT, hΓ, one_div, inv_mul_eq_div]
  have : (∑ i, H i i) ^ 2 / ((n : ℝ) - 1) = (∑ i, H i i) ^ 2 / ((n : ℝ) - 1) := rfl
  nlinarith [key]

end MarkovTriple.BGL.SphereN
