import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Curv1
import MarkovTriple.BGL.Instances.SphereN.Hess

/-!
# `CD(n-2, n-1)` on the genuine sphere `S^{n-1}` (Round 28, stream L, group L3)

Following BGL Appendix C.5 in the flat ambient formulation: for the degree-0 extension `F̃` of `f`,
`Γ₂(f)(x) = |Hess F̃(x)|² + (n-4) Γ(f)(x)` (Euclidean Bochner on `ℝ^n`, with the radial weights `|y|²` of
`ext (Γ f) = |y|² |∇F̃|²`, `ext (L f) = |y|² ΔF̃`), and `Hess F̃(x) x = -∇F̃(x)` (Euler), whence
`|Hess F̃|² ≥ 2 |∇F̃|² + (ΔF̃)²/(n-1)`: `Γ₂ ≥ (n-2) Γ + (Lf)²/(n-1)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma dd_coord (i j : Fin n) (y : Fin n → ℝ) :
    dd i (fun z : Fin n → ℝ => z j) y = if i = j then 1 else 0 := by
  unfold dd
  rw [(hasFDerivAt_apply j y).fderiv]
  simp [Pi.single_apply, eq_comm]

lemma Lf_sq (y : Fin n → ℝ) : Lf (LebesgueRd.sq : (Fin n → ℝ) → ℝ) y = 2 * n := by
  have e : ∀ i, dd i (dd i (LebesgueRd.sq : (Fin n → ℝ) → ℝ)) y = 2 := fun i => by
    have : dd i (LebesgueRd.sq : (Fin n → ℝ) → ℝ) = fun z => 2 * z i := funext fun z => dd_sq i z
    rw [this]
    have h : HasFDerivAt (fun z : Fin n → ℝ => 2 * z i) ((2 : ℝ) • (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ)) y :=
      ((hasFDerivAt_apply i y).const_mul (2 : ℝ))
    unfold dd
    rw [h.fderiv]
    simp
  unfold Lf
  simp only [e, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma hom_Gf {F : (Fin n → ℝ) → ℝ} (hF : SmO F) (h : Hom 0 F) : Hom (-2) (Gf F F) := by
  intro t ht y hy
  have h1 : ∀ i, dd i F (t • y) = t ^ ((0 : ℤ) - 1) * dd i F y := fun i => hom_dd hF h i t ht y hy
  unfold Gf
  simp only [h1]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : t ^ ((0 : ℤ) - 1) * t ^ ((0 : ℤ) - 1) = t ^ (-2 : ℤ) := by
    rw [← zpow_add₀ ht.ne']; norm_num
  rw [← this]; ring

/-- Euler for the cut-off: `y · ∇F̂(y) = 0` on the sphere. -/
lemma euler_hat {f : Sph n → ℝ} (hf : f ∈ A₀S n) (x : Sph n) :
    ∑ j, cv (x : Ee n) j * dd j (hat (ext f)) (cv (x : Ee n)) = 0 := by
  have hy := cv_ne_zero x
  have := euler hf (hom_ext f) hy
  simp only [Int.cast_zero, zero_mul] at this
  rw [← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dd_congr (hat_ev (sphere_far x)) j]

/-- the differentiated Euler relation `Hess F̂(y) y = -∇F̂(y)` on the sphere. -/
lemma hess_euler {f : Sph n → ℝ} (hf : f ∈ A₀S n) (x : Sph n) (i : Fin n) :
    dd i (hat (ext f)) (cv (x : Ee n)) +
      ∑ j, cv (x : Ee n) j * dd i (dd j (hat (ext f))) (cv (x : Ee n)) = 0 := by
  have hF : Sm (hat (ext f)) := Sm_hat hf
  set y := cv (x : Ee n) with hy
  have hE : (fun z : Fin n → ℝ => ∑ j, z j * dd j (hat (ext f)) z) =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_far.mem_nhds (sphere_far x)] with z hz
    have hz0 : z ≠ 0 := by
      intro h0; subst h0
      have : nrm (0 : Fin n → ℝ) = 0 := by simp [nrm]
      have hz' : (3 : ℝ) / 10 < nrm 0 := hz
      linarith
    have := euler hf (hom_ext f) hz0
    simp only [Int.cast_zero, zero_mul] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [dd_congr (hat_ev (F := ext f) hz) j]
  have h0 : dd i (fun z : Fin n → ℝ => ∑ j, z j * dd j (hat (ext f)) z) y = 0 := by
    rw [dd_congr hE i]; simp [dd]
  have hh : ∀ j, Sm (fun z : Fin n → ℝ => z j * dd j (hat (ext f)) z) := fun j =>
    (contDiff_apply ℝ ℝ j).mul (hF.dd j)
  rw [dd_fsum hh i] at h0
  simp only at h0
  have hm : ∀ j, dd i (fun z : Fin n → ℝ => z j * dd j (hat (ext f)) z) y =
      (if i = j then 1 else 0) * dd j (hat (ext f)) y + y j * dd i (dd j (hat (ext f))) y := fun j => by
    have := dd_mul (f := fun z : Fin n → ℝ => z j) (g := dd j (hat (ext f)))
      (contDiff_apply ℝ ℝ j) (hF.dd j) i y
    rw [dd_coord] at this
    exact this
  simp only [hm, Finset.sum_add_distrib] at h0
  have : ∑ j, (if i = j then (1 : ℝ) else 0) * dd j (hat (ext f)) y = dd i (hat (ext f)) y := by
    simp
  rw [this] at h0
  exact h0

/-- Euclidean Bochner at a point for a smooth function. -/
lemma bochner_flat {F : (Fin n → ℝ) → ℝ} (hn1 : 1 ≤ n) (hF : Sm F) (y : Fin n → ℝ) :
    (Lf (Gf F F) y - 2 * Gf F (Lf F) y) / 2 = ∑ i, ∑ j, (dd i (dd j F) y) ^ 2 := by
  have hB := Γ₂_eq hn1 hF y
  have hLf : Sm (Lf F) := by
    have : Lf F = fun y => ∑ i, dd i (dd i F) y := rfl
    rw [this]; exact ContDiff.sum fun i _ => (hF.dd i).dd i
  have : (lebesgueRdDiffusion n hn1).Γ₂ F F y = (Lf (Gf F F) y - Gf F (Lf F) y - Gf (Lf F) F y) / 2 := by
    show (Lf ((lebesgueRdDiffusion n hn1).ΓA F F) y - (lebesgueRdDiffusion n hn1).ΓA F (Lf F) y
      - (lebesgueRdDiffusion n hn1).ΓA (Lf F) F y) / 2 = _
    rw [ΓA_eq_Gf hn1 hF hF, ΓA_eq_Gf hn1 hF hLf, ΓA_eq_Gf hn1 hLf hF]
  rw [this, Gf_symm (Lf F) F] at hB
  rw [← hB]; ring

end MarkovTriple.BGL.SphereN
