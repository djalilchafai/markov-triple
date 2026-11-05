import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Ops

/-!
# Pointwise first-order calculus off the origin and the algebraic axioms (Round 28, stream L)
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

lemma dd_add_at {F G : (Fin n → ℝ) → ℝ} (hF : SmO F) (hG : SmO G) {y : Fin n → ℝ} (hy : y ≠ 0)
    (i : Fin n) : dd i (fun z => F z + G z) y = dd i F y + dd i G y := by
  have h : fderiv ℝ (fun z => F z + G z) y = _ :=
    ((hF.differentiableAt hy).hasFDerivAt.add (hG.differentiableAt hy).hasFDerivAt).fderiv
  unfold dd
  rw [h]
  rfl

lemma dd_smul_at (c : ℝ) {F : (Fin n → ℝ) → ℝ} (hF : SmO F) {y : Fin n → ℝ} (hy : y ≠ 0)
    (i : Fin n) : dd i (fun z => c * F z) y = c * dd i F y := by
  unfold dd
  rw [fderiv_const_mul (hF.differentiableAt hy)]
  rfl

lemma dd_mul_at {F G : (Fin n → ℝ) → ℝ} (hF : SmO F) (hG : SmO G) {y : Fin n → ℝ} (hy : y ≠ 0)
    (i : Fin n) : dd i (fun z => F z * G z) y = dd i F y * G y + F y * dd i G y := by
  have h : fderiv ℝ (fun z => F z * G z) y = _ :=
    ((hF.differentiableAt hy).hasFDerivAt.mul (hG.differentiableAt hy).hasFDerivAt).fderiv
  unfold dd
  rw [h]
  simp
  ring

lemma dd_comp_at {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin n → ℝ) → ℝ) (hf : ∀ j, SmO (f j)) {x : Fin n → ℝ} (hx : x ≠ 0) (i : Fin n) :
    dd i (fun y => ψ (fun j => f j y)) x =
      ∑ j, MarkovTriple.BGL.pderiv ψ j (fun l => f l x) * dd i (f j) x := by
  have hF : HasFDerivAt (fun y => fun j => f j y)
      (ContinuousLinearMap.pi fun j => fderiv ℝ (f j) x) x :=
    hasFDerivAt_pi'.2 fun j => ((hf j).differentiableAt hx).hasFDerivAt
  have hψd : HasFDerivAt ψ (fderiv ℝ ψ (fun l => f l x)) (fun l => f l x) :=
    ((hψ.differentiable (by simp)) _).hasFDerivAt
  have h := hψd.comp x hF
  have h2 : fderiv ℝ (fun y => ψ fun j => f j y) x = _ := h.fderiv
  unfold dd
  rw [h2]
  simp only [ContinuousLinearMap.comp_apply]
  rw [MarkovTriple.BGL.Lebesgue.clm_pi_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [ContinuousLinearMap.pi_apply, MarkovTriple.BGL.pderiv]
  ring

lemma ext_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (h0 : ψ 0 = 0) (f : Fin k → Sph n → ℝ) :
    ext (fun x => ψ (fun j => f j x)) = fun y => ψ (fun j => ext (f j) y) := by
  funext y
  by_cases hy : y = 0
  · subst hy
    have : (fun j : Fin k => ext (f j) 0) = 0 := funext fun j => ext_zero _
    rw [ext_zero, this, h0]
  · simp [ext_of_ne _ hy]

lemma ΓS_symm (f g : Sph n → ℝ) : ΓS f g = ΓS g f := by
  funext x; simp [ΓS, Gf, mul_comm]

lemma ΓS_nonneg (f : Sph n → ℝ) (x : Sph n) : 0 ≤ ΓS f f x := by
  unfold ΓS Gf
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

lemma ΓS_add {f f' g : Sph n → ℝ} (hf : f ∈ A₀S n) (hf' : f' ∈ A₀S n) :
    ΓS (f + f') g = ΓS f g + ΓS f' g := by
  funext x
  have hx := cv_ne_zero x
  simp only [ΓS, Gf, Pi.add_apply, ext_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := dd_add_at hf hf' hx i
  rw [show dd i (ext f + ext f') = dd i (fun z => ext f z + ext f' z) from rfl, this]
  ring

lemma ΓS_smul (c : ℝ) {f g : Sph n → ℝ} (hf : f ∈ A₀S n) :
    ΓS (c • f) g = c • ΓS f g := by
  funext x
  have hx := cv_ne_zero x
  simp only [ΓS, Gf, Pi.smul_apply, ext_smul', smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := dd_smul_at c hf hx i
  rw [show dd i (c • ext f) = dd i (fun z => c * ext f z) from rfl, this]
  ring

lemma ΓS_comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → Sph n → ℝ) (hf : ∀ j, f j ∈ A₀S n) (g : Sph n → ℝ) :
    ΓS (fun x => ψ (fun j => f j x)) g
      = fun x => ∑ j, MarkovTriple.BGL.pderiv ψ j (fun l => f l x) * ΓS (f j) g x := by
  funext x
  have hx := cv_ne_zero x
  have hfx : ∀ l, f l x = ext (f l) (cv (x : Ee n)) := fun l => (ext_cv _ _).symm
  simp only [ΓS, Gf, ext_comp ψ h0 f, dd_comp_at ψ hψ (fun j => ext (f j)) hf hx, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [← hfx]
  ring

end MarkovTriple.BGL.SphereN
