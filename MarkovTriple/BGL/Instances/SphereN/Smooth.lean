import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Basic

/-!
# Calculus off the origin (Round 28, stream L)

`SmO F`: `F` is `C^∞` on `{y ≠ 0}`; local equality of derivatives; cut-off `hat F`; homogeneity and Euler.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

/-- smooth away from the origin. -/
def SmO (F : (Fin n → ℝ) → ℝ) : Prop := ContDiffOn ℝ (⊤ : ℕ∞) F {y | y ≠ 0}

lemma isOpen_ne0 : IsOpen {y : Fin n → ℝ | y ≠ 0} := isOpen_ne

lemma SmO.cdAt {F : (Fin n → ℝ) → ℝ} (h : SmO F) {y : Fin n → ℝ} (hy : y ≠ 0) :
    ContDiffAt ℝ (⊤ : ℕ∞) F y :=
  ContDiffOn.contDiffAt h (isOpen_ne0.mem_nhds hy)

lemma SmO.differentiableAt {F : (Fin n → ℝ) → ℝ} (h : SmO F) {y : Fin n → ℝ} (hy : y ≠ 0) :
    DifferentiableAt ℝ F y :=
  (h.cdAt hy).differentiableAt (by simp)

lemma SmO.of_sm {F : (Fin n → ℝ) → ℝ} (h : Sm F) : SmO F := h.contDiffOn

lemma SmO.ddO {F : (Fin n → ℝ) → ℝ} (h : SmO F) (i : Fin n) : SmO (dd i F) := by
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ F y) {y | y ≠ 0} :=
    ContDiffOn.fderiv_of_isOpen h isOpen_ne0 (by simp)
  exact h1.clm_apply contDiffOn_const

lemma SmO.add {F G : (Fin n → ℝ) → ℝ} (hF : SmO F) (hG : SmO G) : SmO (fun y => F y + G y) :=
  ContDiffOn.add hF hG

lemma SmO.mul {F G : (Fin n → ℝ) → ℝ} (hF : SmO F) (hG : SmO G) : SmO (fun y => F y * G y) :=
  ContDiffOn.mul hF hG

lemma SmO.const (c : ℝ) : SmO (fun _ : Fin n → ℝ => c) := contDiffOn_const

lemma SmO.sum {k : ℕ} {F : Fin k → (Fin n → ℝ) → ℝ} (h : ∀ j, SmO (F j)) :
    SmO (fun y => ∑ j, F j y) :=
  ContDiffOn.sum fun j _ => h j

lemma SmO.comp {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (f : Fin k → (Fin n → ℝ) → ℝ) (hf : ∀ j, SmO (f j)) :
    SmO (fun y => ψ (fun j => f j y)) :=
  hψ.comp_contDiffOn (contDiffOn_pi.2 hf)

lemma dd_congr {F : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} {G : (Fin n → ℝ) → ℝ}
    (h : F =ᶠ[𝓝 y] G) (i : Fin n) : dd i F y = dd i G y := by
  unfold dd; rw [h.fderiv_eq]

lemma dd_dd_congr {F G : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (h : F =ᶠ[𝓝 y] G) (i j : Fin n) :
    dd i (dd j F) y = dd i (dd j G) y := by
  have h2 : dd j F =ᶠ[𝓝 y] dd j G := by
    filter_upwards [h.eventuallyEq_nhds] with z hz
    exact dd_congr hz j
  exact dd_congr h2 i

lemma continuous_nrm : Continuous (nrm : (Fin n → ℝ) → ℝ) := by
  unfold nrm
  exact continuous_norm.comp (PiLp.continuous_toLp 2 _)

lemma smO_nrm : SmO (nrm : (Fin n → ℝ) → ℝ) := by
  have : (nrm : (Fin n → ℝ) → ℝ) = fun y => Real.sqrt (LebesgueRd.sq y) := funext nrm_eq
  rw [this]
  intro y hy
  refine ContDiffAt.contDiffWithinAt ?_
  have hpos : LebesgueRd.sq y ≠ 0 := by
    rw [← nrm_sq]; exact pow_ne_zero 2 (nrm_pos hy).ne'
  exact (sq_smooth.contDiffAt).sqrt hpos

lemma Sm_of_SmO_of_zero {H : (Fin n → ℝ) → ℝ} (h : SmO H) (hz : ∀ᶠ y in 𝓝 (0 : Fin n → ℝ), H y = 0) :
    Sm H := by
  show ContDiff ℝ (⊤ : ℕ∞) H
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst hy
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hz
  · exact h.cdAt hy

/-! ### cut-off -/

noncomputable def chi (r : ℝ) : ℝ := Real.smoothTransition ((r - 1 / 5) * 10)

lemma chi_smooth : ContDiff ℝ (⊤ : ℕ∞) chi :=
  Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).mul contDiff_const)

lemma chi_of_le {r : ℝ} (h : r ≤ 1 / 5) : chi r = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith)

lemma chi_of_ge {r : ℝ} (h : 3 / 10 ≤ r) : chi r = 1 :=
  Real.smoothTransition.one_of_one_le (by nlinarith)

/-- cut-off extension (globally defined, equal to `F` for `|y| ≥ 3/10`). -/
noncomputable def hat (F : (Fin n → ℝ) → ℝ) : (Fin n → ℝ) → ℝ := fun y => chi (nrm y) * F y

lemma Sm_hat {F : (Fin n → ℝ) → ℝ} (hF : SmO F) : Sm (hat F) := by
  refine Sm_of_SmO_of_zero ((chi_smooth.contDiffOn.comp smO_nrm (fun _ _ => Set.mem_univ _)).mul hF) ?_
  have : ∀ᶠ y in 𝓝 (0 : Fin n → ℝ), nrm y < 1 / 5 := by
    have h0 : nrm (0 : Fin n → ℝ) = 0 := by simp [nrm]
    have := continuous_nrm.continuousAt (x := (0 : Fin n → ℝ))
    exact this.eventually (gt_mem_nhds (by rw [h0]; norm_num))
  filter_upwards [this] with y hy
  show chi (nrm y) * F y = 0
  rw [chi_of_le hy.le, zero_mul]

lemma isOpen_far : IsOpen {y : Fin n → ℝ | 3 / 10 < nrm y} :=
  isOpen_lt continuous_const continuous_nrm

lemma hat_eventuallyEq {F : (Fin n → ℝ) → ℝ} {y : Fin n → ℝ} (hy : 3 / 10 < nrm y) :
    hat F =ᶠ[𝓝 y] F := by
  filter_upwards [isOpen_far.mem_nhds hy] with z hz
  show chi (nrm z) * F z = F z
  rw [chi_of_ge (le_of_lt hz), one_mul]

end MarkovTriple.BGL.SphereN
