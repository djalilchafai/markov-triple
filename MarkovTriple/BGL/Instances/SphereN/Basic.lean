import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Basic

/-!
# The round sphere `S^{n-1} ⊂ ℝ^n` (Round 28, stream L): space, extension, norm

Statements frozen in `STATEMENTS_R28_L.md`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.SphereN

open LebesgueRd

variable {n : ℕ}

abbrev Ee (n : ℕ) := EuclideanSpace ℝ (Fin n)
abbrev Sph (n : ℕ) := Metric.sphere (0 : Ee n) 1

/-- coordinates of a point of `Ee n`. -/
def cv (x : Ee n) : Fin n → ℝ := WithLp.ofLp x

/-- the Euclidean norm of `y : Fin n → ℝ`. -/
noncomputable def nrm (y : Fin n → ℝ) : ℝ := ‖(WithLp.toLp 2 y : Ee n)‖

lemma nrm_eq (y : Fin n → ℝ) : nrm y = Real.sqrt (LebesgueRd.sq y) := by
  unfold nrm LebesgueRd.sq
  rw [EuclideanSpace.norm_eq]
  simp

lemma nrm_nonneg (y : Fin n → ℝ) : 0 ≤ nrm y := norm_nonneg _

lemma nrm_pos {y : Fin n → ℝ} (hy : y ≠ 0) : 0 < nrm y := by
  unfold nrm
  rw [norm_pos_iff]
  intro h
  apply hy
  have := congrArg WithLp.ofLp h
  simpa using this

lemma nrm_smul (t : ℝ) (y : Fin n → ℝ) : nrm (t • y) = |t| * nrm y := by
  unfold nrm
  have : (WithLp.toLp 2 (t • y) : Ee n) = t • WithLp.toLp 2 y := rfl
  rw [this, norm_smul, Real.norm_eq_abs]

lemma nrm_cv (x : Ee n) : nrm (cv x) = ‖x‖ := rfl

lemma nrm_cv_sph (x : Sph n) : nrm (cv (x : Ee n)) = 1 := by
  rw [nrm_cv]; simp

lemma nrm_sq (y : Fin n → ℝ) : nrm y ^ 2 = LebesgueRd.sq y := by
  rw [nrm_eq]; exact Real.sq_sqrt (LebesgueRd.sq_nonneg' y)

lemma cv_ne_zero (x : Sph n) : cv (x : Ee n) ≠ 0 := by
  intro h
  have := nrm_cv_sph x
  rw [h] at this
  have h0 : nrm (0 : Fin n → ℝ) = 0 := by simp [nrm]
  linarith

/-- radial projection `y ↦ y/|y|` as a point of the sphere. -/
noncomputable def proj (y : Fin n → ℝ) (hy : y ≠ 0) : Sph n :=
  ⟨(nrm y)⁻¹ • (WithLp.toLp 2 y : Ee n), by
    have h := nrm_pos hy
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos h]
    exact inv_mul_cancel₀ h.ne'⟩

lemma proj_coe_apply (y : Fin n → ℝ) (hy : y ≠ 0) (i : Fin n) :
    ((proj y hy : Sph n) : Ee n) i = (nrm y)⁻¹ * y i := by
  simp [proj]

lemma proj_cv (x : Sph n) : proj (cv (x : Ee n)) (cv_ne_zero x) = x := by
  apply Subtype.ext
  ext i
  rw [proj_coe_apply, nrm_cv_sph]
  simp [cv]

lemma proj_smul {t : ℝ} (ht : 0 < t) {y : Fin n → ℝ} (hy : y ≠ 0) (hty : t • y ≠ 0) :
    proj (t • y) hty = proj y hy := by
  apply Subtype.ext
  ext i
  rw [proj_coe_apply, proj_coe_apply, nrm_smul, abs_of_pos ht]
  have := (nrm_pos hy).ne'
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- degree-0 homogeneous extension of `f : S^{n-1} → ℝ` to `ℝ^n` (`0` at the origin). -/
noncomputable def ext (f : Sph n → ℝ) : (Fin n → ℝ) → ℝ :=
  fun y => if h : y ≠ 0 then f (proj y h) else 0

lemma ext_of_ne (f : Sph n → ℝ) {y : Fin n → ℝ} (hy : y ≠ 0) : ext f y = f (proj y hy) := by
  simp [ext, hy]

lemma ext_zero (f : Sph n → ℝ) : ext f 0 = 0 := by simp [ext]

lemma ext_cv (f : Sph n → ℝ) (x : Sph n) : ext f (cv (x : Ee n)) = f x := by
  rw [ext_of_ne f (cv_ne_zero x), proj_cv]

lemma ext_smul (f : Sph n → ℝ) {t : ℝ} (ht : 0 < t) (y : Fin n → ℝ) :
    ext f (t • y) = ext f y := by
  by_cases hy : y = 0
  · subst hy; simp [ext_zero]
  · have hty : t • y ≠ 0 := smul_ne_zero ht.ne' hy
    rw [ext_of_ne f hy, ext_of_ne f hty, proj_smul ht hy hty]

lemma ext_add (f g : Sph n → ℝ) : ext (f + g) = ext f + ext g := by
  funext y; by_cases hy : y = 0
  · subst hy; simp [ext_zero]
  · simp [ext_of_ne _ hy]

lemma ext_mul (f g : Sph n → ℝ) : ext (f * g) = ext f * ext g := by
  funext y; by_cases hy : y = 0
  · subst hy; simp [ext_zero]
  · simp [ext_of_ne _ hy]

lemma ext_smul' (c : ℝ) (f : Sph n → ℝ) : ext (c • f) = c • ext f := by
  funext y; by_cases hy : y = 0
  · subst hy; simp [ext_zero]
  · simp [ext_of_ne _ hy]

lemma ext_one : ext (1 : Sph n → ℝ) = fun y => if y ≠ 0 then 1 else 0 := by
  funext y; by_cases hy : y = 0
  · subst hy; simp [ext_zero]
  · simp [ext_of_ne _ hy, hy]

end MarkovTriple.BGL.SphereN
