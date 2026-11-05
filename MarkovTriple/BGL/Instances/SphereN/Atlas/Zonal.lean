import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Extrinsic
import MarkovTriple.BGL.Instances.SphereN.ExtrinsicL
import MarkovTriple.BGL.Instances.Sphere.Compact

/-!
# The zonal reduction (Round 29, stream R, R4)

For `f(x) = φ(x₀)` on `Sph n`: `Γ(f,g) = (1-x₀²) φ'ψ'` and `L f = (1-x₀²) φ'' - (n-1) x₀ φ'` (from the extrinsic formulas of R28).
For `n = 4` (`S³ ⊂ ℝ⁴`, Gegenbauer `λ = 1`, weight `(1-x²)^{1/2}`) these are the operators `GZ`, `LZ` of the library zonal sphere `Instances/Sphere/*`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.SphereN.Atlas

open LebesgueRd (dd Lf Gf)

lemma dd_zonal {n : ℕ} [NeZero n] {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin n) (y : Fin n → ℝ) :
    dd i (fun z : Fin n → ℝ => φ (z 0)) y = if i = 0 then deriv φ (y 0) else 0 := by
  have h1 : HasDerivAt φ (deriv φ (y 0)) (y 0) := ((hφ.differentiable (by simp)) _).hasDerivAt
  have h2 : HasFDerivAt (fun z : Fin n → ℝ => φ (z 0))
      (deriv φ (y 0) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) (0 : Fin n)) y :=
    HasDerivAt.comp_hasFDerivAt (f := fun z : Fin n → ℝ => z 0) y h1 (hasFDerivAt_apply (0 : Fin n) y)
  unfold dd
  rw [h2.fderiv]
  simp [Pi.single_apply, eq_comm]

lemma zonal_smooth {n : ℕ} [NeZero n] {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin n → ℝ => φ (z 0)) :=
  hφ.comp (contDiff_apply ℝ ℝ 0)

lemma deriv_smooth {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ (⊤ : ℕ∞) (deriv φ) :=
  (contDiff_infty_iff_deriv.1 hφ).2

theorem zonal_Γ {n : ℕ} [NeZero n] {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (x : Sph n) :
    ΓS (fun z : Sph n => φ (cv (z : Ee n) 0)) (fun z : Sph n => ψ (cv (z : Ee n) 0)) x =
      (1 - cv (x : Ee n) 0 ^ 2) * deriv φ (cv (x : Ee n) 0) * deriv ψ (cv (x : Ee n) 0) := by
  rw [ΓS_extrinsic (F := fun z : Fin n → ℝ => φ (z 0)) (G := fun z : Fin n → ℝ => ψ (z 0))
    (zonal_smooth hφ) (zonal_smooth hψ) x]
  simp only [dd_zonal hφ, dd_zonal hψ]
  simp [mul_ite, ite_mul]
  ring

theorem zonal_L {n : ℕ} [NeZero n] {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Sph n) :
    LS (fun z : Sph n => φ (cv (z : Ee n) 0)) x =
      (1 - cv (x : Ee n) 0 ^ 2) * deriv (deriv φ) (cv (x : Ee n) 0)
        - ((n : ℝ) - 1) * cv (x : Ee n) 0 * deriv φ (cv (x : Ee n) 0) := by
  rw [LS_extrinsic (F := fun z : Fin n → ℝ => φ (z 0)) (zonal_smooth hφ) x]
  have e : ∀ j : Fin n, dd j (fun z : Fin n → ℝ => φ (z 0)) =
      fun z => if j = 0 then deriv φ (z 0) else 0 := fun j => funext fun z => dd_zonal hφ j z
  have e2 : ∀ (i j : Fin n) (z : Fin n → ℝ), dd i (dd j (fun z : Fin n → ℝ => φ (z 0))) z =
      if j = 0 then (if i = 0 then deriv (deriv φ) (z 0) else 0) else 0 := by
    intro i j z
    rw [e j]
    by_cases hj : j = 0
    · simp only [hj, ite_true]
      exact dd_zonal (deriv_smooth hφ) i z
    · simp only [hj, ite_false]
      exact congrFun (LebesgueRd.dd_const (0 : ℝ) i) z
  unfold Lf
  simp only [e2, dd_zonal hφ]
  simp [mul_ite]
  ring

/-! ### the library zonal sphere `S³` (`n = 4`) -/

section lib

open MarkovTriple.BGL.Instances.Sphere

lemma lib_ext (φ : ℝ → ℝ) : MarkovTriple.BGL.Instances.Sphere.ext (fun t : Zon => φ t.1) =
    fun θ => φ (Real.cos θ) := rfl

lemma hasDerivAt_zon {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (θ : ℝ) :
    HasDerivAt (fun θ => φ (Real.cos θ)) (-(Real.sin θ) * deriv φ (Real.cos θ)) θ := by
  have h1 : HasDerivAt φ (deriv φ (Real.cos θ)) (Real.cos θ) := ((hφ.differentiable (by simp)) _).hasDerivAt
  have := h1.comp θ (Real.hasDerivAt_cos θ)
  exact this.congr_deriv (by ring)

lemma deriv_zon {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (θ : ℝ) :
    deriv (fun θ => φ (Real.cos θ)) θ = -(Real.sin θ) * deriv φ (Real.cos θ) :=
  (hasDerivAt_zon hφ θ).deriv

lemma deriv2_zon {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (θ : ℝ) :
    deriv (deriv (fun θ => φ (Real.cos θ))) θ =
      -(Real.cos θ) * deriv φ (Real.cos θ) + Real.sin θ ^ 2 * deriv (deriv φ) (Real.cos θ) := by
  have e : deriv (fun θ => φ (Real.cos θ)) = fun θ => -(Real.sin θ) * deriv φ (Real.cos θ) :=
    funext (deriv_zon hφ)
  rw [e]
  have h1 : HasDerivAt (deriv φ) (deriv (deriv φ) (Real.cos θ)) (Real.cos θ) :=
    (((deriv_smooth hφ).differentiable (by simp)) _).hasDerivAt
  have h2 := (h1.comp θ (Real.hasDerivAt_cos θ))
  have h3 : HasDerivAt (fun θ => -Real.sin θ * deriv φ (Real.cos θ))
      (-Real.cos θ * deriv φ (Real.cos θ) + (-Real.sin θ) * (deriv (deriv φ) (Real.cos θ) * -Real.sin θ)) θ :=
    (Real.hasDerivAt_sin θ).neg.mul h2
  rw [h3.deriv]
  ring

lemma sin_sq_arc (x : Zon) : Real.sin (arc x) ^ 2 = 1 - x.1 ^ 2 := by
  have := Real.sin_sq_add_cos_sq (arc x)
  have hc : Real.cos (arc x) = x.1 := Real.cos_arccos x.2.1 x.2.2
  rw [hc] at this
  linarith

lemma cos_arc (x : Zon) : Real.cos (arc x) = x.1 := Real.cos_arccos x.2.1 x.2.2

theorem GZ_zonal {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Zon) :
    GZ (fun t : Zon => φ t.1) (fun t : Zon => ψ t.1) x = (1 - x.1 ^ 2) * deriv φ x.1 * deriv ψ x.1 := by
  rw [GZ_apply, lib_ext, lib_ext]
  unfold dG
  rw [deriv_zon hφ, deriv_zon hψ, cos_arc]
  have := sin_sq_arc x
  linear_combination (deriv φ x.1 * deriv ψ x.1) * this

theorem LZ_zonal {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Zon) :
    LZ (fun t : Zon => φ t.1) x =
      (1 - x.1 ^ 2) * deriv (deriv φ) x.1 - 3 * x.1 * deriv φ x.1 := by
  rw [LZ_apply, lib_ext]
  unfold dL
  have hDq : Dq (fun θ => φ (Real.cos θ)) (arc x) = -deriv φ (Real.cos (arc x)) := by
    unfold Dq
    by_cases hs : Real.sin (arc x) = 0
    · have hc : Real.cos (arc x) ≠ 0 := by
        intro h0
        have := Real.sin_sq_add_cos_sq (arc x)
        rw [hs, h0] at this
        norm_num at this
      simp only [hs, ↓reduceIte]
      rw [deriv2_zon hφ, hs]
      field_simp
      ring
    · simp only [hs, ↓reduceIte]
      rw [deriv_zon hφ]
      field_simp
  rw [deriv2_zon hφ, hDq, cos_arc]
  have := sin_sq_arc x
  linear_combination (deriv (deriv φ) x.1) * this

/-- **the zonal reduction**: the library zonal operators `GZ`, `LZ` of `S³` are `ΓS`, `LS` of `Sph 4` on zonal functions. -/
theorem zonal_lib {φ ψ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (x : Zon) (y : Sph 4) (hy : cv (y : Ee 4) 0 = x.1) :
    GZ (fun t : Zon => φ t.1) (fun t : Zon => ψ t.1) x =
        ΓS (fun z : Sph 4 => φ (cv (z : Ee 4) 0)) (fun z : Sph 4 => ψ (cv (z : Ee 4) 0)) y ∧
      LZ (fun t : Zon => φ t.1) x = LS (fun z : Sph 4 => φ (cv (z : Ee 4) 0)) y := by
  refine ⟨?_, ?_⟩
  · rw [GZ_zonal hφ hψ, zonal_Γ hφ hψ, hy]
  · rw [LZ_zonal hφ, zonal_L hφ, hy]
    norm_num

end lib

end MarkovTriple.BGL.SphereN.Atlas
