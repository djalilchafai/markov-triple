import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Triple
import MarkovTriple.BGL.Instances.SphereN.Curv2
import MarkovTriple.BGL.Instances.Riemannian.R26.AtlasTriple

/-!
# `Sph 2` versus the circle `𝕋 = ℝ/ℤ` (Round 29, stream R, R3): the map `κ` and the operators

`κ(t) = (cos 2πt, sin 2πt)`.  For `f ∈ 𝒜₀(Sph 2)`, `E = ext f`: `D(f∘κ)(t) = Σ_a ∂_aE(γ) γ'_a` and, by Euler (`x·∇E = 0`,
`Σ x_a x_c ∂_a∂_cE = 0`), `Γ_𝕋 = (2π)² Γ`, `L_𝕋 = (2π)² L` (the circle `𝕋` has length `1`, the unit circle `2π`).
-/

open MeasureTheory Filter Topology
open scoped Real

namespace MarkovTriple.BGL.SphereN.Atlas

open LebesgueRd (dd Lf Gf)
open MarkovTriple.Sanity.Circle

/-- Euler relation (degree 0), any dimension -/
lemma euler_zero {n : ℕ} {f : Sph n → ℝ} (hf : f ∈ A₀S n) {x : Fin n → ℝ} (hx : x ≠ 0) :
    ∑ a, x a * dd a (ext f) x = 0 := by
  have := euler (show SmO (ext f) from hf) (hom_ext f) hx
  simpa using this

/-- second Euler relation (degree `-1` for the gradient), any dimension -/
lemma euler_two {n : ℕ} {f : Sph n → ℝ} (hf : f ∈ A₀S n) {x : Fin n → ℝ} (hx : x ≠ 0) (a : Fin n) :
    ∑ c, x c * dd c (dd a (ext f)) x = - dd a (ext f) x := by
  have hE : SmO (ext f) := hf
  have := euler (hE.ddO a) (hom_dd hE (hom_ext f) a) hx
  simpa using this

/-- the curve `t ↦ (cos 2πt, sin 2πt)` -/
noncomputable def γ (t : ℝ) : Fin 2 → ℝ := ![Real.cos (2 * π * t), Real.sin (2 * π * t)]

/-- its velocity -/
noncomputable def γ' (t : ℝ) : Fin 2 → ℝ := ![-(2 * π) * Real.sin (2 * π * t), (2 * π) * Real.cos (2 * π * t)]

lemma γ_ne (t : ℝ) : γ t ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [γ, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply] at h0 h1
  have := Real.cos_sq_add_sin_sq (2 * π * t)
  rw [h0, h1] at this
  norm_num at this

lemma γ_sq (t : ℝ) : γ t 0 ^ 2 + γ t 1 ^ 2 = 1 := by
  simp [γ, Real.cos_sq_add_sin_sq]

lemma hasDerivAt_γ (t : ℝ) : HasDerivAt γ (γ' t) t := by
  rw [hasDerivAt_pi]
  intro a
  fin_cases a
  · have h : HasDerivAt (fun x => Real.cos (2 * π * x)) (-Real.sin (2 * π * t) * (2 * π * 1)) t :=
      ((hasDerivAt_id t).const_mul (2 * π)).cos
    exact h.congr_deriv (by simp [γ']; ring)
  · have h : HasDerivAt (fun x => Real.sin (2 * π * x)) (Real.cos (2 * π * t) * (2 * π * 1)) t :=
      ((hasDerivAt_id t).const_mul (2 * π)).sin
    exact h.congr_deriv (by simp [γ']; ring)

/-- the point `κ x` of `Sph 2` -/
noncomputable def κ (x : 𝕋) : Sph 2 :=
  ⟨(WithLp.toLp 2 ![cC x, sC x] : Ee 2), by
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq]
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    simp [Fin.sum_univ_two, cC_coe, sC_coe, Real.cos_sq_add_sin_sq]⟩

lemma cv_κ (t : ℝ) : cv ((κ (t : 𝕋) : Sph 2) : Ee 2) = γ t := by
  funext a
  fin_cases a
  · simp [κ, cv, γ, cC_coe]
  · simp [κ, cv, γ, sC_coe]

lemma lift_κ (f : Sph 2 → ℝ) : (fun t : ℝ => f (κ (t : 𝕋))) = fun t => ext f (γ t) := by
  funext t
  rw [← cv_κ, ext_cv]

lemma hasDerivAt_Eγ {E : (Fin 2 → ℝ) → ℝ} (hE : SmO E) (t : ℝ) :
    HasDerivAt (fun s => E (γ s)) (∑ a, dd a E (γ t) * γ' t a) t := by
  have h1 : HasFDerivAt E (fderiv ℝ E (γ t)) (γ t) := (hE.differentiableAt (γ_ne t)).hasFDerivAt
  have h := h1.comp_hasDerivAt t (hasDerivAt_γ t)
  rw [MarkovTriple.BGL.Lebesgue.clm_pi_apply (fderiv ℝ E (γ t)) (γ' t)] at h
  show HasDerivAt (E ∘ γ) _ t
  refine HasDerivAt.congr_deriv h (Finset.sum_congr rfl fun a _ => ?_)
  unfold dd; ring

lemma contDiff_γ : ContDiff ℝ (⊤ : ℕ∞) γ := by
  refine contDiff_pi.2 fun a => ?_
  fin_cases a
  · show ContDiff ℝ _ (fun t : ℝ => Real.cos (2 * π * t))
    exact Real.contDiff_cos.comp (contDiff_const.mul contDiff_id)
  · show ContDiff ℝ _ (fun t : ℝ => Real.sin (2 * π * t))
    exact Real.contDiff_sin.comp (contDiff_const.mul contDiff_id)

theorem circle_A₀ {f : Sph 2 → ℝ} (hf : f ∈ A₀S 2) : (fun x => f (κ x)) ∈ A₀ := by
  rw [mem_A₀, lift_κ]
  exact (show SmO (ext f) from hf).comp_contDiff contDiff_γ γ_ne

/-- its acceleration -/
noncomputable def γ'' (t : ℝ) : Fin 2 → ℝ :=
  ![-(2 * π) * ((2 * π) * Real.cos (2 * π * t)), (2 * π) * (-(2 * π) * Real.sin (2 * π * t))]

lemma hasDerivAt_γ' (t : ℝ) : HasDerivAt γ' (γ'' t) t := by
  rw [hasDerivAt_pi]
  intro a
  fin_cases a
  · have h : HasDerivAt (fun x => -(2 * π) * Real.sin (2 * π * x))
        (-(2 * π) * (Real.cos (2 * π * t) * (2 * π * 1))) t :=
      (((hasDerivAt_id t).const_mul (2 * π)).sin).const_mul (-(2 * π))
    exact h.congr_deriv (by simp [γ'']; ring)
  · have h : HasDerivAt (fun x => (2 * π) * Real.cos (2 * π * x))
        ((2 * π) * (-Real.sin (2 * π * t) * (2 * π * 1))) t :=
      (((hasDerivAt_id t).const_mul (2 * π)).cos).const_mul (2 * π)
    exact h.congr_deriv (by simp [γ'']; ring)

lemma DG_coe {f : Sph 2 → ℝ} (hf : f ∈ A₀S 2) (t : ℝ) :
    D (fun x => f (κ x)) (t : 𝕋) = ∑ a, dd a (ext f) (γ t) * γ' t a := by
  rw [D_coe (circle_A₀ hf), lift_κ]
  exact (hasDerivAt_Eγ (show SmO (ext f) from hf) t).deriv

lemma γ_zero (t : ℝ) : γ t 0 = Real.cos (2 * π * t) := rfl
lemma γ_one (t : ℝ) : γ t 1 = Real.sin (2 * π * t) := rfl
lemma γ'_zero (t : ℝ) : γ' t 0 = -(2 * π) * Real.sin (2 * π * t) := rfl
lemma γ'_one (t : ℝ) : γ' t 1 = (2 * π) * Real.cos (2 * π * t) := rfl
lemma γ''_zero (t : ℝ) : γ'' t 0 = -(2 * π) * ((2 * π) * Real.cos (2 * π * t)) := rfl
lemma γ''_one (t : ℝ) : γ'' t 1 = (2 * π) * (-(2 * π) * Real.sin (2 * π * t)) := rfl

theorem circle_Γ {f h : Sph 2 → ℝ} (hf : f ∈ A₀S 2) (hh : h ∈ A₀S 2) (x : 𝕋) :
    Gc (fun x => f (κ x)) (fun x => h (κ x)) x = (2 * π) ^ 2 * ΓS f h (κ x) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  simp only [Gc, DG_coe hf, DG_coe hh]
  unfold ΓS Gf
  rw [cv_κ]
  have h1 := euler_zero hf (γ_ne t)
  have h2 := euler_zero hh (γ_ne t)
  simp only [Fin.sum_univ_two, γ_zero, γ_one, γ'_zero, γ'_one] at h1 h2 ⊢
  have hsc := Real.cos_sq_add_sin_sq (2 * π * t)
  linear_combination (2 * π) ^ 2 * ((dd 0 (ext f) (γ t) * dd 0 (ext h) (γ t) + dd 1 (ext f) (γ t) * dd 1 (ext h) (γ t)) * hsc
    - (Real.cos (2 * π * t) * dd 0 (ext h) (γ t) + Real.sin (2 * π * t) * dd 1 (ext h) (γ t)) * h1)

theorem circle_L {f : Sph 2 → ℝ} (hf : f ∈ A₀S 2) (x : 𝕋) :
    Lc (fun x => f (κ x)) x = (2 * π) ^ 2 * LS f (κ x) := by
  obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hE : SmO (ext f) := hf
  have hD : D (fun x => f (κ x)) ∈ A₀ := D_mem_A₀ (circle_A₀ hf)
  have e1 : (fun u : ℝ => D (fun x => f (κ x)) (u : 𝕋)) = fun u => ∑ a, dd a (ext f) (γ u) * γ' u a :=
    funext (DG_coe hf)
  have hder : HasDerivAt (fun u : ℝ => ∑ a, dd a (ext f) (γ u) * γ' u a)
      (∑ a, ((∑ c, dd c (dd a (ext f)) (γ t) * γ' t c) * γ' t a + dd a (ext f) (γ t) * γ'' t a)) t := by
    refine HasDerivAt.fun_sum fun a _ => ?_
    have h1 := hasDerivAt_Eγ (hE.ddO a) t
    have h2 : HasDerivAt (fun u => γ' u a) (γ'' t a) t := (hasDerivAt_pi.1 (hasDerivAt_γ' t)) a
    exact h1.mul h2
  have h2 := euler_two hf (γ_ne t)
  unfold Lc LS Lf
  rw [D_coe hD, e1, hder.deriv, cv_κ]
  simp only [Fin.sum_univ_two, γ_zero, γ_one, γ'_zero, γ'_one, γ''_zero, γ''_one] at h2 ⊢
  have h20 := h2 0
  have h21 := h2 1
  have hsc := Real.cos_sq_add_sin_sq (2 * π * t)
  linear_combination (2 * π) ^ 2 * (-(Real.cos (2 * π * t) * h20) - Real.sin (2 * π * t) * h21
    + (dd 0 (dd 0 (ext f)) (γ t) + dd 1 (dd 1 (ext f)) (γ t)) * hsc)

lemma κ_coord0 (x : 𝕋) : ((κ x : Sph 2) : Ee 2) 0 = cC x := rfl
lemma κ_coord1 (x : 𝕋) : ((κ x : Sph 2) : Ee 2) 1 = sC x := rfl

lemma coe_toCircle (x : 𝕋) : ((AddCircle.toCircle x : Circle) : ℂ) = fourier 1 x := by
  rw [fourier_one]

theorem κ_injective : Function.Injective κ := by
  intro x y hxy
  have h0 : cC x = cC y := by
    have := congrArg (fun p : Sph 2 => ((p : Ee 2)) 0) hxy
    simpa [κ_coord0] using this
  have h1 : sC x = sC y := by
    have := congrArg (fun p : Sph 2 => ((p : Ee 2)) 1) hxy
    simpa [κ_coord1] using this
  have hz : fourier 1 x = fourier 1 y := Complex.ext h0 h1
  have hc : AddCircle.toCircle x = AddCircle.toCircle y := by
    apply Circle.ext
    rw [coe_toCircle, coe_toCircle, hz]
  have e := AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero
  have hh : ∀ z : 𝕋, AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero z = AddCircle.toCircle z :=
    fun z => AddCircle.homeomorphCircle_apply _ z
  exact (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).injective (by rw [hh, hh]; exact hc)

theorem κ_surjective : Function.Surjective κ := by
  intro p
  have hp : ((p : Ee 2) 0) ^ 2 + ((p : Ee 2) 1) ^ 2 = 1 := by
    have h := p.2
    rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq] at h
    rw [Real.sqrt_eq_one] at h
    simpa [Fin.sum_univ_two] using h
  have hn : (⟨(p : Ee 2) 0, (p : Ee 2) 1⟩ : ℂ) ∈ Metric.sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_def, Complex.normSq_apply]
    simp only [Real.sqrt_eq_one]
    nlinarith [hp]
  let z : Circle := ⟨⟨(p : Ee 2) 0, (p : Ee 2) 1⟩, hn⟩
  obtain ⟨x, hx⟩ := (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).surjective z
  rw [AddCircle.homeomorphCircle_apply] at hx
  refine ⟨x, ?_⟩
  apply Subtype.ext
  apply WithLp.ofLp_injective
  funext a
  have hz := congrArg (fun w : Circle => (w : ℂ)) hx
  simp only [coe_toCircle] at hz
  fin_cases a
  · show cC x = _
    have := congrArg Complex.re hz
    simpa [cC, z] using this
  · show sC x = _
    have := congrArg Complex.im hz
    simpa [sC, z] using this

theorem circle_atlasDiff {f h : Sph 2 → ℝ} (hf : f ∈ A₀S 2) (hh : h ∈ A₀S 2) (x : 𝕋) :
    MarkovTriple.BGL.Instances.Riemannian.R26.atlasDiff.Γ (fun x => f (κ x)) (fun x => h (κ x)) x =
        (2 * π) ^ 2 * ΓS f h (κ x) ∧
    MarkovTriple.BGL.Instances.Riemannian.R26.atlasDiff.L (fun x => f (κ x)) x =
        (2 * π) ^ 2 * LS f (κ x) := by
  refine ⟨?_, ?_⟩
  · rw [MarkovTriple.BGL.Instances.Riemannian.R26.atlasDiff_Γ (circle_A₀ hf) (circle_A₀ hh)]
    exact circle_Γ hf hh x
  · rw [MarkovTriple.BGL.Instances.Riemannian.R26.atlasDiff_L (circle_A₀ hf)]
    exact circle_L hf x

end MarkovTriple.BGL.SphereN.Atlas
