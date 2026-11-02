import Mathlib
import MarkovTriple.BGL.Instances.Sphere.Compact

/-!
# `CD(2,3)` on the zonal sphere `S³` (Bakry–Émery: `CD(n-1,n)`, `n = 3`)

`Γ₂(f) = F''² + 2 (F'/sin θ)²` exactly (all of `𝒜`, everywhere), hence
`Γ₂(f) - 2Γ(f) - (L f)²/3 = (2/3)(F'' - cot θ F')² ≥ 0`.
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.Sphere

/-- the `θ`-side computation of `Γ₂`. -/
lemma Γ₂_theta {F : ℝ → ℝ} (hF : Sm F) (eF : EP F) (θ : ℝ) :
    (dL (dG F F) θ - dG F (dL F) θ - dG (dL F) F θ) / 2 =
      deriv (deriv F) θ ^ 2 + 2 * Dq F θ ^ 2 := by
  have hD : Sm (Dq F) := sm_Dq hF eF
  have hF1 : Sm (deriv F) := hF.deriv'
  have hF2 : Sm (deriv (deriv F)) := hF.deriv'.deriv'
  have hK : Sm (dG F F) := sm_dG hF hF
  have eK : EP (dG F F) := ep_dG eF eF
  have e1 : deriv F = fun θ => sin θ * Dq F θ := funext fun θ => (sin_mul_Dq (hF0 hF eF) θ).symm
  -- second derivative of `F` through `Dq`
  have eb : deriv (deriv F) θ = cos θ * Dq F θ + sin θ * deriv (Dq F) θ := by
    have h := ((hasDerivAt_sin θ).fun_mul (hD.hasDerivAt θ)).deriv
    rw [e1]; simpa using h
  -- derivative of `K = F'²`
  have hKd : deriv (dG F F) = fun y => 2 * (deriv F y * deriv (deriv F) y) := by
    funext y
    have := ((hF1.hasDerivAt y).fun_mul (hF1.hasDerivAt y)).deriv
    show deriv (fun θ => deriv F θ * deriv F θ) y = _
    rw [this]; ring
  have hKdd : deriv (deriv (dG F F)) θ =
      2 * (deriv (deriv F) θ * deriv (deriv F) θ + deriv F θ * deriv (deriv (deriv F)) θ) := by
    rw [hKd]
    have := ((hF1.hasDerivAt θ).mul (hF2.hasDerivAt θ)).const_mul 2
    simpa using this.deriv
  -- `Dq K`
  have hDqK : Dq (dG F F) = fun y => 2 * Dq F y * deriv (deriv F) y := by
    refine eq_of_sin_mul_eq (sm_Dq hK eK).continuous
      ((continuous_const.mul hD.continuous).mul hF2.continuous) fun y => ?_
    rw [sin_mul_Dq (hF0 hK eK) y, hKd]
    have := sin_mul_Dq (hF0 hF eF) y
    calc 2 * (deriv F y * deriv (deriv F) y) = 2 * (sin y * Dq F y) * deriv (deriv F) y := by
          rw [this]; ring
      _ = _ := by ring
  -- derivative of `dL F`
  have hLd : deriv (dL F) θ = deriv (deriv (deriv F)) θ +
      2 * (-sin θ * Dq F θ + cos θ * deriv (Dq F) θ) := by
    have h1 := (hF2.hasDerivAt θ)
    have h2 := ((hasDerivAt_cos θ).fun_mul (hD.hasDerivAt θ)).const_mul 2
    have := (h1.fun_add h2).deriv
    have e : dL F = fun y => deriv (deriv F) y + 2 * (cos y * Dq F y) := rfl
    rw [e, this]
  have ea : deriv F θ = sin θ * Dq F θ := (sin_mul_Dq (hF0 hF eF) θ).symm
  have hsc := sin_sq_add_cos_sq θ
  have hLK : dL (dG F F) θ = 2 * (deriv (deriv F) θ ^ 2 + deriv F θ * deriv (deriv (deriv F)) θ) +
      2 * (cos θ * (2 * Dq F θ * deriv (deriv F) θ)) := by
    unfold dL
    rw [hKdd, congrFun hDqK θ]; ring
  have hGL : dG F (dL F) θ = deriv F θ * deriv (dL F) θ := rfl
  have hGL' : dG (dL F) F θ = deriv F θ * deriv (dL F) θ := by
    show deriv (dL F) θ * deriv F θ = _; ring
  rw [hLK, hGL, hGL', hLd]
  linear_combination (2 * cos θ * Dq F θ) * eb +
    (2 * (sin θ * Dq F θ - cos θ * deriv (Dq F) θ)) * ea + (2 * Dq F θ ^ 2) * hsc


/-- `Γ₂(f) = F''² + 2 (Dq F)²` on `Zon`, for every `f ∈ 𝒜` and every point. -/
lemma Γ₂_eq {f : Zon → ℝ} (hf : f ∈ AZ) (x : Zon) :
    sT.Γ₂ f f x = deriv (deriv (ext f)) (arc x) ^ 2 + 2 * Dq (ext f) (arc x) ^ 2 := by
  have hF : Sm (ext f) := hf
  have hΓ : sT.ΓA f f = GZ f f := ΓA_eq_GZ hf hf
  have hΓ1 : sT.ΓA f (LZ f) = GZ f (LZ f) := ΓA_eq_GZ hf (LZ_mem hf)
  have hΓ2 : sT.ΓA (LZ f) f = GZ (LZ f) f := ΓA_eq_GZ (LZ_mem hf) hf
  show (LZ (sT.ΓA f f) x - sT.ΓA f (LZ f) x - sT.ΓA (LZ f) f x) / 2 = _
  rw [hΓ, hΓ1, hΓ2, LZ_apply, GZ_apply, GZ_apply, ext_GZ hf hf, ext_LZ]
  exact Γ₂_theta hF (ep_ext f) (arc x)

/-- pointwise values of `ΓA f f` and `L f`. -/
lemma ΓA_apply {f : Zon → ℝ} (hf : f ∈ AZ) (x : Zon) :
    sT.ΓA f f x = deriv (ext f) (arc x) * deriv (ext f) (arc x) := by
  rw [ΓA_eq_GZ hf hf]; rfl

lemma L_apply (f : Zon → ℝ) (x : Zon) :
    sT.L f x = deriv (deriv (ext f)) (arc x) + 2 * (cos (arc x) * Dq (ext f) (arc x)) := rfl

lemma inv_toReal_le {n : ℝ≥0∞} (hn : 3 ≤ n) : (n⁻¹).toReal ≤ 1 / 3 := by
  have h : n⁻¹ ≤ (3 : ℝ≥0∞)⁻¹ := ENNReal.inv_le_inv.2 hn
  have := ENNReal.toReal_mono (by simp) h
  have e : ((3 : ℝ≥0∞)⁻¹).toReal = 1 / 3 := by
    rw [ENNReal.toReal_inv]; simp
  rwa [e] at this

/-- **`CD(ρ, n)` on the zonal sphere `S³` for all `ρ ≤ 2`, `n ≥ 3`** (BGL Def. 3.3.14, all of `𝒜`);
in particular `CD(2,3)`, the sphere value `CD(n-1,n)` for `n = 3`. -/
theorem sphere_CD {ρ : ℝ} {n : ℝ≥0∞} (hρ : ρ ≤ 2) (hn : 3 ≤ n) : sCompact.toFullTriple.CD ρ n := by
  refine ⟨le_trans (by norm_num) hn, fun f hf => Eventually.of_forall fun x => ?_⟩
  have hf' : f ∈ AZ := hf
  show ρ * sT.ΓA f f x + (n⁻¹).toReal * (sT.L f x) ^ 2 ≤ sT.Γ₂ f f x
  rw [Γ₂_eq hf' x, ΓA_apply hf' x, L_apply]
  set a := deriv (ext f) (arc x) with ha
  set b := deriv (deriv (ext f)) (arc x) with hb
  set D := Dq (ext f) (arc x) with hD
  set c := cos (arc x) with hc
  have hsa : a = sin (arc x) * D := (sin_mul_Dq (hF0 (show Sm (ext f) from hf') (ep_ext f)) (arc x)).symm
  have hsc := sin_sq_add_cos_sq (arc x)
  have hκ0 : 0 ≤ (n⁻¹).toReal := ENNReal.toReal_nonneg
  have hκ := inv_toReal_le hn
  have h1 : ρ * (a * a) ≤ 2 * (a * a) := mul_le_mul_of_nonneg_right hρ (mul_self_nonneg a)
  have h2 : (n⁻¹).toReal * (b + 2 * (c * D)) ^ 2 ≤ 1 / 3 * (b + 2 * (c * D)) ^ 2 :=
    mul_le_mul_of_nonneg_right hκ (sq_nonneg _)
  have h3 : 2 * (a * a) + 1 / 3 * (b + 2 * (c * D)) ^ 2 ≤ b ^ 2 + 2 * D ^ 2 := by
    have e : a * a = sin (arc x) ^ 2 * D ^ 2 := by rw [hsa]; ring
    rw [e]
    have : 2 * D ^ 2 = 2 * (sin (arc x) ^ 2 + c ^ 2) * D ^ 2 := by rw [hc]; rw [hsc]; ring
    nlinarith [sq_nonneg (b - c * D)]
  linarith

/-- `CD(2,3)`. -/
theorem sphere_CD_two_three : sCompact.toFullTriple.CD 2 3 := sphere_CD le_rfl le_rfl

/-- Non-degeneracy: `Γ ≠ 0` (witness `f(x) = x`, i.e. `F = cos`). -/
theorem sphere_Γ_ne_zero : ∃ f ∈ sCompact.A₀, sCompact.Γ f f ≠ 0 := by
  have hf : (fun x : Zon => x.1) ∈ AZ := by
    show Sm (ext (fun x : Zon => x.1))
    exact (by simpa [ext, cosZ] using contDiff_cos : Sm fun θ => cos θ)
  refine ⟨fun x : Zon => x.1, hf, fun h => ?_⟩
  have := congrFun h ⟨0, by norm_num, by norm_num⟩
  have e : ext (fun x : Zon => x.1) = cos := by funext θ; simp [ext, cosZ]
  have h0 : arc ⟨0, by norm_num, by norm_num⟩ = π / 2 := by simp [arc, Real.arccos_zero]
  have : sT.Γ (fun x : Zon => x.1) (fun x : Zon => x.1) ⟨0, by norm_num, by norm_num⟩ = 0 := this
  simp only [sT, GZ, mk, dG, e, h0, Real.deriv_cos] at this
  simp at this

end MarkovTriple.BGL.Instances.Sphere
