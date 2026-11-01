import Mathlib
import MarkovTriple.Divergences.Wasserstein

/-!
# Position-scale transport and the Gelbrich/Bures formula for `W₂²`

Ported from cutoff-fastdiff (`Cutfast/Wasserstein.lean`, Lemma 2.1, and `Cutfast/Elliptic.lean`,
Lemma 2.2).  The source quantified couplings over probability measures with the given marginals
(`wassersteinSqP` below, kept verbatim for the proofs); the public statements
`wassersteinSq_map_affine` and `wassersteinSq_elliptic` are stated for the unified
`MarkovTriple.wassersteinSq` through `wassersteinSq_eq_wassersteinSqP`.
-/

namespace MarkovTriple

namespace Gelbrich

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace

/-- Euclidean space `ℝᵈ`. -/
abbrev Eu (d : ℕ) := EuclideanSpace ℝ (Fin d)

/-- The cutoff-fastdiff form of `W₂²`: infimum over probability couplings. -/
noncomputable def wassersteinSqP {d : ℕ} (μ ν : Measure (Eu d)) : ℝ≥0∞ :=
  ⨅ (γ : Measure (Eu d × Eu d)) (_ : IsProbabilityMeasure γ)
    (_ : γ.map Prod.fst = μ) (_ : γ.map Prod.snd = ν), ∫⁻ p, edist p.1 p.2 ^ 2 ∂γ

namespace Wasserstein

variable {d : ℕ}

lemma edist_sq_eq (x y : Eu d) : edist x y ^ 2 = ENNReal.ofReal (‖x - y‖ ^ 2) := by
  rw [edist_dist, dist_eq_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma measurable_cost : Measurable (fun p : Eu d × Eu d => edist p.1 p.2 ^ 2) :=
  (measurable_fst.edist measurable_snd).pow_const 2

variable {α : Type*} [MeasurableSpace α] {ρ : Measure α}

/-- The inner product of two square-integrable functions is integrable. -/
lemma integrable_inner {f g : α → Eu d} (hf : AEStronglyMeasurable f ρ)
    (hg : AEStronglyMeasurable g ρ) (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ρ)
    (hg2 : Integrable (fun a => ‖g a‖ ^ 2) ρ) :
    Integrable (fun a => ⟪f a, g a⟫_ℝ) ρ := by
  refine (hf2.add hg2).mono' (hf.inner hg) (ae_of_all _ fun a => ?_)
  have h1 := abs_real_inner_le_norm (f a) (g a)
  rw [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [norm_nonneg (f a), norm_nonneg (g a), sq_nonneg (‖f a‖ - ‖g a‖)]

/-- An affine image of a square-integrable function is square-integrable. -/
lemma integrable_sq_clm [IsFiniteMeasure ρ] {f : α → Eu d} (hf : AEStronglyMeasurable f ρ)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ρ) (L : Eu d →L[ℝ] Eu d) (c : Eu d) :
    Integrable (fun a => ‖L (f a) + c‖ ^ 2) ρ := by
  refine ((hf2.const_mul (2 * ‖L‖ ^ 2)).add (integrable_const (2 * ‖c‖ ^ 2))).mono'
    (((L.continuous.comp_aestronglyMeasurable hf).add aestronglyMeasurable_const).norm.pow 2)
    (ae_of_all _ fun a => ?_)
  have h1 := norm_add_le (L (f a)) c
  have h2 := L.le_opNorm (f a)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h3 : ‖L (f a) + c‖ ≤ ‖L‖ * ‖f a‖ + ‖c‖ := by linarith
  have h4 : 0 ≤ ‖L (f a) + c‖ := norm_nonneg _
  rw [Pi.add_apply]
  nlinarith [sq_nonneg (‖L‖ * ‖f a‖ - ‖c‖), norm_nonneg c, mul_nonneg (norm_nonneg L)
    (norm_nonneg (f a))]

/-- A function with integrable squared norm on a finite measure space is integrable. -/
lemma integrable_of_sq [IsFiniteMeasure ρ] {f : α → Eu d} (hf : AEStronglyMeasurable f ρ)
    (hf2 : Integrable (fun a => ‖f a‖ ^ 2) ρ) : Integrable f ρ := by
  refine (hf2.add (integrable_const 1)).mono' hf (ae_of_all _ fun a => ?_)
  rw [Pi.add_apply]
  nlinarith [sq_nonneg (‖f a‖ - 1)]

/-- Fenchel–Young type inequality for a positive operator `P`:
`2⟪x, P w⟫ ≤ ⟪P x, x⟫ + ⟪P w, w⟫`. -/
lemma two_inner_le {P : Eu d →L[ℝ] Eu d} (hP : P.IsPositive) (x w : Eu d) :
    2 * ⟪x, P w⟫_ℝ ≤ ⟪P x, x⟫_ℝ + ⟪P w, w⟫_ℝ := by
  have h := hP.re_inner_nonneg_left (x - w)
  have hs := hP.inner_left_eq_inner_right w x
  simp only [RCLike.re_to_real, map_sub, inner_sub_left, inner_sub_right] at h
  have e1 : ⟪P x, w⟫_ℝ = ⟪w, P x⟫_ℝ := real_inner_comm _ _
  have e2 : ⟪P w, x⟫_ℝ = ⟪x, P w⟫_ℝ := real_inner_comm _ _
  linarith

/-- If `(A + δ • 1) w = A z` with `A` positive and `δ ≥ 0`, then
`⟪(A + δ • 1) w, w⟫ ≤ ⟪A z, z⟫`. -/
lemma inner_reg_le {A : Eu d →L[ℝ] Eu d} (hA : A.IsPositive) {δ : ℝ} (hδ : 0 ≤ δ)
    {w z : Eu d} (hwz : (A + δ • (1 : Eu d →L[ℝ] Eu d)) w = A z) :
    ⟪(A + δ • (1 : Eu d →L[ℝ] Eu d)) w, w⟫_ℝ ≤ ⟪A z, z⟫_ℝ := by
  have h := two_inner_le hA z w
  have hs := hA.inner_left_eq_inner_right z w
  have hB : ⟪(A + δ • (1 : Eu d →L[ℝ] Eu d)) w, w⟫_ℝ = ⟪A w, w⟫_ℝ + δ * ⟪w, w⟫_ℝ := by
    simp [inner_add_left, inner_smul_left]
  have hw : 0 ≤ ⟪w, w⟫_ℝ := real_inner_self_nonneg
  have hzw : ⟪A z, w⟫_ℝ = ⟪A w, w⟫_ℝ + δ * ⟪w, w⟫_ℝ := by rw [← hwz, hB]
  have e : ⟪A z, w⟫_ℝ = ⟪w, A z⟫_ℝ := real_inner_comm _ _
  rw [hB]
  nlinarith [mul_nonneg hδ hw]

/-- The key lower bound: for every coupling `γ` of `μ` and `T_#μ` and every `δ > 0`,
`∫ ‖x - T x‖² dμ - δ ∫ ‖x‖² dμ ≤ ∫ ‖x - y‖² dγ`. -/
lemma lower_bound (μ : Measure (Eu d)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖ ^ 2) μ) {A : Eu d →L[ℝ] Eu d} (hA : A.IsPositive) (h : Eu d)
    (γ : Measure (Eu d × Eu d)) [IsProbabilityMeasure γ] (h1 : γ.map Prod.fst = μ)
    (h2 : γ.map Prod.snd = μ.map fun x => A x + h) {δ : ℝ} (hδ : 0 < δ) :
    ∫ x, ‖x - (A x + h)‖ ^ 2 ∂μ - δ * ∫ x, ‖x‖ ^ 2 ∂μ ≤ ∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ := by
  set T : Eu d → Eu d := fun x => A x + h with hT
  set ν := μ.map T with hν
  have hTc : Continuous T := A.continuous.add continuous_const
  have hTm : Measurable T := hTc.measurable
  have hid : AEStronglyMeasurable (fun x : Eu d => x) μ := aestronglyMeasurable_id
  have hν2 : Integrable (fun y => ‖y‖ ^ 2) ν :=
    (integrable_map_measure (by fun_prop) hTm.aemeasurable).2 (integrable_sq_clm hid hμ A h)
  -- second moments of the marginals of `γ`
  have hγ1 : Integrable (fun p : Eu d × Eu d => ‖p.1‖ ^ 2) γ := by
    have : Integrable (fun x : Eu d => ‖x‖ ^ 2) (γ.map Prod.fst) := h1 ▸ hμ
    exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).1 this
  have hγ2 : Integrable (fun p : Eu d × Eu d => ‖p.2‖ ^ 2) γ := by
    have : Integrable (fun x : Eu d => ‖x‖ ^ 2) (γ.map Prod.snd) := h2 ▸ hν2
    exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).1 this
  -- the regularized operator and its inverse
  set B : Eu d →L[ℝ] Eu d := A + δ • (1 : Eu d →L[ℝ] Eu d) with hBdef
  have hBinner : ∀ x, ⟪B x, x⟫_ℝ = ⟪A x, x⟫_ℝ + δ * ‖x‖ ^ 2 := fun x => by
    simp [hBdef, inner_add_left, inner_smul_left]
  have hBpos : B.IsPositive := by
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · simp only [hBdef, ContinuousLinearMap.toLinearMap_add, ContinuousLinearMap.toLinearMap_smul,
        LinearMap.add_apply, LinearMap.smul_apply, ContinuousLinearMap.coe_coe,
        one_apply_eq_self, inner_add_left, inner_add_right, inner_smul_left,
        inner_smul_right]
      rw [hA.inner_left_eq_inner_right]
      simp
    · simp only [ContinuousLinearMap.reApplyInnerSelf, RCLike.re_to_real, hBinner]
      have := hA.re_inner_nonneg_left x
      simp only [RCLike.re_to_real] at this
      positivity
  have hBinj : Function.Injective (B : Eu d →ₗ[ℝ] Eu d) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h0 := hBinner x
    have hx' : B x = 0 := hx
    rw [hx', inner_zero_left] at h0
    have := hA.re_inner_nonneg_left x
    simp only [RCLike.re_to_real] at this
    have : ‖x‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x‖]
    simpa using this
  set e := LinearEquiv.ofInjectiveEndo (B : Eu d →ₗ[ℝ] Eu d) hBinj
  set C : Eu d →L[ℝ] Eu d := LinearMap.toContinuousLinearMap (e.symm : Eu d →ₗ[ℝ] Eu d)
  have hBC : ∀ y, B (C y) = y := fun y => e.apply_symm_apply y
  -- the two potentials
  set f₁ : Eu d → ℝ := fun x => ‖x‖ ^ 2 - ⟪B x, x⟫_ℝ - 2 * ⟪x, h⟫_ℝ with hf₁
  set f₂ : Eu d → ℝ := fun y => ‖y‖ ^ 2 - ⟪y - h, C (y - h)⟫_ℝ with hf₂
  have hf₁c : Continuous f₁ := by fun_prop
  have hf₂c : Continuous f₂ := by fun_prop
  have key : ∀ x y, f₁ x + f₂ y ≤ ‖x - y‖ ^ 2 := fun x y => by
    have := two_inner_le hBpos x (C (y - h))
    rw [hBC] at this
    simp only [hf₁, hf₂, inner_sub_right] at this ⊢
    rw [norm_sub_sq_real]
    linarith
  have key₂ : ∀ x, ‖T x‖ ^ 2 - ⟪A x, x⟫_ℝ ≤ f₂ (T x) := fun x => by
    have hw : B (C (A x)) = A x := hBC _
    have := inner_reg_le hA hδ.le hw
    rw [hw] at this
    have e : ⟪x, A x⟫_ℝ = ⟪A x, x⟫_ℝ := real_inner_comm _ _
    simp only [hf₂, hT, add_sub_cancel_right]
    linarith
  have key₁ : ∀ x, f₁ x + (‖T x‖ ^ 2 - ⟪A x, x⟫_ℝ) = ‖x - T x‖ ^ 2 - δ * ‖x‖ ^ 2 := fun x => by
    simp only [hf₁, hT, hBinner, norm_sub_sq_real, inner_add_right]
    rw [real_inner_comm (A x) x]
    ring
  -- integrability
  have hf₁i : Integrable f₁ μ := by
    refine (hμ.sub (integrable_inner (B.continuous.aestronglyMeasurable) hid ?_ hμ)).sub
      ((integrable_inner hid aestronglyMeasurable_const hμ (integrable_const _)).const_mul 2)
    simpa using integrable_sq_clm hid hμ B 0
  have hf₂i : Integrable f₂ ν := by
    have hidν : AEStronglyMeasurable (fun y : Eu d => y) ν := aestronglyMeasurable_id
    have h3 : Integrable (fun y => ‖y - h‖ ^ 2) ν := by
      simpa [sub_eq_add_neg] using integrable_sq_clm hidν hν2 1 (-h)
    have h4 : Integrable (fun y => ‖C (y - h)‖ ^ 2) ν := by
      simpa [sub_eq_add_neg] using integrable_sq_clm hidν hν2 C (-C h)
    exact hν2.sub (integrable_inner (by fun_prop) (by fun_prop) h3 h4)
  have hf₂Ti : Integrable (fun x => f₂ (T x)) μ :=
    (integrable_map_measure hf₂c.aestronglyMeasurable hTm.aemeasurable).1 hf₂i
  have hf₁γ : Integrable (fun p : Eu d × Eu d => f₁ p.1) γ := by
    have : Integrable f₁ (γ.map Prod.fst) := by rw [h1]; exact hf₁i
    exact this.comp_measurable measurable_fst
  have hf₂γ : Integrable (fun p : Eu d × Eu d => f₂ p.2) γ := by
    have : Integrable f₂ (γ.map Prod.snd) := by rw [h2]; exact hf₂i
    exact this.comp_measurable measurable_snd
  have hcost : Integrable (fun p : Eu d × Eu d => ‖p.1 - p.2‖ ^ 2) γ := by
    refine ((hγ1.add hγ2).const_mul 2).mono' (by fun_prop) (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
    have := norm_sub_le p.1 p.2
    nlinarith [norm_nonneg (p.1 - p.2), sq_nonneg (‖p.1‖ - ‖p.2‖)]
  have hI : Integrable (fun x => ‖x - T x‖ ^ 2) μ := by
    have := integrable_sq_clm hid hμ (1 - A) (-h)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [hT, sub_apply, one_apply_eq_self]
    congr 2
    abel
  have hTsq : Integrable (fun x => ‖T x‖ ^ 2 - ⟪A x, x⟫_ℝ) μ :=
    (integrable_sq_clm hid hμ A h).sub (integrable_inner (by fun_prop) hid
      (by simpa using integrable_sq_clm hid hμ A 0) hμ)
  -- integrate
  have e₁ : ∫ p, f₁ p.1 ∂γ = ∫ x, f₁ x ∂μ := by
    rw [← h1, integral_map measurable_fst.aemeasurable (h1 ▸ hf₁c.aestronglyMeasurable)]
  have e₂ : ∫ p, f₂ p.2 ∂γ = ∫ x, f₂ (T x) ∂μ := by
    have : ∫ x, f₂ (T x) ∂μ = ∫ y, f₂ y ∂ν :=
      (integral_map hTm.aemeasurable hf₂c.aestronglyMeasurable).symm
    rw [this, ← h2, integral_map measurable_snd.aemeasurable (h2 ▸ hf₂c.aestronglyMeasurable)]
  calc ∫ x, ‖x - (A x + h)‖ ^ 2 ∂μ - δ * ∫ x, ‖x‖ ^ 2 ∂μ
      = ∫ x, (f₁ x + (‖T x‖ ^ 2 - ⟪A x, x⟫_ℝ)) ∂μ := by
        simp_rw [key₁]
        rw [integral_sub hI (hμ.const_mul δ), integral_const_mul]
    _ ≤ ∫ x, (f₁ x + f₂ (T x)) ∂μ :=
        integral_mono (hf₁i.add hTsq) (hf₁i.add hf₂Ti) fun x => by
          simp only; linarith [key₂ x]
    _ = ∫ p, (f₁ p.1 + f₂ p.2) ∂γ := by
        rw [integral_add hf₁i hf₂Ti, integral_add hf₁γ hf₂γ, e₁, e₂]
    _ ≤ ∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ :=
        integral_mono (hf₁γ.add hf₂γ) hcost fun p => key p.1 p.2

end Wasserstein

open Wasserstein in
/-- Lemma 2.1: for a positive operator `A` and `h ∈ ℝᵈ`, the affine map `x ↦ A x + h` is
optimal, and `W₂²(μ, (A · + h)_#μ) = ∫ ‖(A - 1) x‖² dμ + 2⟪(A - 1) 𝔼 X, h⟫ + ‖h‖²`. -/
theorem wassersteinSqP_map_affine' {d : ℕ} (μ : Measure (Eu d)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖ ^ 2) μ) (A : Eu d →L[ℝ] Eu d) (hA : A.IsPositive) (h : Eu d) :
    wassersteinSqP μ (μ.map fun x => A x + h) =
      ENNReal.ofReal (∫ x, ‖(A - 1) x‖ ^ 2 ∂μ + 2 * ⟪(A - 1) (∫ x, x ∂μ), h⟫_ℝ + ‖h‖ ^ 2) := by
  set T : Eu d → Eu d := fun x => A x + h with hT
  have hTc : Continuous T := A.continuous.add continuous_const
  have hTm : Measurable T := hTc.measurable
  have hid : AEStronglyMeasurable (fun x : Eu d => x) μ := aestronglyMeasurable_id
  have hI : Integrable (fun x => ‖x - T x‖ ^ 2) μ := by
    have := integrable_sq_clm hid hμ (1 - A) (-h)
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [hT, sub_apply, one_apply_eq_self]
    congr 2
    abel
  have hRHS : ∫ x, ‖(A - 1) x‖ ^ 2 ∂μ + 2 * ⟪(A - 1) (∫ x, x ∂μ), h⟫_ℝ + ‖h‖ ^ 2 =
      ∫ x, ‖x - T x‖ ^ 2 ∂μ := by
    have hx : Integrable (fun x : Eu d => x) μ := integrable_of_sq hid hμ
    have h1 : Integrable (fun x => ‖(A - 1) x‖ ^ 2) μ := by
      simpa using integrable_sq_clm hid hμ (A - 1) 0
    have h2 : Integrable (fun x => ⟪(A - 1) x, h⟫_ℝ) μ :=
      integrable_inner (by fun_prop) aestronglyMeasurable_const h1 (integrable_const _)
    have e : ∀ x, ‖x - T x‖ ^ 2 = ‖(A - 1) x‖ ^ 2 + 2 * ⟪(A - 1) x, h⟫_ℝ + ‖h‖ ^ 2 := by
      intro x
      rw [← norm_add_sq_real, ← norm_neg]
      congr 1
      simp only [hT, sub_apply, one_apply_eq_self]
      abel_nf
    have hlin : ∫ x, ⟪(A - 1) x, h⟫_ℝ ∂μ = ⟪(A - 1) (∫ x, x ∂μ), h⟫_ℝ := by
      have := ((innerSL ℝ h).comp (A - 1)).integral_comp_comm hx
      calc ∫ x, ⟪(A - 1) x, h⟫_ℝ ∂μ = ∫ x, ((innerSL ℝ h).comp (A - 1)) x ∂μ :=
            integral_congr_ae (ae_of_all _ fun x => by simp [real_inner_comm, inner_sub_right])
        _ = _ := this
        _ = _ := by simp [real_inner_comm, inner_sub_right]
    have h3 : Integrable (fun x => ‖(A - 1) x‖ ^ 2 + 2 * ⟪(A - 1) x, h⟫_ℝ) μ :=
      h1.add (h2.const_mul 2)
    simp_rw [e]
    rw [integral_add h3 (integrable_const _), integral_add h1 (h2.const_mul 2),
      integral_const_mul, hlin]
    simp
  rw [hRHS]
  apply le_antisymm
  · -- upper bound: the coupling `(id, T)₊μ`
    have hg : Measurable fun x : Eu d => (x, T x) := measurable_id.prodMk hTm
    refine iInf_le_of_le (μ.map fun x => (x, T x)) <| iInf_le_of_le inferInstance <|
      iInf_le_of_le ?_ <| iInf_le_of_le ?_ ?_
    · rw [Measure.map_map measurable_fst hg]; exact Measure.map_id
    · rw [Measure.map_map measurable_snd hg]; rfl
    · rw [lintegral_map measurable_cost hg, ofReal_integral_eq_lintegral_ofReal hI
        (ae_of_all _ fun x => by positivity)]
      simp only [edist_sq_eq, le_refl]
  · -- lower bound
    refine le_iInf fun γ => le_iInf fun hγ => le_iInf fun h1 => le_iInf fun h2 => ?_
    have := hγ
    have hγ1 : Integrable (fun p : Eu d × Eu d => ‖p.1‖ ^ 2) γ := by
      have : Integrable (fun x : Eu d => ‖x‖ ^ 2) (γ.map Prod.fst) := h1 ▸ hμ
      exact (integrable_map_measure (by fun_prop) measurable_fst.aemeasurable).1 this
    have hγ2 : Integrable (fun p : Eu d × Eu d => ‖p.2‖ ^ 2) γ := by
      have hν2 : Integrable (fun y => ‖y‖ ^ 2) (μ.map T) :=
        (integrable_map_measure (by fun_prop) hTm.aemeasurable).2 (integrable_sq_clm hid hμ A h)
      have : Integrable (fun x : Eu d => ‖x‖ ^ 2) (γ.map Prod.snd) := h2 ▸ hν2
      exact (integrable_map_measure (by fun_prop) measurable_snd.aemeasurable).1 this
    have hcost : Integrable (fun p : Eu d × Eu d => ‖p.1 - p.2‖ ^ 2) γ := by
      refine ((hγ1.add hγ2).const_mul 2).mono' (by fun_prop) (ae_of_all _ fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
      have := norm_sub_le p.1 p.2
      nlinarith [norm_nonneg (p.1 - p.2), sq_nonneg (‖p.1‖ - ‖p.2‖)]
    have hlin : ∫⁻ p, edist p.1 p.2 ^ 2 ∂γ = ENNReal.ofReal (∫ p, ‖p.1 - p.2‖ ^ 2 ∂γ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hcost (ae_of_all _ fun x => by positivity)]
      simp only [edist_sq_eq]
    rw [hlin]
    refine ENNReal.ofReal_le_ofReal (le_of_forall_pos_le_add fun ε hε => ?_)
    set M := ∫ x, ‖x‖ ^ 2 ∂μ
    have hM : 0 ≤ M := integral_nonneg fun x => by positivity
    have hδ : 0 < ε / (M + 1) := by positivity
    have := lower_bound μ hμ hA h γ h1 h2 hδ
    have hδM : ε / (M + 1) * M ≤ ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    simp only [hT] at *
    linarith


local notation "𝓛" => Matrix.toEuclideanCLM (𝕜 := ℝ)

namespace Elliptic

open Matrix
open scoped MatrixOrder

variable {d : ℕ}

/-- Transposition of a matrix acting in an inner product. -/
lemma inner_toEuclideanCLM_left (D : Matrix (Fin d) (Fin d) ℝ) (x u : Eu d) :
    ⟪𝓛 D x, u⟫_ℝ = ⟪x, 𝓛 (star D) u⟫_ℝ := by
  rw [map_star, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]

/-- Diagonal entries of a matrix as inner products. -/
lemma inner_basisFun_toEuclideanCLM (M : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    ⟪EuclideanSpace.basisFun (Fin d) ℝ i, 𝓛 M (EuclideanSpace.basisFun (Fin d) ℝ i)⟫_ℝ = M i i := by
  rw [inner_toEuclideanCLM]; simp

/-- Composition of matrices acting on `Eu d`. -/
lemma toEuclideanCLM_apply_apply (D D' : Matrix (Fin d) (Fin d) ℝ) (x : Eu d) :
    𝓛 D (𝓛 D' x) = 𝓛 (D * D') x := by
  rw [map_mul]; rfl

lemma sqrt_mul_self_of_posDef {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg

/-- The square root of a positive definite matrix is invertible. -/
lemma isUnit_det_sqrt {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    IsUnit (CFC.sqrt S).det := by
  have : IsUnit S := hS.isUnit
  rw [← sqrt_mul_self_of_posDef hS] at this
  exact (Matrix.isUnit_iff_isUnit_det _).mp (isUnit_of_mul_isUnit_left this)

lemma star_sqrt (S : Matrix (Fin d) (Fin d) ℝ) : star (CFC.sqrt S) = CFC.sqrt S :=
  (CFC.sqrt_nonneg S).isSelfAdjoint.star_eq

lemma star_inv_sqrt (S : Matrix (Fin d) (Fin d) ℝ) : star (CFC.sqrt S)⁻¹ = (CFC.sqrt S)⁻¹ := by
  rw [star_eq_conjTranspose, conjTranspose_nonsing_inv, ← star_eq_conjTranspose, star_sqrt]

/-- Nonnegativity of a product of commuting nonnegative real matrices. -/
lemma mul_nonneg_of_commute {R Q : Matrix (Fin d) (Fin d) ℝ} (hR : 0 ≤ R) (hQ : 0 ≤ Q)
    (h : Commute R Q) : 0 ≤ R * Q := by
  have h1 : Commute (CFC.sqrt R) Q := by
    rw [CFC.sqrt_eq_cfc]; exact h.cfc_nnreal _
  have h2 := (CFC.sqrt_nonneg R).isSelfAdjoint.conjugate_nonneg hQ
  rwa [mul_assoc, h1.eq.symm, ← mul_assoc, CFC.sqrt_mul_sqrt_self R] at h2

/-- The transport matrix `A = R⁻¹ √(R Σν R) R⁻¹`, `R = √Σμ`. -/
noncomputable def transportMatrix (Sμ Sν : Matrix (Fin d) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (CFC.sqrt Sμ)⁻¹ * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ) * (CFC.sqrt Sμ)⁻¹

section transport

variable {Sμ Sν : Matrix (Fin d) (Fin d) ℝ} (hSμ : Sμ.PosDef) (hSν : Sν.PosDef)
include hSμ hSν

omit hSμ hSν in
lemma transportMatrix_nonneg : 0 ≤ transportMatrix Sμ Sν := by
  have := star_left_conjugate_nonneg (CFC.sqrt_nonneg (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ))
    (CFC.sqrt Sμ)⁻¹
  rwa [star_inv_sqrt] at this

/-- The transport matrix pushes `Σμ` to `Σν`: `A Σμ A = Σν`. -/
lemma transportMatrix_mul : transportMatrix Sμ Sν * Sμ * transportMatrix Sμ Sν = Sν := by
  have hM : 0 ≤ CFC.sqrt Sμ * Sν * CFC.sqrt Sμ := by
    simpa [star_sqrt] using star_left_conjugate_nonneg hSν.posSemidef.nonneg (CFC.sqrt Sμ)
  have hu := isUnit_det_sqrt hSμ
  have key := CFC.sqrt_mul_sqrt_self _ hM
  have hR := sqrt_mul_self_of_posDef hSμ
  unfold transportMatrix
  generalize CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ) = N at key ⊢
  generalize CFC.sqrt Sμ = R at hR hu key ⊢
  subst hR
  simp only [mul_assoc, nonsing_inv_mul_cancel_left _ _ hu, mul_nonsing_inv_cancel_left _ _ hu]
  rw [← mul_assoc N N, key]
  simp only [mul_assoc, mul_nonsing_inv _ hu, mul_one, nonsing_inv_mul_cancel_left _ _ hu]

omit hSν in
/-- `Tr (A Σμ) = Tr √(√Σμ Σν √Σμ)`. -/
lemma trace_transportMatrix_mul : (transportMatrix Sμ Sν * Sμ).trace =
    (CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace := by
  have hu := isUnit_det_sqrt hSμ
  have hR := sqrt_mul_self_of_posDef hSμ
  unfold transportMatrix
  generalize CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ) = N
  generalize CFC.sqrt Sμ = R at hR hu ⊢
  subst hR
  simp only [mul_assoc, nonsing_inv_mul_cancel_left _ _ hu]
  rw [trace_mul_comm, mul_assoc, mul_nonsing_inv _ hu, mul_one]

end transport

section moments

variable {η : Measure (Eu d)}

lemma memLp_two_id (h2 : Integrable (fun x => ‖x‖ ^ 2) η) : MemLp (fun x : Eu d => x) 2 η :=
  (memLp_two_iff_integrable_sq_norm aestronglyMeasurable_id).mpr h2

lemma integrable_id' [IsProbabilityMeasure η] (h2 : Integrable (fun x => ‖x‖ ^ 2) η) :
    Integrable (fun x : Eu d => x) η :=
  (memLp_two_id h2).integrable one_le_two

lemma integrable_sq_norm_affine [IsProbabilityMeasure η] (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (a : Eu d) (T : Eu d →L[ℝ] Eu d) : Integrable (fun x => ‖a + T x‖ ^ 2) η := by
  have : MemLp (fun x => a + T x) 2 η := (memLp_const a).add (T.comp_memLp' (memLp_two_id h2))
  exact (memLp_two_iff_integrable_sq_norm this.aestronglyMeasurable).mp this

/-- For `η` centered, `∫ ‖a + T x‖² dη = ‖a‖² + ∫ ‖T x‖² dη`. -/
lemma integral_sq_norm_affine [IsProbabilityMeasure η] (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hmean : ∫ x, x ∂η = 0) (a : Eu d) (T : Eu d →L[ℝ] Eu d) :
    ∫ x, ‖a + T x‖ ^ 2 ∂η = ‖a‖ ^ 2 + ∫ x, ‖T x‖ ^ 2 ∂η := by
  have hT : Integrable (fun x => T x) η := T.integrable_comp (integrable_id' h2)
  have hT2 : Integrable (fun x => ‖T x‖ ^ 2) η := by
    simpa using integrable_sq_norm_affine h2 0 T
  have hin : Integrable (fun x => 2 * ⟪a, T x⟫_ℝ) η := (hT.const_inner a).const_mul 2
  have h1 : Integrable (fun x => ‖a‖ ^ 2 + 2 * ⟪a, T x⟫_ℝ) η := (integrable_const _).add hin
  simp_rw [norm_add_sq_real]
  rw [integral_add h1 hT2, integral_add (integrable_const _) hin,
    integral_const_mul, integral_inner hT, T.integral_comp_comm (integrable_id' h2), hmean]
  simp

lemma integrable_inner_mul_inner (h2 : Integrable (fun x => ‖x‖ ^ 2) η) (u v : Eu d) :
    Integrable (fun x => ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ) η := by
  refine (h2.const_mul (‖u‖ * ‖v‖)).mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  calc |⟪x, u⟫_ℝ| * |⟪x, v⟫_ℝ| ≤ (‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) := by
        gcongr <;> exact abs_real_inner_le_norm _ _
    _ = ‖u‖ * ‖v‖ * ‖x‖ ^ 2 := by ring

/-- For `η` with identity covariance, `∫ ‖D x‖² dη = Tr (D Dᵀ)`. -/
lemma integral_sq_norm_toEuclideanCLM (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hcov : ∀ u v : Eu d, ∫ x, ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ ∂η = ⟪u, v⟫_ℝ) (D : Matrix (Fin d) (Fin d) ℝ) :
    ∫ x, ‖𝓛 D x‖ ^ 2 ∂η = (D * star D).trace := by
  set b := EuclideanSpace.basisFun (Fin d) ℝ
  have h : ∀ x, ‖𝓛 D x‖ ^ 2 =
      ∑ i, ⟪x, 𝓛 (star D) (b i)⟫_ℝ * ⟪x, 𝓛 (star D) (b i)⟫_ℝ := by
    intro x
    rw [← b.sum_sq_inner_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_toEuclideanCLM_left, sq]
  simp_rw [h]
  rw [integral_finsetSum _ fun i _ => integrable_inner_mul_inner h2 _ _]
  simp_rw [hcov, inner_toEuclideanCLM_left, star_star, toEuclideanCLM_apply_apply]
  simp only [b, inner_basisFun_toEuclideanCLM]
  rfl

/-- Mean and covariance of the image of `η` under `x ↦ m + √S x`. -/
lemma moments_map [IsProbabilityMeasure η] (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hmean : ∫ x, x ∂η = 0) (hcov : ∀ u v : Eu d, ∫ x, ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ ∂η = ⟪u, v⟫_ℝ)
    (m : Eu d) {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.PosDef) :
    ∫ x, x ∂(η.map fun x => m + 𝓛 (CFC.sqrt S) x) = m ∧
      ∀ u v : Eu d, ∫ x, ⟪x - m, u⟫_ℝ * ⟪x - m, v⟫_ℝ ∂(η.map fun x => m + 𝓛 (CFC.sqrt S) x) =
        ⟪u, 𝓛 S v⟫_ℝ := by
  have hmeas : Measurable fun x : Eu d => m + 𝓛 (CFC.sqrt S) x := by fun_prop
  constructor
  · rw [integral_map hmeas.aemeasurable (by fun_prop), integral_add (integrable_const _)
      ((𝓛 _).integrable_comp (integrable_id' h2)), (𝓛 _).integral_comp_comm (integrable_id' h2),
      hmean]
    simp
  · intro u v
    rw [integral_map hmeas.aemeasurable (by fun_prop)]
    simp_rw [add_sub_cancel_left, inner_toEuclideanCLM_left, star_sqrt, hcov,
      inner_toEuclideanCLM_left, star_sqrt, toEuclideanCLM_apply_apply, sqrt_mul_self_of_posDef hS]

end moments

lemma transportMatrix_star {Sμ Sν : Matrix (Fin d) (Fin d) ℝ} :
    star (transportMatrix Sμ Sν) = transportMatrix Sμ Sν :=
  transportMatrix_nonneg.isSelfAdjoint.star_eq

/-- A nonnegative matrix gives a positive operator. -/
lemma isPositive_toEuclideanCLM {A : Matrix (Fin d) (Fin d) ℝ} (hA : 0 ≤ A) :
    (𝓛 A).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff']
  refine ⟨hA.isSelfAdjoint.map _, fun x => ?_⟩
  rw [real_inner_comm, inner_toEuclideanCLM]
  simpa using (Matrix.nonneg_iff_posSemidef.mp hA).dotProduct_mulVec_nonneg (WithLp.ofLp x)

end Elliptic

open MarkovTriple.Gelbrich.Elliptic Matrix in
open scoped MatrixOrder in
/-- **Lemma 2.2.** Let `η` be a rotationally invariant probability measure on `ℝᵈ` with finite
second moment, zero mean and identity covariance, and let `μ`, `ν` be its images under
`x ↦ m_μ + √Σ_μ x` and `x ↦ m_ν + √Σ_ν x`, with `Σ_μ`, `Σ_ν` symmetric positive definite
matrices. Then `μ`, `ν` have means `m_μ`, `m_ν` and covariances `Σ_μ`, `Σ_ν`, and
`W₂²(μ,ν) = Tr(Σ_μ + Σ_ν - 2 √(√Σ_μ Σ_ν √Σ_μ)) + |m_μ - m_ν|²`; if moreover `Σ_μ` and `Σ_ν`
commute, `W₂²(μ,ν) = Tr((√Σ_μ - √Σ_ν)²) + |m_μ - m_ν|²`. Square roots are those of the
continuous functional calculus (`CFC.sqrt`) for the order on matrices. -/
theorem wassersteinSqP_elliptic' {d : ℕ} (η : Measure (Eu d)) [IsProbabilityMeasure η]
    (hrot : ∀ U : Eu d ≃ₗᵢ[ℝ] Eu d, η.map U = η) (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hmean : ∫ x, x ∂η = 0) (hcov : ∀ u v : Eu d, ∫ x, ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ ∂η = ⟪u, v⟫_ℝ)
    (mμ mν : Eu d) (Sμ Sν : Matrix (Fin d) (Fin d) ℝ) (hSμ : Sμ.PosDef) (hSν : Sν.PosDef) :
    let μ := η.map fun x => mμ + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sμ) x
    let ν := η.map fun x => mν + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sν) x
    (∫ x, x ∂μ = mμ ∧ ∀ u v : Eu d, ∫ x, ⟪x - mμ, u⟫_ℝ * ⟪x - mμ, v⟫_ℝ ∂μ =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Sμ v⟫_ℝ) ∧
    (∫ x, x ∂ν = mν ∧ ∀ u v : Eu d, ∫ x, ⟪x - mν, u⟫_ℝ * ⟪x - mν, v⟫_ℝ ∂ν =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Sν v⟫_ℝ) ∧
    wassersteinSqP μ ν = ENNReal.ofReal
      ((Sμ + Sν - 2 * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace + ‖mμ - mν‖ ^ 2) ∧
    (Sμ * Sν = Sν * Sμ → wassersteinSqP μ ν = ENNReal.ofReal
      (((CFC.sqrt Sμ - CFC.sqrt Sν) ^ 2).trace + ‖mμ - mν‖ ^ 2)) := by
  intro μ ν
  have hμ := moments_map h2 hmean hcov mμ hSμ
  have hν := moments_map h2 hmean hcov mν hSν
  set R := CFC.sqrt Sμ with hR
  set Q := CFC.sqrt Sν with hQ
  have hRR : R * R = Sμ := sqrt_mul_self_of_posDef hSμ
  have hQQ : Q * Q = Sν := sqrt_mul_self_of_posDef hSν
  have hRu : IsUnit R.det := isUnit_det_sqrt hSμ
  have hQu : IsUnit Q.det := isUnit_det_sqrt hSν
  set A := transportMatrix Sμ Sν with hA
  set h := mν - 𝓛 A mμ with hh
  have hTμ : Measurable fun x : Eu d => mμ + 𝓛 R x := by fun_prop
  have hTν : Measurable fun x : Eu d => mν + 𝓛 Q x := by fun_prop
  have hT : Measurable fun x : Eu d => 𝓛 A x + h := by fun_prop
  -- the orthogonal matrix `U = Q⁻¹ A R`
  set U := Q⁻¹ * (A * R) with hU
  have hUu : U ∈ unitary (Matrix (Fin d) (Fin d) ℝ) := by
    have h1 : U * star U = 1 := by
      rw [hU, star_mul, star_mul, star_sqrt, star_inv_sqrt, transportMatrix_star]
      calc Q⁻¹ * (A * R) * (R * A * Q⁻¹) = Q⁻¹ * (A * (R * R) * A) * Q⁻¹ := by
            simp only [mul_assoc]
        _ = 1 := by
            rw [hRR, transportMatrix_mul hSμ hSν, ← hQQ]
            simp only [mul_assoc, mul_nonsing_inv _ hQu, mul_one, nonsing_inv_mul _ hQu]
    exact Unitary.mem_iff.mpr ⟨mul_eq_one_comm.mp h1, h1⟩
  set e := Unitary.linearIsometryEquiv ⟨𝓛 U, Unitary.map_mem 𝓛 hUu⟩
  have hνT : ν = μ.map fun x => 𝓛 A x + h := by
    have hcomp : ((fun x => 𝓛 A x + h) ∘ fun x => mμ + 𝓛 R x) =
        (fun x => mν + 𝓛 Q x) ∘ e := by
      funext x
      have he : e x = 𝓛 U x := rfl
      simp only [Function.comp_apply, he, hU, toEuclideanCLM_apply_apply,
        mul_nonsing_inv_cancel_left _ _ hQu, map_add, hh]
      abel
    rw [Measure.map_map hT hTμ, hcomp, ← Measure.map_map hTν e.continuous.measurable, hrot]
  have hint : Integrable (fun x => ‖x‖ ^ 2) μ := by
    rw [integrable_map_measure (by fun_prop) hTμ.aemeasurable]
    exact integrable_sq_norm_affine h2 mμ _
  have hpos : (𝓛 A).IsPositive := isPositive_toEuclideanCLM transportMatrix_nonneg
  have main : wassersteinSqP μ ν = ENNReal.ofReal
      ((Sμ + Sν - 2 * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace + ‖mμ - mν‖ ^ 2) := by
    rw [hνT, wassersteinSqP_map_affine' μ hint _ hpos h, hμ.1]
    congr 1
    have hB : 𝓛 A - 1 = 𝓛 (A - 1) := by rw [map_sub, map_one]
    rw [hB, integral_map hTμ.aemeasurable (by fun_prop)]
    simp_rw [map_add (𝓛 (A - 1)), toEuclideanCLM_apply_apply]
    rw [integral_sq_norm_affine h2 hmean, integral_sq_norm_toEuclideanCLM h2 hcov]
    have e1 : ‖𝓛 (A - 1) mμ‖ ^ 2 + 2 * ⟪𝓛 (A - 1) mμ, h⟫_ℝ + ‖h‖ ^ 2 = ‖mμ - mν‖ ^ 2 := by
      rw [← norm_add_sq_real, norm_sub_rev, hh, map_sub, map_one]
      congr 1
      simp only [_root_.sub_apply, one_apply_eq_self]
      abel_nf
    have e2 : ((A - 1) * R * star ((A - 1) * R)).trace =
        (Sμ + Sν - 2 * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace := by
      have h3 : (A - 1) * R * star ((A - 1) * R) = A * Sμ * A - A * Sμ - Sμ * A + Sμ := by
        rw [star_mul, star_sqrt, star_sub, star_one, transportMatrix_star,
          show (A - 1) * R * (R * (A - 1)) = (A - 1) * (R * R) * (A - 1) by simp only [mul_assoc],
          hRR]
        simp only [sub_mul, mul_sub, one_mul, mul_one]
        abel
      rw [h3, transportMatrix_mul hSμ hSν, trace_add, trace_sub, trace_sub, trace_sub, trace_add,
        trace_mul_comm Sμ A, trace_transportMatrix_mul hSμ, two_mul, trace_add]
      ring
    linarith
  refine ⟨hμ, hν, main, fun hcomm => ?_⟩
  rw [main]
  have hRν : Commute R Sν := by rw [hR, CFC.sqrt_eq_cfc]; exact Commute.cfc_nnreal hcomm _
  have hRQ : Commute R Q := by rw [hQ, CFC.sqrt_eq_cfc]; exact (Commute.cfc_nnreal hRν.symm _).symm
  have hsqrt : CFC.sqrt (R * Sν * R) = R * Q :=
    CFC.sqrt_unique
      (by rw [← hQQ, mul_assoc R Q, hRQ.eq, ← mul_assoc, mul_assoc R]; simp only [mul_assoc])
      (mul_nonneg_of_commute (CFC.sqrt_nonneg _) (CFC.sqrt_nonneg _) hRQ)
  rw [hsqrt, sq (R - Q), sub_mul, mul_sub, mul_sub, hRR, hQQ, ← hRQ.eq, two_mul]
  congr 3
  abel

/-- For probability marginals the unified `wassersteinSq` coincides with the infimum over
probability couplings used in cutoff-fastdiff. -/
theorem wassersteinSq_eq_wassersteinSqP {d : ℕ} (μ ν : Measure (Eu d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    MarkovTriple.wassersteinSq μ ν = wassersteinSqP μ ν := by
  apply le_antisymm
  · refine le_iInf fun γ => le_iInf fun hγ => le_iInf fun h1 => le_iInf fun h2 => ?_
    exact MarkovTriple.wassersteinSq_le_cost (⟨γ, h1, h2⟩ : Coupling μ ν)
  · refine le_iInf fun c => ?_
    have := c.isProbabilityMeasure
    exact iInf_le_of_le c.val <| iInf_le_of_le inferInstance <|
      iInf_le_of_le c.property.1 <| iInf_le_of_le c.property.2 le_rfl

end Gelbrich

open MeasureTheory Gelbrich in
/-- **Lemma 2.1 (position-scale transport).** For a positive operator `A` and `h ∈ ℝᵈ`, the map
`x ↦ A x + h` is optimal and `W₂²(μ, (A · + h)_#μ) = ∫ ‖(A - 1) x‖² dμ + 2⟪(A - 1) 𝔼 X, h⟫ + ‖h‖²`.
Source: cutoff-fastdiff `wassersteinSq_map_affine'`. -/
theorem wassersteinSq_map_affine {d : ℕ} (μ : Measure (Eu d)) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x => ‖x‖ ^ 2) μ) (A : Eu d →L[ℝ] Eu d) (hA : A.IsPositive) (h : Eu d) :
    wassersteinSq μ (μ.map fun x => A x + h) =
      ENNReal.ofReal (∫ x, ‖(A - 1) x‖ ^ 2 ∂μ + 2 * inner ℝ ((A - 1) (∫ x, x ∂μ)) h + ‖h‖ ^ 2) := by
  have : IsProbabilityMeasure (μ.map fun x => A x + h) :=
    (Measure.isProbabilityMeasure_map_iff
      (A.continuous.add continuous_const).measurable.aemeasurable).2 inferInstance
  rw [wassersteinSq_eq_wassersteinSqP]
  exact wassersteinSqP_map_affine' μ hμ A hA h

open MeasureTheory Gelbrich Matrix in
open scoped MatrixOrder InnerProductSpace in
/-- **Lemma 2.2 (Gelbrich / Bures formula for elliptic families).** Let `η` be a rotationally
invariant probability measure on `ℝᵈ` with finite second moment, zero mean and identity
covariance, and `μ`, `ν` its images under `x ↦ m + √Σ x`.  Then
`W₂²(μ,ν) = Tr(Σμ + Σν - 2 √(√Σμ Σν √Σμ)) + |mμ - mν|²`, and for commuting `Σμ`, `Σν` it equals
`Tr((√Σμ - √Σν)²) + |mμ - mν|²`.  Source: cutoff-fastdiff `wassersteinSq_elliptic'`. -/
theorem wassersteinSq_elliptic {d : ℕ} (η : Measure (Eu d)) [IsProbabilityMeasure η]
    (hrot : ∀ U : Eu d ≃ₗᵢ[ℝ] Eu d, η.map U = η) (h2 : Integrable (fun x => ‖x‖ ^ 2) η)
    (hmean : ∫ x, x ∂η = 0) (hcov : ∀ u v : Eu d, ∫ x, ⟪x, u⟫_ℝ * ⟪x, v⟫_ℝ ∂η = ⟪u, v⟫_ℝ)
    (mμ mν : Eu d) (Sμ Sν : Matrix (Fin d) (Fin d) ℝ) (hSμ : Sμ.PosDef) (hSν : Sν.PosDef) :
    let μ := η.map fun x => mμ + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sμ) x
    let ν := η.map fun x => mν + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sν) x
    (∫ x, x ∂μ = mμ ∧ ∀ u v : Eu d, ∫ x, ⟪x - mμ, u⟫_ℝ * ⟪x - mμ, v⟫_ℝ ∂μ =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Sμ v⟫_ℝ) ∧
    (∫ x, x ∂ν = mν ∧ ∀ u v : Eu d, ∫ x, ⟪x - mν, u⟫_ℝ * ⟪x - mν, v⟫_ℝ ∂ν =
        ⟪u, Matrix.toEuclideanCLM (𝕜 := ℝ) Sν v⟫_ℝ) ∧
    wassersteinSq μ ν = ENNReal.ofReal
      ((Sμ + Sν - 2 * CFC.sqrt (CFC.sqrt Sμ * Sν * CFC.sqrt Sμ)).trace + ‖mμ - mν‖ ^ 2) ∧
    (Sμ * Sν = Sν * Sμ → wassersteinSq μ ν = ENNReal.ofReal
      (((CFC.sqrt Sμ - CFC.sqrt Sν) ^ 2).trace + ‖mμ - mν‖ ^ 2)) := by
  intro μ ν
  have hP := wassersteinSqP_elliptic' η hrot h2 hmean hcov mμ mν Sμ Sν hSμ hSν
  have hμp : IsProbabilityMeasure μ :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop : Measurable fun x : Eu d =>
      mμ + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sμ) x).aemeasurable).2 inferInstance
  have hνp : IsProbabilityMeasure ν :=
    (Measure.isProbabilityMeasure_map_iff (by fun_prop : Measurable fun x : Eu d =>
      mν + Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Sν) x).aemeasurable).2 inferInstance
  refine ⟨hP.1, hP.2.1, ?_, fun hc => ?_⟩
  · rw [wassersteinSq_eq_wassersteinSqP]; exact hP.2.2.1
  · rw [wassersteinSq_eq_wassersteinSqP]; exact hP.2.2.2 hc

end MarkovTriple
