import Mathlib
import MarkovTriple.BGL.Theory.Conservation.ExtAlgebra
import MarkovTriple.BGL.Theory.Conservation.Hilbert
import MarkovTriple.BGL.Semigroup.Conservative
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Frozen.Complete

/-!
# The key estimate of BGL Thm 3.2.6 / 3.3.23

For `ζ, η ∈ 𝒜₀`, with `ξ = η²`, `ζ_s = P_s ζ`:

`⟪P_t ζ − ζ, ξ⟫ = ∫₀ᵗ ⟪P_s Lζ, ξ⟫ ds`  (Duhamel, `inner_duhamel`),
`⟪P_s Lζ, ξ⟫ = −∫ Γ(P_s ζ, ξ) dμ`       (commutation with the generator, symmetry, F7; `inner_semigroup_Lcls`),
`|∫ Γ(g, η²)| ≤ √B (∫η² + ∫Γ(η))` if `Γ(g) ≤ B` (Cauchy–Schwarz, `ΓA_sq_bound`),

and the *gradient bound* `Γ(P_s ζ) ≤ e^{-2ρ s} P_s Γ(ζ) ≤ e^{-2ρ s} sup Γ(ζ)`.  The book uses
`‖√Γ ξ‖₁ ‖√Γ ζ_k‖_∞`; the Young inequality `2 |η| √Γη ≤ η² + Γη` replaces `√Γ ξ ∈ L¹`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- **The (weak) gradient bound** `Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)` (BGL Cor. 3.3.19) for `f ∈ 𝒜₀`,
stated for an arbitrary representative `g ∈ 𝒜` of `P_t [f]` and arbitrary `c ∈ 𝒜₀` representing
`Γ(f)`.  It is a *hypothesis* of the mass-conservation theorems below; it is a theorem for compact
triples and for full triples satisfying `GradientInterpolation`
(`FullTriple.hasGradientBound`, `BGL/Theory/Conservation/Mass.lean`). -/
def HasGradientBound (D : DiffusionTriple E) (A : Subalgebra ℝ (E → ℝ)) (ρ : ℝ) : Prop :=
  ∀ (f c : D.A₀), c.1 =ᵐ[D.μ] D.Γ f.1 f.1 → ∀ (t : ℝ≥0) (g : E → ℝ), g ∈ A →
    (D.semigroup t (D.cls f) : E → ℝ) =ᵐ[D.μ] g →
    D.ΓA g g ≤ᵐ[D.μ] fun x => Real.exp (-2 * ρ * t) * (D.semigroup t (D.cls c) : E → ℝ) x

namespace DiffusionTriple

variable (D : DiffusionTriple E)

/-- `⟪P_s Lζ, ξ⟫ = ∫ g L ξ` for a representative `g` of `P_s ζ` (symmetry of `P_s`, commutation with
the generator and symmetry of the generator). -/
theorem inner_semigroup_Lcls (s : ℝ≥0) (ζ ξ : D.A₀) (g : E → ℝ)
    (hg : (D.semigroup s (D.cls ζ) : E → ℝ) =ᵐ[D.μ] g) :
    inner ℝ (D.semigroup s (D.Lcls ζ)) (D.cls ξ) = ∫ x, g x * D.L ξ.1 x ∂D.μ := by
  have hζ := D.cls_mem_generator_domain ζ
  have hGζ : D.generator ⟨D.cls ζ, hζ⟩ = D.Lcls ζ := D.generator_cls ζ _
  obtain ⟨hP, hGP⟩ := (formData D).semigroup_generator_comm hζ s
  have hξ := D.cls_mem_generator_domain ξ
  have hsymm := (formData D).generator_symm hP hξ
  have hGξ : D.generator ⟨D.cls ξ, hξ⟩ = D.Lcls ξ := D.generator_cls ξ _
  have hP' : D.semigroup s (D.cls ζ) ∈ D.generator.domain := hP
  have hGP' : D.generator ⟨D.semigroup s (D.cls ζ), hP'⟩ = D.semigroup s (D.Lcls ζ) := by
    have h1 : D.generator ⟨D.semigroup s (D.cls ζ), hP'⟩ = D.semigroup s (D.generator ⟨D.cls ζ, hζ⟩) :=
      hGP
    rw [h1, hGζ]
  have hsymm' : inner ℝ (D.generator ⟨D.semigroup s (D.cls ζ), hP'⟩) (D.cls ξ) =
    inner ℝ (D.semigroup s (D.cls ζ)) (D.generator ⟨D.cls ξ, hξ⟩) := hsymm
  rw [hGP', hGξ] at hsymm'
  have hsymm := hsymm'
  rw [hsymm, L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hg, D.coeFn_Lcls ξ] with x h1 h2
  rw [h1, h2]

/-- **Duhamel formula in weak form**: `⟪P_t ζ − ζ, ξ⟫ = ∫₀ᵗ ⟪P_s Lζ, ξ⟫ ds`. -/
theorem inner_duhamel (t : ℝ≥0) (ζ ξ : D.A₀) :
    inner ℝ (D.semigroup t (D.cls ζ) - D.cls ζ) (D.cls ξ) =
      ∫ s in (0 : ℝ)..t, inner ℝ (D.semigroup s.toNNReal (D.Lcls ζ)) (D.cls ξ) := by
  have h := (formData D).semigroup_integral (D.cls ζ - D.Lcls ζ) t
  rw [DiffusionTriple.R_cls_sub D ζ] at h
  have e : D.cls ζ - D.Lcls ζ - D.cls ζ = -D.Lcls ζ := by abel
  rw [e] at h
  simp only [map_neg, intervalIntegral.integral_neg, neg_neg] at h
  have hc : Continuous fun s : ℝ => D.semigroup s.toNNReal (D.Lcls ζ) :=
    ((formData D).continuous_semigroup_apply _).comp continuous_real_toNNReal
  have hcomm := ContinuousLinearMap.intervalIntegral_comp_comm (innerSL ℝ (D.cls ξ))
    (hc.intervalIntegrable (μ := volume) 0 (t : ℝ))
  have h2 : (innerSL ℝ (D.cls ξ)) (∫ s in (0 : ℝ)..t, D.semigroup s.toNNReal (D.Lcls ζ)) =
      ∫ s in (0 : ℝ)..t, (innerSL ℝ (D.cls ξ)) (D.semigroup s.toNNReal (D.Lcls ζ)) := hcomm.symm
  rw [show (formData D).semigroup = D.semigroup from rfl] at h
  rw [h, real_inner_comm]
  simp only [innerSL_apply_apply] at h2
  rw [h2]
  refine intervalIntegral.integral_congr (fun s _ => ?_)
  exact real_inner_comm _ _

/-- The finite constant `K(η) = ∫ η² + ∫ Γ(η)` (the book's `‖η‖² + ℰ(η)`). -/
noncomputable def Kconst (η : D.A₀) : ℝ := ∫ x, (η.1 x ^ 2 + D.ΓA η.1 η.1 x) ∂D.μ

theorem integrable_K (η : D.A₀) : Integrable (fun x => η.1 x ^ 2 + D.ΓA η.1 η.1 x) D.μ := by
  have h1 : Integrable (fun x => η.1 x ^ 2) D.μ := by
    have : (fun x => η.1 x ^ 2) = η.1 * η.1 := by funext x; simp [sq]
    rw [this]; exact D.integrable_of_mem (D.A₀.mul_mem η.2 η.2)
  have h2 : Integrable (D.ΓA η.1 η.1) D.μ :=
    (D.integrable_of_mem (D.Γ_mem _ η.2 _ η.2)).congr (D.ΓA_ae_eq η.2 η.2).symm
  exact h1.add h2

theorem Kconst_nonneg {A : Subalgebra ℝ (E → ℝ)} (h : ExtendedAlgebra D A) (η : D.A₀) : 0 ≤ D.Kconst η := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [h.ΓA_nonneg η.1 (h.A₀_le _ η.2)] with x hx
  simp only [Pi.zero_apply] at hx ⊢
  have := sq_nonneg (η.1 x)
  linarith

end DiffusionTriple

namespace ExtendedAlgebra

variable {D : DiffusionTriple E} {A : Subalgebra ℝ (E → ℝ)} (h : ExtendedAlgebra D A)
include h

/-- **Key estimate.**  `|⟪P_s Lζ, η²⟫| ≤ √(e^{-2ρ s} B) · (∫η² + ∫Γ(η))` if `Γ(ζ) ≤ B` is preserved
by the semigroup (`P_s Γ(ζ) ≤ B`) and the gradient bound holds. -/
theorem abs_inner_le {ρ : ℝ} (hGB : HasGradientBound D A ρ) (ζ c : D.A₀)
    (hc : c.1 =ᵐ[D.μ] D.Γ ζ.1 ζ.1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ s : ℝ≥0, (D.semigroup s (D.cls c) : E → ℝ) ≤ᵐ[D.μ] fun _ => B)
    (η : D.A₀) (s : ℝ≥0) :
    |inner ℝ (D.semigroup s (D.Lcls ζ)) (D.cls ⟨η.1 * η.1, D.A₀.mul_mem η.2 η.2⟩)| ≤
      Real.sqrt (Real.exp (-2 * ρ * s) * B) * D.Kconst η := by
  obtain ⟨g, hgA, hg⟩ := h.semigroup_A s ζ
  set ξ : D.A₀ := ⟨η.1 * η.1, D.A₀.mul_mem η.2 η.2⟩ with hξ
  have e1 := D.inner_semigroup_Lcls s ζ ξ g hg
  have e2 := h.ibp_A g hgA ξ.1 ξ.2
  have hΓg : D.ΓA g g ≤ᵐ[D.μ] fun _ => Real.exp (-2 * ρ * s) * B := by
    filter_upwards [hGB ζ c hc s g hgA hg, hB s] with x h1 h2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le)
  have hsq := ΓA_sq_bound h hgA (h.A₀_le _ η.2) (mul_nonneg (Real.exp_pos _).le hB0) hΓg
  have hξf : ξ.1 = fun x => η.1 x ^ 2 := by funext x; simp [hξ, sq]
  have e2' : ∫ x, D.ΓA g (fun x => η.1 x ^ 2) x ∂D.μ = -∫ x, g x * D.L ξ.1 x ∂D.μ := by
    rw [← hξf]; exact e2
  rw [e1]
  have e3 : ∫ x, g x * D.L ξ.1 x ∂D.μ = -∫ x, D.ΓA g (fun x => η.1 x ^ 2) x ∂D.μ := by
    linarith
  rw [e3, abs_neg]
  calc |∫ x, D.ΓA g (fun x => η.1 x ^ 2) x ∂D.μ|
      ≤ ∫ x, |D.ΓA g (fun x => η.1 x ^ 2) x| ∂D.μ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := D.μ) (fun x => D.ΓA g (fun x => η.1 x ^ 2) x)
    _ ≤ ∫ x, Real.sqrt (Real.exp (-2 * ρ * s) * B) * (η.1 x ^ 2 + D.ΓA η.1 η.1 x) ∂D.μ :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
          ((D.integrable_K η).const_mul _) hsq
    _ = Real.sqrt (Real.exp (-2 * ρ * s) * B) * D.Kconst η := by
        rw [integral_const_mul]; rfl

end ExtendedAlgebra

end MarkovTriple.BGL
