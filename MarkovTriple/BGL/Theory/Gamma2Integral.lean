import Mathlib
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.FullBasic
import MarkovTriple.BGL.Consistency
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Semigroup.Characterization

/-!
# Integrated `Γ₂` identities and their extension to `𝒟(L)` (BGL Props. 3.3.16–3.3.17, integrated form)

Statements proved here, for a full triple `T` (BGL numbering, paraphrase):

* (3.3.8) on test functions: `∫ Γ₂(f) dμ = ∫ (L f)² dμ` for `f ∈ 𝒜₀`
  (`FullTriple.integral_Γ₂`);
* the integrated curvature-dimension inequality on `𝒜₀`:
  `ρ ∫ Γ(f) + n⁻¹ ∫ (L f)² ≤ ∫ (L f)²` (`FullTriple.integral_CD`);
* **extension to `𝒟(L)`** (Prop. 3.3.16 (i)–(ii), *integrated* form): for every `u ∈ 𝒟(L)`
  (`ρ ℰ(u) + n⁻¹ ‖L u‖² ≤ ‖L u‖²`, with `ℰ(u) = -⟪L u, u⟫`), by the ESA hypothesis F10
  (`FullTriple.CD_integrated_domain`), and its form version `FullTriple.CD_form_domain`.

NOT proved here (documented in `Theory/GAPS.md`): the extension of the *operator* `Γ₂` itself
to a bilinear map `𝒟(L)×𝒟(L) → L¹` (Prop. 3.3.16 (i), (iii)), the Hessian items (iv)–(viii), and the
identification on `𝒜 ∩ 𝒟(L)` (Prop. 3.3.17).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace DiffusionTriple

lemma ΓA_comm (T : DiffusionTriple E) (f g : E → ℝ) : T.ΓA f g = T.ΓA g f := by
  funext x
  simp only [ΓA]
  rw [mul_comm f g]; ring

end DiffusionTriple

namespace FullTriple

variable (T : FullTriple E)

lemma ΓA_self_mem_A₀ {f : E → ℝ} (hf : f ∈ T.A₀) : T.toDiffusionTriple.ΓA f f ∈ T.A₀ :=
  ΓA_mem_A₀ T (T.A₀_le f hf) hf

/-- `∫ Γ₂(f) = ∫ (L f)²` for `f ∈ 𝒜₀` (BGL (3.3.8) on test functions). -/
theorem integral_Γ₂ {f : E → ℝ} (hf : f ∈ T.A₀) :
    ∫ x, T.toDiffusionTriple.Γ₂ f f x ∂T.μ = ∫ x, T.L f x * T.L f x ∂T.μ := by
  have hfA := T.A₀_le f hf
  have hLf : T.L f ∈ T.A₀ := T.L_mem f hf
  have hΓ := ΓA_self_mem_A₀ T hf
  have i1 : Integrable (T.L (T.toDiffusionTriple.ΓA f f)) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.L_mem _ hΓ)
  have i2 : Integrable (T.toDiffusionTriple.ΓA f (T.L f)) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (ΓA_mem_A₀ T hfA hLf)
  have h0 : ∫ x, T.L (T.toDiffusionTriple.ΓA f f) x ∂T.μ = 0 := T.integral_L _ hΓ
  have h1 : ∫ x, T.toDiffusionTriple.ΓA f (T.L f) x ∂T.μ = -∫ x, T.L f x * T.L f x ∂T.μ :=
    (T.ibp_A f hfA (T.L f) hLf).1
  have hfun : T.toDiffusionTriple.Γ₂ f f = fun x =>
      (1 / 2 : ℝ) * (T.L (T.toDiffusionTriple.ΓA f f) x -
        2 * T.toDiffusionTriple.ΓA f (T.L f) x) := by
    funext x
    simp only [DiffusionTriple.Γ₂]
    rw [DiffusionTriple.ΓA_comm T.toDiffusionTriple (T.L f) f]; ring
  rw [hfun, integral_const_mul, integral_sub i1 (i2.const_mul 2), integral_const_mul, h0, h1]
  ring

lemma integrable_Γ₂ {f : E → ℝ} (hf : f ∈ T.A₀) :
    Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ := by
  have hfA := T.A₀_le f hf
  have hLf : T.L f ∈ T.A₀ := T.L_mem f hf
  have hΓ := ΓA_self_mem_A₀ T hf
  have i1 : Integrable (T.L (T.toDiffusionTriple.ΓA f f)) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.L_mem _ hΓ)
  have i2 : Integrable (T.toDiffusionTriple.ΓA f (T.L f)) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (ΓA_mem_A₀ T hfA hLf)
  have hfun : T.toDiffusionTriple.Γ₂ f f = fun x =>
      (1 / 2 : ℝ) * (T.L (T.toDiffusionTriple.ΓA f f) x -
        2 * T.toDiffusionTriple.ΓA f (T.L f) x) := by
    funext x
    simp only [DiffusionTriple.Γ₂]
    rw [DiffusionTriple.ΓA_comm T.toDiffusionTriple (T.L f) f]; ring
  rw [hfun]
  exact (i1.sub (i2.const_mul 2)).const_mul _

/-- Integrated `CD(ρ,n)` on `𝒜₀`: `ρ ∫ Γ(f) + n⁻¹ ∫ (L f)² ≤ ∫ (L f)²`
(`Γ` = the carré du champ field of the triple). -/
theorem integral_CD {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A₀) :
    ρ * ∫ x, T.Γ f f x ∂T.μ + (n⁻¹).toReal * ∫ x, T.L f x * T.L f x ∂T.μ ≤
      ∫ x, T.L f x * T.L f x ∂T.μ := by
  have hLf : T.L f ∈ T.A₀ := T.L_mem f hf
  have hΓ : T.Γ f f ∈ T.A₀ := T.Γ_mem f hf f hf
  have i1 : Integrable (T.Γ f f) T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple hΓ
  have i4 : Integrable (fun x => T.L f x * T.L f x) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.A₀.mul_mem hLf hLf)
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (i1.const_mul ρ) (i4.const_mul _), ← integral_Γ₂ T hf]
  refine integral_mono_ae ((i1.const_mul ρ).add (i4.const_mul _)) (integrable_Γ₂ T hf) ?_
  filter_upwards [hCD.2 f (T.A₀_le f hf),
    DiffusionTriple.ΓA_ae_eq T.toDiffusionTriple hf hf] with x hx hx2
  rw [← hx2]
  show ρ * T.toDiffusionTriple.ΓA f f x + (n⁻¹).toReal * (T.L f x * T.L f x) ≤ _
  nlinarith [hx]

/-- `CD(ρ,n)` integrated, dimension term dropped: `ρ ∫ Γ(f) ≤ ∫ (L f)²`. -/
theorem integral_CD_infty {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A₀) :
    ρ * ∫ x, T.Γ f f x ∂T.μ ≤ ∫ x, T.L f x * T.L f x ∂T.μ := by
  have h := integral_CD T hCD hf
  have : 0 ≤ (n⁻¹).toReal * ∫ x, T.L f x * T.L f x ∂T.μ :=
    mul_nonneg ENNReal.toReal_nonneg (integral_nonneg fun x => mul_self_nonneg _)
  linarith

/-- The two integrals in `L²` language: for `f ∈ 𝒜₀`,
`ρ (-⟪L[f], [f]⟫) + n⁻¹ ‖L[f]‖² ≤ ‖L[f]‖²`. -/
theorem CD_integrated_cls {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (f : T.A₀) :
    ρ * (-inner ℝ (T.toDiffusionTriple.Lcls f) (T.toDiffusionTriple.cls f)) +
        (n⁻¹).toReal * ‖T.toDiffusionTriple.Lcls f‖ ^ 2 ≤ ‖T.toDiffusionTriple.Lcls f‖ ^ 2 := by
  have h := integral_CD T hCD f.2
  have e1 : -inner ℝ (T.toDiffusionTriple.Lcls f) (T.toDiffusionTriple.cls f) =
      ∫ x, T.Γ f.1 f.1 x ∂T.μ := by
    rw [DiffusionTriple.inner_Lcls_cls]; simp
  have e2 : ‖T.toDiffusionTriple.Lcls f‖ ^ 2 = ∫ x, T.L f.1 x * T.L f.1 x ∂T.μ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple f] with x hx
    rw [hx]
  rw [e1, e2]
  exact h

/-- **Prop. 3.3.16 (ii), integrated form.**  Under ESA (F10) and `CD(ρ,n)`, for every `u ∈ 𝒟(L)`:
`ρ (-⟪L u, u⟫) + n⁻¹ ‖L u‖² ≤ ‖L u‖²`.  (`-⟪Lu,u⟫ = ℰ(u)`, see `CD_form_domain`.) -/
theorem CD_integrated_domain {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) :
    ρ * (-inner ℝ (T.toDiffusionTriple.generator ⟨u, hu⟩) u) +
        (n⁻¹).toReal * ‖T.toDiffusionTriple.generator ⟨u, hu⟩‖ ^ 2 ≤
      ‖T.toDiffusionTriple.generator ⟨u, hu⟩‖ ^ 2 := by
  obtain ⟨a, ha1, ha2⟩ := T.esa u hu
  set Gu := T.toDiffusionTriple.generator ⟨u, hu⟩
  have hl1 : Tendsto (fun k => ρ * (-inner ℝ (T.toDiffusionTriple.Lcls (a k))
      (T.toDiffusionTriple.cls (a k))) + (n⁻¹).toReal * ‖T.toDiffusionTriple.Lcls (a k)‖ ^ 2)
      atTop (𝓝 (ρ * (-inner ℝ Gu u) + (n⁻¹).toReal * ‖Gu‖ ^ 2)) := by
    have h1 : Tendsto (fun k => inner ℝ (T.toDiffusionTriple.Lcls (a k))
        (T.toDiffusionTriple.cls (a k))) atTop (𝓝 (inner ℝ Gu u)) :=
      ha2.inner ha1
    have h2 : Tendsto (fun k => ‖T.toDiffusionTriple.Lcls (a k)‖) atTop (𝓝 ‖Gu‖) :=
      ha2.norm
    exact (h1.neg.const_mul ρ).add ((h2.pow 2).const_mul _)
  have hl2 : Tendsto (fun k => ‖T.toDiffusionTriple.Lcls (a k)‖ ^ 2) atTop (𝓝 (‖Gu‖ ^ 2)) :=
    ha2.norm.pow 2
  exact le_of_tendsto_of_tendsto' hl1 hl2 fun k => CD_integrated_cls T hCD (a k)

/-- The same in terms of the closed Dirichlet form: for `u ∈ 𝒟(L)`, `u ∈ 𝒟(ℰ)` and
`ρ ℰ(u) + n⁻¹ ‖L u‖² ≤ ‖L u‖²`. -/
theorem CD_form_domain {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) :
    ∃ hQ : u ∈ T.toDiffusionTriple.formDomain,
      ρ * T.toDiffusionTriple.closedForm ⟨u, hQ⟩ ⟨u, hQ⟩ +
          (n⁻¹).toReal * ‖T.toDiffusionTriple.generator ⟨u, hu⟩‖ ^ 2 ≤
        ‖T.toDiffusionTriple.generator ⟨u, hu⟩‖ ^ 2 := by
  obtain ⟨hQ, hform⟩ := (T.toDiffusionTriple.generator_iff_form u
    (T.toDiffusionTriple.generator ⟨u, hu⟩)).1 ⟨hu, rfl⟩
  refine ⟨hQ, ?_⟩
  rw [hform ⟨u, hQ⟩]
  exact CD_integrated_domain T hCD u hu

end FullTriple

end MarkovTriple.BGL
