import Mathlib
import MarkovTriple.BGL.Frozen.Classes

/-!
# Basic consequences of D1–D8

Lemmas (not frozen) justifying that the following items of the book are *consequences* of the
fields of `DiffusionTriple` rather than fields: D4 (`exists_bound_D4`), a.e.-linearity of `L`
(`L_add_ae`, `L_smul_ae`), well-definedness of `L` on a.e.-classes (`L_ae_zero_of_ae_zero`).
-/

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

lemma memLp2 {f : E → ℝ} (hf : f ∈ T.A₀) : MemLp f 2 T.μ := T.memLp f hf 2 (by norm_num) (by simp)

lemma integrable_of_mem {f : E → ℝ} (hf : f ∈ T.A₀) : Integrable f T.μ :=
  memLp_one_iff_integrable.1 (T.memLp f hf 1 le_rfl (by simp))

lemma coeFn_cls (f : T.A₀) : (T.cls f : E → ℝ) =ᵐ[T.μ] f.1 :=
  MemLp.coeFn_toLp (memLp2 T f.2)

lemma coeFn_Lcls (f : T.A₀) : (T.Lcls f : E → ℝ) =ᵐ[T.μ] T.L f.1 :=
  MemLp.coeFn_toLp (memLp2 T (T.L_mem f.1 f.2))

/-- If `d ∈ 𝒜₀` is orthogonal (in `L²`) to all of `𝒜₀`, then `d = 0` a.e. -/
lemma ae_zero_of_orth {d : E → ℝ} (hd : d ∈ T.A₀) (h : ∀ g ∈ T.A₀, ∫ x, g x * d x ∂T.μ = 0) :
    d =ᵐ[T.μ] 0 := by
  have hdd : d * d ∈ T.A₀ := T.A₀.mul_mem hd hd
  have h0 : ∫ x, d x * d x ∂T.μ = 0 := h d hd
  have hi : Integrable (fun x => d x * d x) T.μ := integrable_of_mem T hdd
  have := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (d x)) hi).1 h0
  filter_upwards [this] with x hx
  have : d x * d x = 0 := hx
  simpa using this

/-- Integrability of `g · L f`, `Γ(f,g)` for test functions. -/
lemma integrable_mul {f g : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀) :
    Integrable (fun x => f x * g x) T.μ := integrable_of_mem T (T.A₀.mul_mem hf hg)

/-- `⟪L f, g⟫ = ∫ g L f = -∫ Γ(f,g)` (integration by parts, in `L²`). -/
lemma inner_Lcls_cls (f g : T.A₀) :
    inner ℝ (T.Lcls f) (T.cls g) = -∫ x, T.Γ f.1 g.1 x ∂T.μ := by
  rw [MeasureTheory.L2.inner_def, ← T.ibp f.1 f.2 g.1 g.2]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_Lcls T f, coeFn_cls T g] with x h1 h2
  rw [h1, h2]
  simp

/-- **D4**: continuity of `g ↦ ∫ Γ(f,g)` for the `L²` norm (it follows from D5, D6). -/
theorem exists_bound_D4 (f : E → ℝ) (hf : f ∈ T.A₀) :
    ∃ C : ℝ, ∀ (g : E → ℝ) (hg : g ∈ T.A₀),
      |∫ x, T.Γ f g x ∂T.μ| ≤ C * ‖T.cls ⟨g, hg⟩‖ := by
  refine ⟨‖T.Lcls ⟨f, hf⟩‖, fun g hg => ?_⟩
  have h := inner_Lcls_cls T ⟨f, hf⟩ ⟨g, hg⟩
  have h2 : ∫ x, T.Γ f g x ∂T.μ = -inner ℝ (T.Lcls ⟨f, hf⟩) (T.cls ⟨g, hg⟩) := by
    rw [h]; simp
  rw [h2, abs_neg]
  exact abs_real_inner_le_norm _ _

/-- `L` is additive on `𝒜₀`, a.e. (consequence of D3, D5, D6). -/
theorem L_add_ae {f g : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀) :
    T.L (f + g) =ᵐ[T.μ] T.L f + T.L g := by
  have hfg : f + g ∈ T.A₀ := T.A₀.add_mem hf hg
  have hd : T.L (f + g) - T.L f - T.L g ∈ T.A₀ :=
    T.A₀.sub_mem (T.A₀.sub_mem (T.L_mem _ hfg) (T.L_mem _ hf)) (T.L_mem _ hg)
  have key := ae_zero_of_orth T hd (fun h hh => by
    have i1 := integrable_mul T hh (T.L_mem _ hfg)
    have i2 := integrable_mul T hh (T.L_mem _ hf)
    have i3 := integrable_mul T hh (T.L_mem _ hg)
    have e1 : (fun x => h x * (T.L (f + g) - T.L f - T.L g) x) =
        fun x => h x * T.L (f + g) x - h x * T.L f x - h x * T.L g x := by
      funext x; simp only [Pi.sub_apply]; ring
    rw [e1, integral_sub (f := fun x => h x * T.L (f + g) x - h x * T.L f x)
      (g := fun x => h x * T.L g x) (i1.sub i2) i3,
      integral_sub (f := fun x => h x * T.L (f + g) x) (g := fun x => h x * T.L f x) i1 i2,
      T.ibp _ hfg _ hh, T.ibp _ hf _ hh, T.ibp _ hg _ hh]
    have j1 := integrable_of_mem T (T.Γ_mem _ hf _ hh)
    have j2 := integrable_of_mem T (T.Γ_mem _ hg _ hh)
    have : ∫ x, T.Γ (f + g) h x ∂T.μ = ∫ x, T.Γ f h x ∂T.μ + ∫ x, T.Γ g h x ∂T.μ := by
      rw [integral_congr_ae (T.Γ_add f hf g hg h hh)]
      exact integral_add j1 j2
    rw [this]; ring)
  filter_upwards [key] with x hx
  simp only [Pi.sub_apply, Pi.zero_apply] at hx
  simp only [Pi.add_apply]; linarith

/-- `L` is homogeneous on `𝒜₀`, a.e. -/
theorem L_smul_ae (c : ℝ) {f : E → ℝ} (hf : f ∈ T.A₀) : T.L (c • f) =ᵐ[T.μ] c • T.L f := by
  have hcf : c • f ∈ T.A₀ := T.A₀.smul_mem c hf
  have hd : T.L (c • f) - c • T.L f ∈ T.A₀ :=
    T.A₀.sub_mem (T.L_mem _ hcf) (T.A₀.smul_mem c (T.L_mem _ hf))
  have key := ae_zero_of_orth T hd (fun h hh => by
    have i1 := integrable_mul T hh (T.L_mem _ hcf)
    have i2 := integrable_mul T hh (T.L_mem _ hf)
    have e1 : (fun x => h x * (T.L (c • f) - c • T.L f) x) =
        fun x => h x * T.L (c • f) x - c * (h x * T.L f x) := by
      funext x; simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e1, integral_sub (f := fun x => h x * T.L (c • f) x) (g := fun x => c * (h x * T.L f x))
      i1 (i2.const_mul c), integral_const_mul, T.ibp _ hcf _ hh, T.ibp _ hf _ hh]
    have j1 := integrable_of_mem T (T.Γ_mem _ hf _ hh)
    have : ∫ x, T.Γ (c • f) h x ∂T.μ = c * ∫ x, T.Γ f h x ∂T.μ := by
      rw [integral_congr_ae (T.Γ_smul c f hf h hh)]
      simp only [Pi.smul_apply, smul_eq_mul]
      exact integral_const_mul _ _
    rw [this]; ring)
  filter_upwards [key] with x hx
  simp only [Pi.sub_apply, Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at hx ⊢
  linarith

end DiffusionTriple

end MarkovTriple.BGL
