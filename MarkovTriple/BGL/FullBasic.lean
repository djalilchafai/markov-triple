import Mathlib
import MarkovTriple.BGL.Basic
import MarkovTriple.BGL.Frozen.FullTriple

/-!
# Consequences of F1, F4 for a full triple (not frozen)

* `ΓA f g = ½ • (L (f g) − f L g − g L f)` as functions;
* `ΓA f g ∈ 𝒜` (F4) and, for `g ∈ 𝒜₀`, `ΓA f g ∈ 𝒜₀` (remark after Def. 3.3.1, from the ideal property);
* integrability of the three terms of F7, so that F7 is a statement about genuine integrals.
-/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : FullTriple E)

namespace FullTriple

lemma ΓA_eq (f g : E → ℝ) :
    T.toDiffusionTriple.ΓA f g = (1 / 2 : ℝ) • (T.L (f * g) - f * T.L g - g * T.L f) := by
  funext x
  simp only [DiffusionTriple.ΓA, Pi.smul_apply, Pi.sub_apply, Pi.mul_apply, smul_eq_mul]
  ring

/-- F4: `Γ(f,g) ∈ 𝒜` for `f, g ∈ 𝒜`. -/
theorem ΓA_mem_A {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) :
    T.toDiffusionTriple.ΓA f g ∈ T.A := by
  rw [ΓA_eq]
  exact T.A.smul_mem (T.A.sub_mem (T.A.sub_mem (T.L_mem_A _ (T.A.mul_mem hf hg))
    (T.A.mul_mem hf (T.L_mem_A _ hg))) (T.A.mul_mem hg (T.L_mem_A _ hf))) _

/-- Remark after Def. 3.3.1: `Γ(f,h) ∈ 𝒜₀` for `f ∈ 𝒜`, `h ∈ 𝒜₀` (from the ideal property). -/
theorem ΓA_mem_A₀ {f h : E → ℝ} (hf : f ∈ T.A) (hh : h ∈ T.A₀) :
    T.toDiffusionTriple.ΓA f h ∈ T.A₀ := by
  rw [ΓA_eq]
  have h1 : f * h ∈ T.A₀ := by rw [mul_comm]; exact T.ideal f hf h hh
  have h2 : f * T.L h ∈ T.A₀ := by
    rw [mul_comm]; exact T.ideal f hf _ (T.L_mem _ hh)
  have h3 : h * T.L f ∈ T.A₀ := T.ideal _ (T.L_mem_A f hf) h hh
  exact T.A₀.smul_mem _ (T.A₀.sub_mem (T.A₀.sub_mem (T.L_mem _ h1) h2) h3)

/-- The three terms of F7 are integrable (so F7 is about genuine integrals). -/
theorem integrable_F7 {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A₀) :
    Integrable (T.toDiffusionTriple.ΓA f g) T.μ ∧ Integrable (fun x => g x * T.L f x) T.μ ∧
      Integrable (fun x => f x * T.L g x) T.μ := by
  refine ⟨DiffusionTriple.integrable_of_mem T.toDiffusionTriple (ΓA_mem_A₀ T hf hg),
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.ideal _ (T.L_mem_A f hf) g hg), ?_⟩
  have h : f * T.L g ∈ T.A₀ := by
    rw [mul_comm]; exact T.ideal f hf _ (T.L_mem _ hg)
  exact DiffusionTriple.integrable_of_mem T.toDiffusionTriple h

end FullTriple

end MarkovTriple.BGL
