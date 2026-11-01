import Mathlib
import MarkovTriple.BGL.Frozen.Semigroup

/-!
# Elementary facts on the Friedrichs semigroup and generator of a diffusion triple (not frozen)
-/

open MeasureTheory
open scoped NNReal LinearPMap

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

/-- `𝒜₀ ⊂ 𝒟(L)` and `L` on the class of `f ∈ 𝒜₀` is the class of `L f` (D7: the generator extends
`L|𝒜₀`). -/
theorem generator_cls (f : T.A₀) (h : T.cls f ∈ T.generator.domain) :
    T.generator ⟨T.cls f, h⟩ = T.Lcls f := by
  obtain ⟨h', hG⟩ := (formData T).generator_extends ⟨clsₗ T f, ⟨f, rfl⟩⟩
  have h2 : formA T ⟨clsₗ T f, ⟨f, rfl⟩⟩ = -T.Lcls f := formA_apply T f
  have h3 : (formData T).A ⟨clsₗ T f, ⟨f, rfl⟩⟩ = -T.Lcls f := h2
  rw [h3, neg_neg] at hG
  exact hG

theorem cls_mem_generator_domain (f : T.A₀) : T.cls f ∈ T.generator.domain :=
  ((formData T).generator_extends ⟨clsₗ T f, ⟨f, rfl⟩⟩).1

/-- If `L f = 0` a.e. for all test functions, the semigroup fixes the classes of test functions. -/
theorem semigroup_cls_of_L_zero (hL0 : ∀ f ∈ T.A₀, T.L f =ᵐ[T.μ] 0) (t : ℝ≥0) (f : T.A₀) :
    T.semigroup t (T.cls f) = T.cls f := by
  have hL : T.Lcls f = 0 := by
    refine Lp.ext ?_
    filter_upwards [coeFn_Lcls T f, Lp.coeFn_zero ℝ 2 T.μ, hL0 f.1 f.2] with x h1 h2 h3
    rw [h1, h2]; exact h3
  have hR := (formData T).R_resolvent (⟨clsₗ T f, ⟨f, rfl⟩⟩ : (formData T).Dom)
  have hA : (formData T).opA (⟨clsₗ T f, ⟨f, rfl⟩⟩ : (formData T).Dom) = 0 := by
    show formA T ⟨clsₗ T f, ⟨f, rfl⟩⟩ = 0
    rw [formA_apply, hL]; simp
  rw [hA, add_zero] at hR
  have hR2 : (formData T).R (T.cls f) = T.cls f := hR
  have hR' : (formData T).R (T.cls f) = ((1 + (0 : ℝ))⁻¹) • T.cls f := by
    rw [hR2]; simp
  have := (formData T).semigroup_eigen (le_refl (0 : ℝ)) hR' t
  simpa [semigroup] using this

end DiffusionTriple

end MarkovTriple.BGL
