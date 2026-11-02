import Mathlib
import MarkovTriple.BGL.Theory.Strong.Reinforced
import MarkovTriple.BGL.Theory.Gamma2Integral

/-!
# Energy estimates for `Γ` on test functions

For `a, b ∈ 𝒜₀` with `Γ(b) ≤ B` a.e.: `‖Γ(a,b)‖₂² ≤ B · ℰ(a)` and `ℰ(a) = ∫Γ(a) = -∫ a L a ≤ ‖a‖₂ ‖La‖₂`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma A₀_memA {a : E → ℝ} (ha : a ∈ T.A₀) : a ∈ T.A := T.A₀_le a ha

/-- `ℰ(a) = ∫ Γ(a,a) = -∫ a L a`. -/
lemma int_G_self {a : E → ℝ} (ha : a ∈ T.A₀) : ∫ x, G T a a x ∂T.μ = -∫ x, a x * T.L a x ∂T.μ :=
  (T.ibp_A a (A₀_memA ha) a ha).1

lemma int_G_self_le {a : E → ℝ} (ha : a ∈ T.A₀) :
    ∫ x, G T a a x ∂T.μ ≤
      ‖T.toDiffusionTriple.cls ⟨a, ha⟩‖ * ‖T.toDiffusionTriple.cls ⟨T.L a, T.L_mem a ha⟩‖ := by
  have hLa := T.L_mem a ha
  have h := real_inner_le_norm (T.toDiffusionTriple.cls ⟨a, ha⟩)
    (T.toDiffusionTriple.cls ⟨T.L a, hLa⟩)
  have e : inner ℝ (T.toDiffusionTriple.cls ⟨a, ha⟩) (T.toDiffusionTriple.cls ⟨T.L a, hLa⟩) =
      ∫ x, a x * T.L a x ∂T.μ := by
    rw [L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [T.toDiffusionTriple.coeFn_cls ⟨a, ha⟩,
      T.toDiffusionTriple.coeFn_cls ⟨T.L a, hLa⟩] with x h1 h2
    rw [h1, h2]
  have hneg : -∫ x, a x * T.L a x ∂T.μ ≤ ‖T.toDiffusionTriple.cls ⟨a, ha⟩‖ *
      ‖T.toDiffusionTriple.cls ⟨T.L a, hLa⟩‖ := by
    have h' := real_inner_le_norm (-(T.toDiffusionTriple.cls ⟨a, ha⟩))
      (T.toDiffusionTriple.cls ⟨T.L a, hLa⟩)
    rw [inner_neg_left, norm_neg, e] at h'
    exact h'
  rw [int_G_self ha]; exact hneg

/-- `∫ Γ(a,b)² ≤ B ∫ Γ(a)` if `Γ(b) ≤ B`. -/
lemma sq_int_G_le {a b : E → ℝ} (ha : a ∈ T.A₀) (hb : b ∈ T.A₀) {B : ℝ}
    (hB : G T b b ≤ᵐ[T.μ] fun _ => B) :
    ∫ x, (G T a b x) ^ 2 ∂T.μ ≤ B * ∫ x, G T a a x ∂T.μ := by
  have hΓaa : G T a a ∈ T.A₀ := T.ΓA_self_mem_A₀ ha
  have hΓab : G T a b ∈ T.A₀ := ΓA_mem_A₀ T (A₀_memA ha) hb
  have i1 : Integrable (fun x => (G T a b x) ^ 2) T.μ := by
    have := DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.A₀.mul_mem hΓab hΓab)
    exact this.congr (Eventually.of_forall fun x => by simp [sq])
  have i2 : Integrable (G T a a) T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple hΓaa
  rw [← integral_const_mul]
  refine integral_mono_ae i1 (i2.const_mul B) ?_
  filter_upwards [ExtendedAlgebra.ΓA_cs T.extendedAlgebra (A₀_memA ha) (A₀_memA hb), hB,
    T.ΓA_nonneg a (A₀_memA ha)] with x h1 h2 h3
  calc (G T a b x) ^ 2 ≤ G T a a x * G T b b x := h1
    _ ≤ G T a a x * B := mul_le_mul_of_nonneg_left h2 h3
    _ = B * G T a a x := by ring

end FullTriple

end MarkovTriple.BGL
