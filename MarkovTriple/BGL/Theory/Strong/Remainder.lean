import Mathlib
import MarkovTriple.BGL.Theory.Strong.Expand

/-!
# The `L²` remainder of `Γ` along a curve (abstract, function level)

If `pr = x + h g + ρ` (all in `𝒜₀`) then
`Γ(pr) − Γ(x) − 2hΓ(x,g) = Γ(ρ,pr) + Γ(ρ,x) + hΓ(g,ρ) + h²Γ(g)` a.e. and, if `Γ(x), Γ(pr) ≤ B`, `Γ(g) ≤ B'`,
`∫ (Γ(pr) − Γ(x) − 2hΓ(x,g))² ≤ 4 (2B + h² B') ℰ(ρ) + 4 h⁴ ∫ Γ(g)²`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma remainder_eq {x g ρ pr : E → ℝ} (hx : x ∈ T.A) (hg : g ∈ T.A) (hρ : ρ ∈ T.A) (hpr : pr ∈ T.A)
    (h : ℝ) (heq : pr = fun w => x w + h * g w + ρ w) :
    (fun w => G T pr pr w - G T x x w - 2 * h * G T x g w) =ᵐ[T.μ]
      fun w => G T ρ pr w + G T ρ x w + h * G T g ρ w + h ^ 2 * G T g g w := by
  have e1 := G_expand_left hx hg hρ hpr h
  have e2 := G_expand_right hx hg hρ hx h
  have e3 := G_expand_right hx hg hρ hg h
  have e1' : G T pr pr =ᵐ[T.μ] fun w => G T x pr w + h * G T g pr w + G T ρ pr w := by
    rw [heq] at e1 ⊢
    exact e1
  subst heq
  have e2' := G_expand_right hx hg hρ hx h
  filter_upwards [e1', e2, e3] with w h1 h2 h3
  have c1 : G T g x w = G T x g w := by rw [G_comm]
  have c2 : G T ρ x w = G T x ρ w := by rw [G_comm]
  linear_combination h1 + h2 + h * h3 + h * c1 - c2

lemma integrable_G_sq {a b : E → ℝ} (ha : a ∈ T.A₀) (hb : b ∈ T.A₀) :
    Integrable (fun w => (G T a b w) ^ 2) T.μ := by
  have hΓ : G T a b ∈ T.A₀ := ΓA_mem_A₀ T (A₀_memA ha) hb
  have := DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.A₀.mul_mem hΓ hΓ)
  exact this.congr (Eventually.of_forall fun x => by simp [sq])

/-- `L²` bound of the remainder. -/
theorem remainder_sq_le {x g ρ pr : E → ℝ} (hx : x ∈ T.A₀) (hg : g ∈ T.A₀) (hρ : ρ ∈ T.A₀)
    (hpr : pr ∈ T.A₀) (h : ℝ) (heq : pr = fun w => x w + h * g w + ρ w) {B B' : ℝ}
    (hBx : G T x x ≤ᵐ[T.μ] fun _ => B) (hBpr : G T pr pr ≤ᵐ[T.μ] fun _ => B)
    (hBg : G T g g ≤ᵐ[T.μ] fun _ => B') :
    ∫ w, (G T pr pr w - G T x x w - 2 * h * G T x g w) ^ 2 ∂T.μ ≤
      4 * ((B + B + h ^ 2 * B') * ∫ w, G T ρ ρ w ∂T.μ + h ^ 4 * ∫ w, (G T g g w) ^ 2 ∂T.μ) := by
  have hxA := A₀_memA hx
  have hgA := A₀_memA hg
  have hρA := A₀_memA hρ
  have hprA := A₀_memA hpr
  have hr := remainder_eq hxA hgA hρA hprA h heq
  have i1 := integrable_G_sq (T := T) hρ hpr
  have i2 := integrable_G_sq (T := T) hρ hx
  have i3 := integrable_G_sq (T := T) hg hρ
  have i4 := integrable_G_sq (T := T) hg hg
  have b1 := sq_int_G_le hρ hpr hBpr
  have b2 := sq_int_G_le hρ hx hBx
  have b3 := sq_int_G_le hρ hg hBg
  have e3 : ∫ w, (G T g ρ w) ^ 2 ∂T.μ = ∫ w, (G T ρ g w) ^ 2 ∂T.μ :=
    integral_congr_ae (Eventually.of_forall fun w => by rw [G_comm g ρ])
  have hB'0 : True := trivial
  -- pointwise bound
  have hint : ∀ᵐ w ∂T.μ, (G T pr pr w - G T x x w - 2 * h * G T x g w) ^ 2 ≤
      4 * ((G T ρ pr w) ^ 2 + (G T ρ x w) ^ 2 + h ^ 2 * (G T g ρ w) ^ 2 +
        h ^ 4 * (G T g g w) ^ 2) := by
    filter_upwards [hr] with w hw
    rw [hw]
    nlinarith [sq_nonneg (G T ρ pr w - G T ρ x w), sq_nonneg (G T ρ pr w + G T ρ x w - h * G T g ρ w - h ^ 2 * G T g g w),
      sq_nonneg (G T ρ pr w - h * G T g ρ w), sq_nonneg (G T ρ pr w - h ^ 2 * G T g g w),
      sq_nonneg (G T ρ x w - h * G T g ρ w), sq_nonneg (G T ρ x w - h ^ 2 * G T g g w),
      sq_nonneg (h * G T g ρ w - h ^ 2 * G T g g w)]
  have iR : Integrable (fun w => (G T pr pr w - G T x x w - 2 * h * G T x g w) ^ 2) T.μ := by
    have hΓpp : G T pr pr ∈ T.A₀ := T.ΓA_self_mem_A₀ hpr
    have hΓxx : G T x x ∈ T.A₀ := T.ΓA_self_mem_A₀ hx
    have hΓxg : G T x g ∈ T.A₀ := ΓA_mem_A₀ T hxA hg
    have hm : (fun w => G T pr pr w - G T x x w - 2 * h * G T x g w) ∈ T.A₀ := by
      have : (fun w => G T pr pr w - G T x x w - 2 * h * G T x g w) =
          G T pr pr - G T x x - (2 * h) • G T x g := by funext w; simp
      rw [this]; exact T.A₀.sub_mem (T.A₀.sub_mem hΓpp hΓxx) (T.A₀.smul_mem _ hΓxg)
    have := DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.A₀.mul_mem hm hm)
    exact this.congr (Eventually.of_forall fun x => by simp [sq])
  have iS : Integrable (fun w => 4 * ((G T ρ pr w) ^ 2 + (G T ρ x w) ^ 2 +
      h ^ 2 * (G T g ρ w) ^ 2 + h ^ 4 * (G T g g w) ^ 2)) T.μ :=
    (((i1.add i2).add (i3.const_mul _)).add (i4.const_mul _)).const_mul 4
  have h1 := integral_mono_ae iR iS hint
  have h2 : ∫ w, 4 * ((G T ρ pr w) ^ 2 + (G T ρ x w) ^ 2 + h ^ 2 * (G T g ρ w) ^ 2 +
      h ^ 4 * (G T g g w) ^ 2) ∂T.μ =
      4 * (∫ w, (G T ρ pr w) ^ 2 ∂T.μ + ∫ w, (G T ρ x w) ^ 2 ∂T.μ +
        h ^ 2 * ∫ w, (G T g ρ w) ^ 2 ∂T.μ + h ^ 4 * ∫ w, (G T g g w) ^ 2 ∂T.μ) := by
    have j3 : Integrable (fun w => h ^ 2 * (G T g ρ w) ^ 2) T.μ := i3.const_mul _
    have j4 : Integrable (fun w => h ^ 4 * (G T g g w) ^ 2) T.μ := i4.const_mul _
    have j12 : Integrable (fun w => (G T ρ pr w) ^ 2 + (G T ρ x w) ^ 2) T.μ := i1.add i2
    have j123 : Integrable (fun w => (G T ρ pr w) ^ 2 + (G T ρ x w) ^ 2 +
        h ^ 2 * (G T g ρ w) ^ 2) T.μ := j12.add j3
    rw [integral_const_mul]
    congr 1
    rw [integral_add (f := fun w => (G T ρ pr w) ^ 2 + (G T ρ x w) ^ 2 + h ^ 2 * (G T g ρ w) ^ 2)
      (g := fun w => h ^ 4 * (G T g g w) ^ 2) j123 j4,
      integral_add (f := fun w => (G T ρ pr w) ^ 2 + (G T ρ x w) ^ 2)
      (g := fun w => h ^ 2 * (G T g ρ w) ^ 2) j12 j3,
      integral_add (f := fun w => (G T ρ pr w) ^ 2) (g := fun w => (G T ρ x w) ^ 2) i1 i2,
      integral_const_mul, integral_const_mul]
  rw [h2] at h1
  refine h1.trans ?_
  have hh2 : 0 ≤ h ^ 2 := sq_nonneg h
  have : h ^ 2 * ∫ w, (G T g ρ w) ^ 2 ∂T.μ ≤ h ^ 2 * (B' * ∫ w, G T ρ ρ w ∂T.μ) := by
    rw [e3]; exact mul_le_mul_of_nonneg_left b3 hh2
  nlinarith [b1, b2, this]

end FullTriple

end MarkovTriple.BGL
