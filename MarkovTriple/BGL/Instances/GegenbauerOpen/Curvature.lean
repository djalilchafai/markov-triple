import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Diffusion
import MarkovTriple.BGL.Frozen.Gamma2

/-!
# `Γ₂` and curvature of the Gegenbauer triple on `(-1,1)` (S2b)

`Γ₂(f) = (1-x²)² f''² - 2x(1-x²) f' f'' + (3+x²) f'²` for smooth `f`, i.e. the Bochner form
`((1-x²) f'' - x f')² + 3 x² f'² + 3 (1-x²) f'²` (`|Hess f|² + Ric(∇f,∇f)`, `Ric = 3`, zonal functions
on `S⁴`), whence `CD(3, 4)`.  See `STATEMENTS_R22_E2.md`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GegenbauerOpen

lemma go_ΓA {f g : ℝ → ℝ} (hf : Lebesgue.Sm f) (hg : Lebesgue.Sm g) (x : ℝ) :
    goDiff.ΓA f g x = (1 - x ^ 2) * (deriv f x * deriv g x) := by
  show (goL (f * g) x - f x * goL g x - g x * goL f x) / 2 = _
  have h1 : goL (f * g) x = (1 - x ^ 2) * Lebesgue.Lf (f * g) x - 4 * x * deriv (f * g) x := rfl
  rw [h1, Lebesgue.Lf_mul hf hg, Lebesgue.deriv_mul_sm hf hg]
  simp only [goL, Lebesgue.Lf, Pi.add_apply, Pi.mul_apply]
  ring

lemma hw1 (x : ℝ) : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-(2 * x)) x := by
  have := (hasDerivAt_pow 2 x).const_sub 1
  convert this using 1
  simp

lemma sm_goL {f : ℝ → ℝ} (hf : Lebesgue.Sm f) : Lebesgue.Sm (goL f) :=
  (sm_w1.mul hf.deriv'.deriv').sub (sm_w4.mul hf.deriv')

lemma hasDerivAt_goL {f : ℝ → ℝ} (hf : Lebesgue.Sm f) (x : ℝ) :
    HasDerivAt (goL f) ((1 - x ^ 2) * deriv (deriv (deriv f)) x - 6 * x * deriv (deriv f) x
      - 4 * deriv f x) x := by
  have h1 := hf.deriv'.hasDerivAt x
  have h2 := hf.deriv'.deriv'.hasDerivAt x
  have h3 := hf.deriv'.deriv'.deriv'.hasDerivAt x
  have a := (hw1 x).mul h2
  have b := (((hasDerivAt_id x).const_mul 4)).mul h1
  have := a.sub b
  refine HasDerivAt.congr_deriv (f := goL f) (by exact this) ?_
  simp only [id]
  ring

/-- `Γ₂(f) = (1-x²)² f''² - 2x(1-x²) f' f'' + (3+x²) f'²` for smooth `f`. -/
theorem go_Γ₂_eq {f : ℝ → ℝ} (hf : Lebesgue.Sm f) (x : ℝ) :
    goDiff.Γ₂ f f x = (1 - x ^ 2) ^ 2 * deriv (deriv f) x ^ 2
      - 2 * x * (1 - x ^ 2) * (deriv f x * deriv (deriv f) x) + (3 + x ^ 2) * deriv f x ^ 2 := by
  have e1 : goDiff.ΓA f f = fun y => (1 - y ^ 2) * (deriv f y * deriv f y) :=
    funext fun y => go_ΓA hf hf y
  have e2 : goDiff.ΓA f (goL f) x = (1 - x ^ 2) * (deriv f x * deriv (goL f) x) :=
    go_ΓA hf (sm_goL hf) x
  have e3 : goDiff.ΓA (goL f) f x = (1 - x ^ 2) * (deriv (goL f) x * deriv f x) :=
    go_ΓA (sm_goL hf) hf x
  have h1 := hf.deriv'.hasDerivAt
  have h2 := hf.deriv'.deriv'.hasDerivAt
  have h3 := hf.deriv'.deriv'.deriv'.hasDerivAt
  have dg1 : deriv (fun y => (1 - y ^ 2) * (deriv f y * deriv f y)) = fun y =>
      -(2 * y) * (deriv f y * deriv f y)
        + (1 - y ^ 2) * (deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y) := by
    funext y
    exact ((hw1 y).mul ((h1 y).mul (h1 y))).deriv
  have dg2 : deriv (fun y => -(2 * y) * (deriv f y * deriv f y)
        + (1 - y ^ 2) * (deriv (deriv f) y * deriv f y + deriv f y * deriv (deriv f) y)) x =
      (-(2 * 1)) * (deriv f x * deriv f x) + (-(2 * x)) * (deriv (deriv f) x * deriv f x
        + deriv f x * deriv (deriv f) x)
      + (-(2 * x) * (deriv (deriv f) x * deriv f x + deriv f x * deriv (deriv f) x)
        + (1 - x ^ 2) * ((deriv (deriv (deriv f)) x * deriv f x + deriv (deriv f) x * deriv (deriv f) x)
          + (deriv (deriv f) x * deriv (deriv f) x + deriv f x * deriv (deriv (deriv f)) x))) := by
    have hA := (((hasDerivAt_id x).const_mul 2).neg).mul ((h1 x).mul (h1 x))
    have hB := (hw1 x).mul ((((h2 x).mul (h1 x)).add ((h1 x).mul (h2 x))))
    have hAB := hA.add hB
    refine hAB.deriv.trans ?_
    simp only [id, mul_one, Pi.mul_apply, Pi.add_apply, Pi.neg_apply]
  show (goL (goDiff.ΓA f f) x - goDiff.ΓA f (goL f) x - goDiff.ΓA (goL f) f x) / 2 = _
  rw [e1, e2, e3]
  have hd : deriv (goL f) x = (1 - x ^ 2) * deriv (deriv (deriv f)) x - 6 * x * deriv (deriv f) x
      - 4 * deriv f x := (hasDerivAt_goL hf x).deriv
  simp only [goL]
  rw [dg1, dg2, hd]
  ring

/-- `CD(ρ, n)` for the Gegenbauer triple, in the shape of `FullTriple.CD` (pointwise on `(-1,1)`, on all smooth
`f`; `FullTriple.CD` itself is unavailable since no `FullTriple` over `goDiff` is constructed). -/
def GoCD (ρ : ℝ) (n : ℝ≥0∞) : Prop :=
  1 ≤ n ∧ ∀ f : ℝ → ℝ, Lebesgue.Sm f → ∀ x ∈ Ioo (-1 : ℝ) 1,
    ρ * goDiff.ΓA f f x + (n⁻¹).toReal * (goDiff.L f x) ^ 2 ≤ goDiff.Γ₂ f f x

/-- **S2b**: `CD(ρ, n)` for every `ρ ≤ 3` and `n ∈ [4, ∞]`; in particular `CD(3, 4) = CD(n-1, n)`, `n = 4`. -/
theorem goDiff_CD {ρ : ℝ} {n : ℝ≥0∞} (hρ : ρ ≤ 3) (hn : 4 ≤ n) : GoCD ρ n := by
  refine ⟨le_trans (by norm_num) hn, fun f hf x hx => ?_⟩
  rw [go_Γ₂_eq hf, go_ΓA hf hf]
  have h1 : (n⁻¹).toReal ≤ 1 / 4 := by
    have : n⁻¹ ≤ 4⁻¹ := ENNReal.inv_le_inv.2 hn
    have := ENNReal.toReal_mono (by simp) this
    simpa using this
  have h0 : 0 ≤ (n⁻¹).toReal := ENNReal.toReal_nonneg
  have hL : goDiff.L f x = (1 - x ^ 2) * deriv (deriv f) x - 4 * x * deriv f x := rfl
  rw [hL]
  have hw : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  set a := deriv f x
  set b := deriv (deriv f) x
  have hΓ : 0 ≤ (1 - x ^ 2) * (a * a) := mul_nonneg hw (mul_self_nonneg a)
  have hρΓ : ρ * ((1 - x ^ 2) * (a * a)) ≤ 3 * ((1 - x ^ 2) * (a * a)) :=
    mul_le_mul_of_nonneg_right hρ hΓ
  have hsq : 0 ≤ ((1 - x ^ 2) * b - 4 * x * a) ^ 2 := sq_nonneg _
  have hmul : (n⁻¹).toReal * ((1 - x ^ 2) * b - 4 * x * a) ^ 2 ≤
      1 / 4 * ((1 - x ^ 2) * b - 4 * x * a) ^ 2 := mul_le_mul_of_nonneg_right h1 hsq
  nlinarith [sq_nonneg ((1 - x ^ 2) * b - x * a + x * a), sq_nonneg ((1 - x ^ 2) * b)]

end MarkovTriple.BGL.Instances.GegenbauerOpen
