import Mathlib
import MarkovTriple.BGL.Theory.Interp.EntropyHelp
import MarkovTriple.BGL.Theory.Strong.Interpolation
import MarkovTriple.BGL.Theory.Strong.Product
import MarkovTriple.BGL.Analysis.BE.Cut

/-!
# Chain rule for `Γ₂` on `𝒜` (the computation behind `I' = -2J`, BGL Prop. 5.7.1)

`Γ₂(ψ∘f) = ψ'(f)²Γ₂(f) + ψ'(f)ψ''(f) Γ(f,Γ(f)) + ψ''(f)² Γ(f)²` a.e., for smooth `ψ` and `f ∈ 𝒜`
(`ψ'''` cancels).  Derived from the definition `Γ₂ = ½(LΓ(·) − 2Γ(·, L·))` and the change-of-variables formulas
`ΓA_comp_left`, `L_comp` (F6) and the Leibniz rules; no Hessian is used.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma contDiff_deriv' {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2

/-- `Γ₂(ψ∘f)` for smooth `ψ`. -/
theorem Γ₂_comp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) {f : E → ℝ} (hf : f ∈ T.A) :
    T.toDiffusionTriple.Γ₂ (fun x => ψ (f x)) (fun x => ψ (f x)) =ᵐ[T.μ] fun x =>
      deriv ψ (f x) ^ 2 * T.toDiffusionTriple.Γ₂ f f x +
        deriv ψ (f x) * deriv (deriv ψ) (f x) * G T f (G T f f) x +
        deriv (deriv ψ) (f x) ^ 2 * G T f f x ^ 2 := by
  have hψ1 := contDiff_deriv' hψ
  have hψ2 := contDiff_deriv' hψ1
  have hψ3 := contDiff_deriv' hψ2
  set B : ℝ → ℝ := fun y => deriv ψ y ^ 2 with hBdef
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hψ1.pow 2
  have hB1 : ∀ y, deriv B y = 2 * deriv ψ y * deriv (deriv ψ) y := by
    intro y
    have h1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) y) y :=
      ((hψ1.differentiable (by simp)) y).hasDerivAt
    have h : HasDerivAt B (2 * deriv ψ y * deriv (deriv ψ) y) y := by
      have := h1.pow 2
      convert this using 1
      simp
    exact h.deriv
  have hB2 : ∀ y, deriv (deriv B) y =
      2 * deriv (deriv ψ) y ^ 2 + 2 * deriv ψ y * deriv (deriv (deriv ψ)) y := by
    intro y
    have e : deriv B = fun y => 2 * deriv ψ y * deriv (deriv ψ) y := funext hB1
    rw [e]
    have h1 : HasDerivAt (deriv ψ) (deriv (deriv ψ) y) y :=
      ((hψ1.differentiable (by simp)) y).hasDerivAt
    have h2 : HasDerivAt (deriv (deriv ψ)) (deriv (deriv (deriv ψ)) y) y :=
      ((hψ2.differentiable (by simp)) y).hasDerivAt
    have h : HasDerivAt (fun y => 2 * deriv ψ y * deriv (deriv ψ) y)
        (2 * deriv (deriv ψ) y ^ 2 + 2 * deriv ψ y * deriv (deriv (deriv ψ)) y) y := by
      have := (h1.const_mul 2).mul h2
      convert this using 1
      ring
    exact h.deriv
  have hX : G T f f ∈ T.A := G_mem hf hf
  have hQ : T.L f ∈ T.A := L_memA hf
  have hu : (fun x => ψ (f x)) ∈ T.A := comp_mem_A T hψ hf
  have ha : (fun x => deriv ψ (f x)) ∈ T.A := comp_mem_A T hψ1 hf
  have hb : (fun x => deriv (deriv ψ) (f x)) ∈ T.A := comp_mem_A T hψ2 hf
  have hc : (fun x => deriv (deriv (deriv ψ)) (f x)) ∈ T.A := comp_mem_A T hψ3 hf
  have hBf : (fun x => B (f x)) ∈ T.A := comp_mem_A T hB hf
  have hBX : (fun x => B (f x)) * G T f f ∈ T.A := T.A.mul_mem hBf hX
  have hLu : T.L (fun x => ψ (f x)) ∈ T.A := L_memA hu
  have haQ : (fun x => deriv ψ (f x)) * T.L f ∈ T.A := T.A.mul_mem ha hQ
  have hbX : (fun x => deriv (deriv ψ) (f x)) * G T f f ∈ T.A := T.A.mul_mem hb hX
  have hsum : (fun x => deriv ψ (f x)) * T.L f + (fun x => deriv (deriv ψ) (f x)) * G T f f ∈ T.A :=
    T.A.add_mem haQ hbX
  -- (i)-(ii)
  have i1 : G T (fun x => ψ (f x)) (fun x => ψ (f x)) =ᵐ[T.μ] (fun x => B (f x)) * G T f f :=
    ΓA_comp_comp T hψ hf
  have i2 : T.L (G T (fun x => ψ (f x)) (fun x => ψ (f x))) =ᵐ[T.μ]
      T.L ((fun x => B (f x)) * G T f f) :=
    L_congr_A T (G_mem hu hu) hBX i1
  have i3 : T.L (fun x => B (f x)) =ᵐ[T.μ] fun x =>
      deriv B (f x) * T.L f x + deriv (deriv B) (f x) * G T f f x := L_comp T hB hf
  have i4 : G T (fun x => B (f x)) (G T f f) =ᵐ[T.μ] fun x => deriv B (f x) * G T f (G T f f) x :=
    ΓA_comp_left T hB hf hX
  -- (iv)-(viii)
  have j1 : T.L (fun x => ψ (f x)) =ᵐ[T.μ]
      (fun x => deriv ψ (f x)) * T.L f + (fun x => deriv (deriv ψ) (f x)) * G T f f := by
    filter_upwards [L_comp T hψ hf] with x hx
    simpa [Pi.mul_apply] using hx
  have j2 : G T (fun x => ψ (f x)) (T.L fun x => ψ (f x)) =ᵐ[T.μ]
      G T (fun x => ψ (f x)) ((fun x => deriv ψ (f x)) * T.L f +
        (fun x => deriv (deriv ψ) (f x)) * G T f f) := G_congr_right hu hLu hsum j1
  have j3 : G T ((fun x => deriv ψ (f x)) * T.L f + (fun x => deriv (deriv ψ) (f x)) * G T f f)
      (fun x => ψ (f x)) =ᵐ[T.μ] fun x => G T ((fun x => deriv ψ (f x)) * T.L f) (fun x => ψ (f x)) x +
        G T ((fun x => deriv (deriv ψ) (f x)) * G T f f) (fun x => ψ (f x)) x := G_add_left haQ hbX hu
  have j4 := G_mul_left ha hQ hu
  have j5 := G_mul_left hb hX hu
  have j6 : G T (fun x => ψ (f x)) (T.L f) =ᵐ[T.μ] fun x => deriv ψ (f x) * G T f (T.L f) x :=
    ΓA_comp_left T hψ hf hQ
  have j7 : G T (fun x => deriv ψ (f x)) (fun x => ψ (f x)) =ᵐ[T.μ]
      fun x => deriv (deriv ψ) (f x) * G T f (fun x => ψ (f x)) x := ΓA_comp_left T hψ1 hf hu
  have j8 : G T (fun x => ψ (f x)) (G T f f) =ᵐ[T.μ] fun x => deriv ψ (f x) * G T f (G T f f) x :=
    ΓA_comp_left T hψ hf hX
  have j9 : G T (fun x => deriv (deriv ψ) (f x)) (fun x => ψ (f x)) =ᵐ[T.μ]
      fun x => deriv (deriv (deriv ψ)) (f x) * G T f (fun x => ψ (f x)) x := ΓA_comp_left T hψ2 hf hu
  have j10 : G T (fun x => ψ (f x)) f =ᵐ[T.μ] fun x => deriv ψ (f x) * G T f f x :=
    ΓA_comp_left T hψ hf hf
  have k1 := G_mul_left ha hQ hu
  have l1 := T.ΓA_nonneg f hf
  filter_upwards [i2, i3, i4, j1, j2, j3, j4, j5, j6, j7, j8, j9, j10] with x
    xi2 xi3 xi4 xj1 xj2 xj3 xj4 xj5 xj6 xj7 xj8 xj9 xj10
  simp only [Pi.mul_apply, Pi.add_apply] at xj1 xj2 xj3 xj4 xj5 xi2
  have c1 := congrFun (G_comm (T := T) (T.L f) (fun x => ψ (f x))) x
  have c2 := congrFun (G_comm (T := T) (T.G f f) (fun x => ψ (f x))) x
  have c4 := congrFun (G_comm (T := T) f (fun x => ψ (f x))) x
  have c5 := congrFun (G_comm (T := T) (T.L f) f) x
  have c6 := congrFun (G_comm (T := T) (T.L fun x => ψ (f x)) (fun x => ψ (f x))) x
  have c7 := congrFun (G_comm (T := T) (fun x => ψ (f x))
    ((fun x => deriv ψ (f x)) * T.L f + (fun x => deriv (deriv ψ) (f x)) * T.G f f)) x
  have hLm := L_mul_eq (T := T) (fun x => B (f x)) (T.G f f) x
  have g1 := Γ₂_eq (T := T) (fun x => ψ (f x)) (fun x => ψ (f x)) x
  have g2 := Γ₂_eq (T := T) f f x
  have b1 := hB1 (f x)
  have b2 := hB2 (f x)
  -- abbreviations
  set a := deriv ψ (f x) with ha_def
  set b := deriv (deriv ψ) (f x) with hb_def
  set c := deriv (deriv (deriv ψ)) (f x) with hc_def
  set X := G T f f x with hXdef
  set Q := T.L f x with hQdef
  have hBx : B (f x) = a ^ 2 := rfl
  have E1 : T.L (G T (fun x => ψ (f x)) (fun x => ψ (f x))) x =
      a ^ 2 * T.L (G T f f) x + X * ((2 * a * b) * Q + (2 * b ^ 2 + 2 * a * c) * X) +
        2 * ((2 * a * b) * G T f (G T f f) x) := by
    rw [xi2, hLm, xi3, xi4, b1, b2, hBx]
  have E2 : G T (fun x => ψ (f x)) (T.L fun x => ψ (f x)) x =
      a * (a * G T f (T.L f) x) + Q * (b * (a * X)) + b * (a * G T f (G T f f) x) + X * (c * (a * X)) := by
    rw [xj2, c7, xj3, xj4, xj5, c1, xj6, xj7, c4, xj10, c2, xj8, xj9, c4, xj10]
    ring
  have E3 : G T (T.L fun x => ψ (f x)) (fun x => ψ (f x)) x =
      G T (fun x => ψ (f x)) (T.L fun x => ψ (f x)) x := c6
  have E4 : G T (T.L f) f x = G T f (T.L f) x := c5
  rw [g1, E3, E1, E2]
  rw [g2, E4]
  ring

end FullTriple

end MarkovTriple.BGL
