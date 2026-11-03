import Mathlib
import MarkovTriple.BGL.Theory.Strong.Reinforced
import MarkovTriple.BGL.Theory.Strong.Product

/-!
# The Hessian `H(f)(g,h)` on `𝒜` (BGL Def. 3.3.13, (3.3.3), (3.3.4), (3.3.7); pp. 158–159)

`Hess T f g h = ½ [Γ(g,Γ(f,h)) + Γ(h,Γ(f,g)) − Γ(f,Γ(g,h))]` with `Γ = ΓA`.

* `Hess_symm`: symmetric in `(g,h)`;
* `Γ₂_mul_Hess`: BGL (3.3.4) `Γ₂(hf,g) = hΓ₂(f,g) + fΓ₂(h,g) + 2H(g)(h,f)` (a.e.);
* `hessian_general_ineq`: BGL (3.3.7) `H(f)(g,h)² ≤ (Γ₂(f) − ρΓ(f)) Γ(g) Γ(h)` a.e. for `f,g,h ∈ 𝒜` under `CD(ρ,n)`
  (the derivation of BGL (C.6.8), p. 517: the quadratic form in `(X₁, Y₂₃)`, obtained by testing the positive form
  `K = Γ₂ − ρΓ` on `f + s (g − a)(h − b)`, discriminant, and then Cauchy–Schwarz `Γ(g,h)² ≤ Γ(g)Γ(h)`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- **The Hessian** (BGL Def. 3.3.13, (3.3.3)): `H(f)(g,h) = ½[Γ(g,Γ(f,h)) + Γ(h,Γ(f,g)) − Γ(f,Γ(g,h))]`.
Total function; meaningful (and `∈ 𝒜`) for `f,g,h ∈ 𝒜`. -/
noncomputable def Hess (T : FullTriple E) (f g h : E → ℝ) : E → ℝ := fun x =>
  (G T g (G T f h) x + G T h (G T f g) x - G T f (G T g h) x) / 2

lemma Hess_symm (f g h : E → ℝ) : Hess T f g h = Hess T f h g := by
  funext x
  simp only [Hess]
  rw [G_comm g h]; ring

/-- BGL (3.3.4): `Γ₂(h k, g) = h Γ₂(k,g) + k Γ₂(h,g) + 2 H(g)(h,k)` a.e. -/
theorem Γ₂_mul_Hess {h k g : E → ℝ} (hh : h ∈ T.A) (hk : k ∈ T.A) (hg : g ∈ T.A) :
    T.toDiffusionTriple.Γ₂ (h * k) g =ᵐ[T.μ] fun x =>
      h x * T.toDiffusionTriple.Γ₂ k g x + k x * T.toDiffusionTriple.Γ₂ h g x +
        2 * Hess T g h k x := by
  filter_upwards [Γ₂_mul_left hh hk hg] with x h1
  rw [h1]
  simp only [Hess]
  rw [G_comm g k, G_comm g h]
  ring

section ineq

variable {ρ : ℝ} {n : ℝ≥0∞}

lemma shift1_K (ρ : ℝ) {g k : E → ℝ} (hg : g ∈ T.A) (hk : k ∈ T.A) (a : ℝ) :
    Kf T ρ (fun x => g x - a) k =ᵐ[T.μ] Kf T ρ g k := by
  filter_upwards [shift_Γ₂ hg a hk, shift_G hg a hk] with x h1 h2
  simp only [Kf]; rw [h1, h2]

/-- the polynomial inequality for fixed shifts `a, b`. -/
lemma poly3 (hCD : T.CD ρ n) {f g h : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (hh : h ∈ T.A)
    (a b : ℝ) : ∀ᵐ x ∂T.μ,
    ((g x - a) * Kf T ρ h f x + (h x - b) * Kf T ρ g f x + G T g (G T h f) x + G T h (G T g f) x -
        G T f (G T g h) x) ^ 2 ≤
      Kf T ρ f f x * ((g x - a) ^ 2 * Kf T ρ h h x + (h x - b) ^ 2 * Kf T ρ g g x +
        2 * (g x - a) * (h x - b) * Kf T ρ g h x + 2 * (g x - a) * G T g (G T h h) x +
        2 * (h x - b) * G T h (G T g g) x + 2 * G T g g x * G T h h x + 2 * G T g h x ^ 2) := by
  have hu := shift_memA (T := T) hg a
  have hv := shift_memA (T := T) hh b
  have huv : (fun x => g x - a) * (fun x => h x - b) ∈ T.A := T.A.mul_mem hu hv
  have cs := cs_of_psd (T := T) (Kf T ρ) (Kf_comm ρ) (fun hf hg hk s => Kf_lin_left ρ hf hg hk s)
    (Kf_nonneg hCD) hf huv
  have e1 := Kf_mul_left ρ hu hv hf
  have e2 := K2 ρ hu hv
  have s1 := shift1_K ρ hh hf b
  have s2 := shift1_K ρ hg hf a
  have s3 : G T (fun x => g x - a) (G T (fun x => h x - b) f) =ᵐ[T.μ] G T g (G T h f) :=
    (shift_G hg a (G_mem hv hf)).trans
      (G_congr_right hg (G_mem hv hf) (G_mem hh hf) (shift_G hh b hf))
  have s4 : G T (fun x => h x - b) (G T (fun x => g x - a) f) =ᵐ[T.μ] G T h (G T g f) :=
    (shift_G hh b (G_mem hu hf)).trans
      (G_congr_right hh (G_mem hu hf) (G_mem hg hf) (shift_G hg a hf))
  have s5 : G T f (G T (fun x => g x - a) (fun x => h x - b)) =ᵐ[T.μ] G T f (G T g h) :=
    G_congr_right hf (G_mem hu hv) (G_mem hg hh) (shift2_G hg hh a b)
  have t_uu : Kf T ρ (fun x => g x - a) (fun x => g x - a) =ᵐ[T.μ] Kf T ρ g g := shift2_K hg hg a a ρ
  have t_vv : Kf T ρ (fun x => h x - b) (fun x => h x - b) =ᵐ[T.μ] Kf T ρ h h := shift2_K hh hh b b ρ
  have t_uv : Kf T ρ (fun x => g x - a) (fun x => h x - b) =ᵐ[T.μ] Kf T ρ g h := shift2_K hg hh a b ρ
  have g_uu : G T (fun x => g x - a) (fun x => g x - a) =ᵐ[T.μ] G T g g := shift2_G hg hg a a
  have g_vv : G T (fun x => h x - b) (fun x => h x - b) =ᵐ[T.μ] G T h h := shift2_G hh hh b b
  have g_uv : G T (fun x => g x - a) (fun x => h x - b) =ᵐ[T.μ] G T g h := shift2_G hg hh a b
  have gg1 : G T (fun x => g x - a) (G T (fun x => h x - b) (fun x => h x - b)) =ᵐ[T.μ]
      G T g (G T h h) := shift2_G_G hg hh a b
  have gg2 : G T (fun x => h x - b) (G T (fun x => g x - a) (fun x => g x - a)) =ᵐ[T.μ]
      G T h (G T g g) := shift2_G_G hh hg b a
  filter_upwards [cs, e1, e2, s1, s2, s3, s4, s5, t_uu, t_vv, t_uv, g_uu, g_vv, g_uv, gg1, gg2]
    with x c h1 h2 a1 a2 a3 a4 a5 b1 b2 b3 d1 d2 d3 d4 d5
  rw [Kf_comm ρ f _, h1, h2] at c
  rw [a1, a2, a3, a4, a5, b1, b2, b3, d1, d2, d3, d4, d5] at c
  exact c

/-- **BGL (3.3.7)** (derived as in (C.6.8)): under `CD(ρ,n)`, for `f,g,h ∈ 𝒜`,
`H(f)(g,h)² ≤ (Γ₂(f) − ρΓ(f)) Γ(g) Γ(h)` a.e. -/
theorem hessian_general_ineq (hCD : T.CD ρ n) {f g h : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A)
    (hh : h ∈ T.A) : ∀ᵐ x ∂T.μ,
    Hess T f g h x ^ 2 ≤ Kf T ρ f f x * (G T g g x * G T h h x) := by
  have per := fun p : ℚ × ℚ => poly3 hCD hf hg hh (p.1 : ℝ) (p.2 : ℝ)
  have hall := ae_all_iff.2 per
  have hcs := ExtendedAlgebra.ΓA_cs T.extendedAlgebra hg hh
  have hK := Kf_nonneg hCD f hf
  have hdense : DenseRange (fun p : ℚ × ℚ => ((p.1 : ℝ), (p.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  filter_upwards [hall, hcs, hK] with x hx hcs' hK'
  have key : ∀ z : ℝ × ℝ,
      ((g x - z.1) * Kf T ρ h f x + (h x - z.2) * Kf T ρ g f x + G T g (G T h f) x +
        G T h (G T g f) x - G T f (G T g h) x) ^ 2 ≤
      Kf T ρ f f x * ((g x - z.1) ^ 2 * Kf T ρ h h x + (h x - z.2) ^ 2 * Kf T ρ g g x +
        2 * (g x - z.1) * (h x - z.2) * Kf T ρ g h x + 2 * (g x - z.1) * G T g (G T h h) x +
        2 * (h x - z.2) * G T h (G T g g) x + 2 * G T g g x * G T h h x + 2 * G T g h x ^ 2) := by
    intro z
    refine hdense.induction_on z (isClosed_le (by fun_prop) (by fun_prop)) (fun p => hx p)
  have := key (g x, h x)
  simp only [sub_self, zero_pow two_ne_zero, mul_zero, zero_mul, add_zero, zero_add] at this
  have e1 : G T h f = G T f h := G_comm h f
  have e2 : G T h (G T g f) x = G T h (G T f g) x := by rw [G_comm g f]
  rw [e1] at this
  rw [e2] at this
  have hH : Hess T f g h x = (G T g (G T f h) x + G T h (G T f g) x - G T f (G T g h) x) / 2 := rfl
  rw [hH]
  have hgg := T.ΓA_nonneg g hg
  nlinarith [mul_nonneg hK' (sub_nonneg.2 hcs'), this]

end ineq

end FullTriple

end MarkovTriple.BGL
