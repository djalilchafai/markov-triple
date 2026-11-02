import Mathlib
import MarkovTriple.BGL.Theory.Strong.Calculus

/-!
# The reinforced curvature inequality (BGL (3.3.6)) from `CD(ρ,n)`

Under `CD(ρ, n)` on `𝒜` (any `n ≥ 1`), `K(f) := Γ₂(f) − ρΓ(f) ≥ 0` on `𝒜`.  We show that the symmetric bilinear
form `K(f,g) = Γ₂(f,g) − ρΓ(f,g)` is pointwise positive semidefinite (Cauchy–Schwarz), and test it on
`f` and `q = (f − a)(w − b)` (`a, b ∈ ℚ`), using the Hessian product rule `Γ₂_mul_left`.  Letting `a → f(x)`,
`b → w(x)` pointwise (polynomial dependence) yields, for `f, w ∈ 𝒜`,

`Γ(w, Γ f)² ≤ 2 K(f) (Γ(f)Γ(w) + Γ(f,w)²)`  a.e.,

and for `w = Γ f`: `Γ(Γ f) ≤ 4 (Γ₂(f) − ρΓ(f)) Γ(f)` (BGL (3.3.6), the pointwise inequality used in
Lemmas 3.3.20–3.3.21).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- `G(p,k)` only depends on the a.e.-class of `p ∈ 𝒜`. -/
lemma G_congr_left {p p' k : E → ℝ} (hp : p ∈ T.A) (hp' : p' ∈ T.A) (hk : k ∈ T.A)
    (h : p =ᵐ[T.μ] p') : G T p k =ᵐ[T.μ] G T p' k := by
  have h1 : T.L (p * k) =ᵐ[T.μ] T.L (p' * k) :=
    L_congr_A T (T.A.mul_mem hp hk) (T.A.mul_mem hp' hk)
      (by filter_upwards [h] with x hx; simp [hx])
  have h2 := L_congr_A T hp hp' h
  filter_upwards [h, h1, h2] with x hx hx1 hx2
  show (T.L (p * k) x - p x * T.L k x - k x * T.L p x) / 2 =
    (T.L (p' * k) x - p' x * T.L k x - k x * T.L p' x) / 2
  rw [hx1, hx2, hx]

lemma G_congr_right {p k k' : E → ℝ} (hp : p ∈ T.A) (hk : k ∈ T.A) (hk' : k' ∈ T.A)
    (h : k =ᵐ[T.μ] k') : G T p k =ᵐ[T.μ] G T p k' := by
  rw [G_comm p k, G_comm p k']
  exact G_congr_left hk hk' hp h

lemma Γ₂_comm (f g : E → ℝ) : T.toDiffusionTriple.Γ₂ f g = T.toDiffusionTriple.Γ₂ g f := by
  funext x
  rw [Γ₂_eq, Γ₂_eq, G_comm f g, G_comm f (T.L g), G_comm (T.L f) g]
  ring

/-- `Γ₂(f + s g, k) = Γ₂(f,k) + s Γ₂(g,k)` a.e. -/
theorem Γ₂_lin_left {f g k : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (hk : k ∈ T.A) (s : ℝ) :
    T.toDiffusionTriple.Γ₂ (fun x => f x + s * g x) k =ᵐ[T.μ] fun x =>
      T.toDiffusionTriple.Γ₂ f k x + s * T.toDiffusionTriple.Γ₂ g k x := by
  have hF : (fun x => f x + s * g x) ∈ T.A := by
    have : (fun x => f x + s * g x) = f + s • g := by funext x; simp
    rw [this]; exact T.A.add_mem hf (T.A.smul_mem hg s)
  have hLk := L_memA (T := T) hk
  have hGf := G_mem (T := T) hf hk
  have hGg := G_mem (T := T) hg hk
  have hM : (fun x => G T f k x + s * G T g k x) ∈ T.A := by
    have : (fun x => G T f k x + s * G T g k x) = G T f k + s • G T g k := by funext x; simp
    rw [this]; exact T.A.add_mem hGf (T.A.smul_mem hGg s)
  have i1 : G T (fun x => f x + s * g x) k =ᵐ[T.μ] fun x => G T f k x + s * G T g k x :=
    G_lin_left hf hg s hk
  have i2 : T.L (G T (fun x => f x + s * g x) k) =ᵐ[T.μ]
      T.L (fun x => G T f k x + s * G T g k x) :=
    L_congr_A T (G_mem hF hk) hM i1
  have i3 : T.L (fun x => G T f k x + s * G T g k x) =ᵐ[T.μ]
      fun x => T.L (G T f k) x + s * T.L (G T g k) x := L_lin hGf hGg s
  have j1 : G T (fun x => f x + s * g x) (T.L k) =ᵐ[T.μ]
      fun x => G T f (T.L k) x + s * G T g (T.L k) x := G_lin_left hf hg s hLk
  have hLF := L_memA (T := T) hF
  have hN : (fun x => T.L f x + s * T.L g x) ∈ T.A := by
    have : (fun x => T.L f x + s * T.L g x) = T.L f + s • T.L g := by funext x; simp
    rw [this]; exact T.A.add_mem (L_memA hf) (T.A.smul_mem (L_memA hg) s)
  have k1 : T.L (fun x => f x + s * g x) =ᵐ[T.μ] fun x => T.L f x + T.L g x * s := by
    filter_upwards [L_lin hf hg s] with x hx
    rw [hx]; ring
  have k1' : T.L (fun x => f x + s * g x) =ᵐ[T.μ] fun x => T.L f x + s * T.L g x := by
    filter_upwards [L_lin hf hg s] with x hx; exact hx
  have k2 : G T (T.L (fun x => f x + s * g x)) k =ᵐ[T.μ]
      G T (fun x => T.L f x + s * T.L g x) k := G_congr_left hLF hN hk k1'
  have k3 : G T (fun x => T.L f x + s * T.L g x) k =ᵐ[T.μ]
      fun x => G T (T.L f) k x + s * G T (T.L g) k x :=
    G_lin_left (L_memA hf) (L_memA hg) s hk
  filter_upwards [i2, i3, j1, k2, k3] with x e2 e3 e4 e5 e6
  rw [Γ₂_eq, Γ₂_eq, Γ₂_eq, e2, e3, e4, e5, e6]
  ring

/-- `K(f,g) = Γ₂(f,g) − ρ Γ(f,g)`. -/
noncomputable def Kf (T : FullTriple E) (ρ : ℝ) (f g : E → ℝ) : E → ℝ :=
  fun x => T.toDiffusionTriple.Γ₂ f g x - ρ * G T f g x

lemma Kf_comm (ρ : ℝ) (f g : E → ℝ) : Kf T ρ f g = Kf T ρ g f := by
  funext x; simp only [Kf]; rw [Γ₂_comm f g, G_comm f g]

lemma Kf_lin_left (ρ : ℝ) {f g k : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (hk : k ∈ T.A) (s : ℝ) :
    Kf T ρ (fun x => f x + s * g x) k =ᵐ[T.μ] fun x => Kf T ρ f k x + s * Kf T ρ g k x := by
  filter_upwards [Γ₂_lin_left hf hg hk s, G_lin_left hf hg s hk] with x h1 h2
  simp only [Kf]; rw [h1, h2]; ring

/-- Cauchy–Schwarz for a pointwise positive semidefinite symmetric bilinear form on `𝒜`. -/
theorem cs_of_psd (B : (E → ℝ) → (E → ℝ) → E → ℝ)
    (hsymm : ∀ f g, B f g = B g f)
    (hlin : ∀ {f g k : E → ℝ}, f ∈ T.A → g ∈ T.A → k ∈ T.A → ∀ s : ℝ,
      B (fun x => f x + s * g x) k =ᵐ[T.μ] fun x => B f k x + s * B g k x)
    (hnn : ∀ f ∈ T.A, 0 ≤ᵐ[T.μ] B f f) {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) :
    ∀ᵐ x ∂T.μ, B f g x ^ 2 ≤ B f f x * B g g x := by
  have key : ∀ s : ℝ, ∀ᵐ x ∂T.μ, 0 ≤ B f f x + 2 * s * B f g x + s ^ 2 * B g g x := by
    intro s
    have hs : (fun x => f x + s * g x) ∈ T.A := by
      have : (fun x => f x + s * g x) = f + s • g := by funext x; simp
      rw [this]; exact T.A.add_mem hf (T.A.smul_mem hg s)
    have e1 := hlin hf hg hs s
    have e2 := hlin hf hg hf s
    have e3 := hlin hf hg hg s
    have hn := hnn _ hs
    filter_upwards [e1, e2, e3, hn] with x h1 h2 h3 h4
    have c1 : B f (fun x => f x + s * g x) x = B (fun x => f x + s * g x) f x :=
      congrFun (hsymm f _) x
    have c2 : B g (fun x => f x + s * g x) x = B (fun x => f x + s * g x) g x :=
      congrFun (hsymm g _) x
    have c3 : B g f x = B f g x := congrFun (hsymm g f) x
    have step : B (fun x => f x + s * g x) (fun x => f x + s * g x) x =
        B f f x + 2 * s * B f g x + s ^ 2 * B g g x := by
      have e1' : B (fun x => f x + s * g x) (fun x => f x + s * g x) x =
          B f (fun x => f x + s * g x) x + s * B g (fun x => f x + s * g x) x := h1
      rw [e1', c1, c2, h2, h3]
      rw [c3]; ring
    rw [← step]; exact h4
  have keyq := ae_all_iff.2 (fun q : ℚ => key (q : ℝ))
  filter_upwards [keyq] with x hx
  have hall : ∀ s : ℝ, 0 ≤ B g g x * (s * s) + (2 * B f g x) * s + B f f x := by
    intro s
    have : 0 ≤ B f f x + 2 * s * B f g x + s ^ 2 * B g g x := by
      refine Rat.denseRange_cast.induction_on s
        (isClosed_le continuous_const (by fun_prop)) (fun q => hx q)
    nlinarith [this]
  have hd := discrim_le_zero hall
  unfold discrim at hd
  nlinarith [hd]

end FullTriple

end MarkovTriple.BGL
