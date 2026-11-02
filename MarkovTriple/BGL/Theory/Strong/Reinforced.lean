import Mathlib
import MarkovTriple.BGL.Theory.Strong.Product
import MarkovTriple.BGL.Theory.Conservation.ExtAlgebra

/-!
# Reinforced curvature inequality (BGL (3.3.6)) from `CD(ρ, n)`

See `Hessian.lean` for the strategy.  Main results:

* `hessian_ineq`: `Γ(w, Γ f)² ≤ 2 K(f) (Γ(f)Γ(w) + Γ(f,w)²)` a.e., `f, w ∈ 𝒜`, `K = Γ₂ − ρΓ`;
* `reinforced_cd`: `Γ(Γ f, Γ f) ≤ 4 (Γ₂(f) − ρΓ(f)) Γ(f)` a.e. for every `f ∈ 𝒜` (BGL (3.3.6)).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma Kf_mul_left (ρ : ℝ) {u v g : E → ℝ} (hu : u ∈ T.A) (hv : v ∈ T.A) (hg : g ∈ T.A) :
    Kf T ρ (u * v) g =ᵐ[T.μ] fun x => u x * Kf T ρ v g x + v x * Kf T ρ u g x +
      G T u (G T v g) x + G T v (G T u g) x - G T g (G T u v) x := by
  filter_upwards [Γ₂_mul_left hu hv hg, G_mul_left hu hv hg] with x h1 h2
  simp only [Kf]; rw [h1, h2]; ring

lemma K1 (ρ : ℝ) {u v : E → ℝ} (hu : u ∈ T.A) (hv : v ∈ T.A) :
    Kf T ρ u (u * v) =ᵐ[T.μ] fun x => u x * Kf T ρ u v x + v x * Kf T ρ u u x +
      G T v (G T u u) x := by
  rw [Kf_comm]
  filter_upwards [Kf_mul_left ρ hu hv hu] with x h
  rw [h]
  have e1 : G T u (G T v u) x = G T u (G T u v) x := by rw [G_comm v u]
  have e2 : Kf T ρ v u x = Kf T ρ u v x := by rw [Kf_comm]
  rw [e2]
  have : G T u (G T v u) x = G T u (G T u v) x := e1
  linarith

lemma K2 (ρ : ℝ) {u v : E → ℝ} (hu : u ∈ T.A) (hv : v ∈ T.A) :
    Kf T ρ (u * v) (u * v) =ᵐ[T.μ] fun x =>
      u x ^ 2 * Kf T ρ v v x + v x ^ 2 * Kf T ρ u u x + 2 * u x * v x * Kf T ρ u v x +
        2 * u x * G T u (G T v v) x + 2 * v x * G T v (G T u u) x +
        2 * G T u u x * G T v v x + 2 * G T u v x ^ 2 := by
  have huv : u * v ∈ T.A := T.A.mul_mem hu hv
  filter_upwards [Γ₂_mul_self hu hv, G_mul_right hu hv huv, G_mul_left hu hv hu,
    G_mul_left hu hv hv] with x h1 h2 h3 h4
  simp only [Kf]
  rw [h1, h2, h3, h4, G_comm v u]
  ring

/-! ### Shift invariance of the atoms -/

section shift2

variable {f w : E → ℝ} (hf : f ∈ T.A) (hw : w ∈ T.A) (a b : ℝ)

include hf hw in
lemma shift2_G : G T (fun x => f x - a) (fun x => w x - b) =ᵐ[T.μ] G T f w := by
  have hu := shift_memA (T := T) hf a
  have hv := shift_memA (T := T) hw b
  have s1 := shift_G hf a hv
  have s2 : G T (fun x => w x - b) f =ᵐ[T.μ] G T w f := shift_G hw b hf
  filter_upwards [s1, s2] with x h1 h2
  rw [h1, G_comm f, h2, G_comm]

include hf hw in
lemma shift2_Γ₂ : T.toDiffusionTriple.Γ₂ (fun x => f x - a) (fun x => w x - b) =ᵐ[T.μ]
    T.toDiffusionTriple.Γ₂ f w := by
  have hv := shift_memA (T := T) hw b
  have s1 := shift_Γ₂ hf a hv
  have s2 : T.toDiffusionTriple.Γ₂ (fun x => w x - b) f =ᵐ[T.μ] T.toDiffusionTriple.Γ₂ w f :=
    shift_Γ₂ hw b hf
  filter_upwards [s1, s2] with x h1 h2
  rw [h1, Γ₂_comm f, h2, Γ₂_comm]

include hf hw in
lemma shift2_K (ρ : ℝ) : Kf T ρ (fun x => f x - a) (fun x => w x - b) =ᵐ[T.μ] Kf T ρ f w := by
  filter_upwards [shift2_Γ₂ hf hw a b, shift2_G hf hw a b] with x h1 h2
  simp only [Kf]; rw [h1, h2]

include hf hw in
lemma shift2_G_G : G T (fun x => f x - a) (G T (fun x => w x - b) (fun x => w x - b)) =ᵐ[T.μ]
    G T f (G T w w) := by
  have hv := shift_memA (T := T) hw b
  have Gv := G_mem (T := T) hv hv
  have Gw := G_mem (T := T) hw hw
  have s1 := shift_G hf a Gv
  have s2 := G_congr_right hf Gv Gw (shift2_G hw hw b b)
  filter_upwards [s1, s2] with x h1 h2
  rw [h1, h2]

end shift2

/-- **Test of the positive form `K` on `f` and `(f−a)(w−b)`**, rational `a,b`: the polynomial inequality. -/
lemma poly_ineq (ρ : ℝ) (hρ : ∀ g ∈ T.A, 0 ≤ᵐ[T.μ] Kf T ρ g g) {f w : E → ℝ} (hf : f ∈ T.A)
    (hw : w ∈ T.A) (a b : ℝ) : ∀ᵐ x ∂T.μ,
    0 ≤ Kf T ρ f f x * (( f x - a) ^ 2 * Kf T ρ w w x + (w x - b) ^ 2 * Kf T ρ f f x +
        2 * (f x - a) * (w x - b) * Kf T ρ f w x + 2 * (f x - a) * G T f (G T w w) x +
        2 * (w x - b) * G T w (G T f f) x + 2 * G T f f x * G T w w x + 2 * G T f w x ^ 2) -
      ((f x - a) * Kf T ρ f w x + (w x - b) * Kf T ρ f f x + G T w (G T f f) x) ^ 2 := by
  have hu := shift_memA (T := T) hf a
  have hv := shift_memA (T := T) hw b
  have huv : (fun x => f x - a) * (fun x => w x - b) ∈ T.A := T.A.mul_mem hu hv
  have cs := cs_of_psd (T := T) (Kf T ρ) (Kf_comm ρ) (fun hf hg hk s => Kf_lin_left ρ hf hg hk s) hρ hu huv
  have e1 := K1 ρ hu hv
  have e2 := K2 ρ hu hv
  have s_uu : Kf T ρ (fun x => f x - a) (fun x => f x - a) =ᵐ[T.μ] Kf T ρ f f := shift2_K hf hf a a ρ
  have s_vv : Kf T ρ (fun x => w x - b) (fun x => w x - b) =ᵐ[T.μ] Kf T ρ w w := shift2_K hw hw b b ρ
  have s_uv : Kf T ρ (fun x => f x - a) (fun x => w x - b) =ᵐ[T.μ] Kf T ρ f w := shift2_K hf hw a b ρ
  have g_uu : G T (fun x => f x - a) (fun x => f x - a) =ᵐ[T.μ] G T f f := shift2_G hf hf a a
  have g_vv : G T (fun x => w x - b) (fun x => w x - b) =ᵐ[T.μ] G T w w := shift2_G hw hw b b
  have g_uv : G T (fun x => f x - a) (fun x => w x - b) =ᵐ[T.μ] G T f w := shift2_G hf hw a b
  have gg1 : G T (fun x => f x - a) (G T (fun x => w x - b) (fun x => w x - b)) =ᵐ[T.μ]
      G T f (G T w w) := shift2_G_G hf hw a b
  have gg2 : G T (fun x => w x - b) (G T (fun x => f x - a) (fun x => f x - a)) =ᵐ[T.μ]
      G T w (G T f f) := shift2_G_G hw hf b a
  filter_upwards [cs, e1, e2, s_uu, s_vv, s_uv, g_uu, g_vv, g_uv, gg1, gg2] with x c h1 h2 a1 a2 a3 b1 b2 b3 d1 d2
  rw [h1, h2, a1, a2, a3, b1, b2, b3, d1, d2] at c
  have hq : Kf T ρ (fun x => f x - a) (fun x => f x - a) x = Kf T ρ f f x := a1
  nlinarith [c]

/-- under `CD(ρ,n)`, `K(g) ≥ 0` on `𝒜`. -/
lemma Kf_nonneg {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) : ∀ g ∈ T.A, 0 ≤ᵐ[T.μ] Kf T ρ g g := by
  intro g hg
  filter_upwards [hCD.2 g hg] with x hx
  have : 0 ≤ (n⁻¹).toReal * (T.L g x) ^ 2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  simp only [Kf]; show 0 ≤ T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x
  have : ρ * G T g g x ≤ T.toDiffusionTriple.Γ₂ g g x := by linarith
  linarith

/-- **Hessian-type inequality**: `Γ(w, Γf)² ≤ 2 K(f) (Γ(f)Γ(w) + Γ(f,w)²)` a.e. -/
theorem hessian_ineq {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f w : E → ℝ} (hf : f ∈ T.A)
    (hw : w ∈ T.A) : ∀ᵐ x ∂T.μ,
    G T w (G T f f) x ^ 2 ≤ 2 * Kf T ρ f f x * (G T f f x * G T w w x + G T f w x ^ 2) := by
  have hK := Kf_nonneg hCD
  have per : ∀ p : ℚ × ℚ, ∀ᵐ x ∂T.μ, 0 ≤ Kf T ρ f f x * (( f x - (p.1 : ℝ)) ^ 2 * Kf T ρ w w x +
        (w x - (p.2 : ℝ)) ^ 2 * Kf T ρ f f x +
        2 * (f x - (p.1 : ℝ)) * (w x - (p.2 : ℝ)) * Kf T ρ f w x +
        2 * (f x - (p.1 : ℝ)) * G T f (G T w w) x +
        2 * (w x - (p.2 : ℝ)) * G T w (G T f f) x + 2 * G T f f x * G T w w x +
        2 * G T f w x ^ 2) -
      ((f x - (p.1 : ℝ)) * Kf T ρ f w x + (w x - (p.2 : ℝ)) * Kf T ρ f f x +
        G T w (G T f f) x) ^ 2 := fun p => poly_ineq ρ hK hf hw p.1 p.2
  have hall := ae_all_iff.2 per
  filter_upwards [hall] with x hx
  have hdense : DenseRange (fun p : ℚ × ℚ => ((p.1 : ℝ), (p.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have key : ∀ z : ℝ × ℝ, 0 ≤ Kf T ρ f f x * (( f x - z.1) ^ 2 * Kf T ρ w w x +
        (w x - z.2) ^ 2 * Kf T ρ f f x + 2 * (f x - z.1) * (w x - z.2) * Kf T ρ f w x +
        2 * (f x - z.1) * G T f (G T w w) x + 2 * (w x - z.2) * G T w (G T f f) x +
        2 * G T f f x * G T w w x + 2 * G T f w x ^ 2) -
      ((f x - z.1) * Kf T ρ f w x + (w x - z.2) * Kf T ρ f f x + G T w (G T f f) x) ^ 2 := by
    intro z
    refine hdense.induction_on z (isClosed_le continuous_const (by fun_prop)) (fun p => hx p)
  have := key (f x, w x)
  simp only [sub_self, zero_pow two_ne_zero, mul_zero, zero_mul, add_zero, zero_add] at this
  nlinarith [this]

/-- **BGL (3.3.6)**: under `CD(ρ,n)`, `Γ(Γ f, Γ f) ≤ 4 (Γ₂(f) − ρΓ(f)) Γ(f)` a.e. on `𝒜`. -/
theorem reinforced_cd {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A) :
    ∀ᵐ x ∂T.μ, G T (G T f f) (G T f f) x ≤
      4 * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) * G T f f x := by
  have hΓ := G_mem (T := T) hf hf
  have h := hessian_ineq hCD hf hΓ
  have hnn := T.ΓA_nonneg _ hΓ
  have hf0 := T.ΓA_nonneg f hf
  have hK := Kf_nonneg hCD f hf
  have hcs := ExtendedAlgebra.ΓA_cs T.extendedAlgebra hf hΓ
  filter_upwards [h, hnn, hf0, hK, hcs] with x h1 h2 h3 h4 h5
  simp only [Kf] at h1 h4
  set Y := G T (G T f f) (G T f f) x with hY
  have hc : G T (G T f f) f x = G T f (G T f f) x := by rw [G_comm]
  -- h1: Γ(Γf, Γf)^2 ≤ 2 K (Γf Γ(Γf) + Γ(f,Γf)^2) and Γ(f,Γf)^2 ≤ Γf Γ(Γf)
  have hY' : G T (G T f f) (G T f f) x = Y := rfl
  have h1' : Y ^ 2 ≤ 2 * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) *
      (G T f f x * Y + G T f (G T f f) x ^ 2) := h1
  have h5' : G T f (G T f f) x ^ 2 ≤ G T f f x * Y := h5
  have hKn : 0 ≤ T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x := h4
  have h6 : Y ^ 2 ≤ 4 * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) * (G T f f x * Y) := by
    nlinarith [mul_le_mul_of_nonneg_left h5' hKn]
  by_cases hY0 : Y = 0
  · rw [hY0]
    have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hKn) h3
    simpa using this
  · have hYpos : 0 < Y := lt_of_le_of_ne h2 (Ne.symm hY0)
    have : Y * Y ≤ (4 * (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) * G T f f x) * Y := by
      nlinarith [h6]
    exact le_of_mul_le_mul_right this hYpos

end FullTriple

end MarkovTriple.BGL
