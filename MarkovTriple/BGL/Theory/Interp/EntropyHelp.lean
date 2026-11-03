import Mathlib
import MarkovTriple.BGL.Theory.Interp.IbpBdd
import MarkovTriple.BGL.Theory.Strong.Reinforced
import MarkovTriple.BGL.Theory.Extension.Gamma2Ident

/-!
# Helpers for the entropy interpolation: bounded `𝒜`-functions, Green's formula, `Γ` estimates

For a `FullTriple` of finite measure and bounded `f ∈ 𝒜` with `Γ(f) ∈ L¹`:
* `memQ_of_bdd`: `[f] ∈ 𝒟(ℰ)` (BGL Prop. 3.3.6 (ii), ESA);
* `integrable_Γ_cross`: `Γ(f,h) ∈ L¹` (Cauchy-Schwarz `Γ(f,h)² ≤ Γ(f)Γ(h)`);
* `ibp_gen`: `∫ Γ(G,k) = -∫ k L G` for bounded `G, k ∈ 𝒜` with `Γ(G), Γ(k), L G ∈ L¹` (via `ibp_bdd`);
* `Γ_prod_le`: `Γ(fh) ≤ 2f²Γ(h) + 2h²Γ(f)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma memLp_of_bdd [IsFiniteMeasure T.μ] {f : E → ℝ} (hf : f ∈ T.A) {K : ℝ}
    (hK : ∀ᵐ x ∂T.μ, |f x| ≤ K) : MemLp f 2 T.μ :=
  MemLp.of_bound (T.A_measurable f hf).aestronglyMeasurable K
    (hK.mono fun x hx => by rwa [Real.norm_eq_abs])

lemma memQ_of_bdd [IsFiniteMeasure T.μ] {f : E → ℝ} (hf : f ∈ T.A) {K : ℝ}
    (hK : ∀ᵐ x ∂T.μ, |f x| ≤ K) (hΓ : Integrable (G T f f) T.μ) :
    (memLp_of_bdd hf hK).toLp f ∈ T.formDomain :=
  mem_formDomain_of_ESA hf _ hΓ

lemma integrable_Γ_cross {f h : E → ℝ} (hf : f ∈ T.A) (hh : h ∈ T.A)
    (i1 : Integrable (G T f f) T.μ) (i2 : Integrable (G T h h) T.μ) :
    Integrable (G T f h) T.μ := by
  refine (i1.add i2).mono' (T.A_measurable _ (G_mem hf hh)).aestronglyMeasurable ?_
  filter_upwards [ExtendedAlgebra.ΓA_cs T.extendedAlgebra hf hh, T.ΓA_nonneg f hf,
    T.ΓA_nonneg h hh] with x h1 h2 h3
  have h2' : 0 ≤ G T f f x := h2
  have h3' : 0 ≤ G T h h x := h3
  have h1' : G T f h x ^ 2 ≤ G T f f x * G T h h x := h1
  rw [Real.norm_eq_abs]
  show |G T f h x| ≤ G T f f x + G T h h x
  have hsq : G T f h x ^ 2 ≤ (G T f f x + G T h h x) ^ 2 := by
    nlinarith [mul_nonneg h2' h3', sq_nonneg (G T f f x), sq_nonneg (G T h h x)]
  exact abs_le.2 (abs_le_of_sq_le_sq' hsq (by linarith))

/-- **Green's formula** for bounded `G, k ∈ 𝒜`: `∫ Γ(G,k) = -∫ k L G` (`Γ(G), Γ(k), L G ∈ L¹`). -/
theorem ibp_gen [IsFiniteMeasure T.μ] {G' k : E → ℝ} (hG : G' ∈ T.A) {KG : ℝ}
    (hGb : ∀ᵐ x ∂T.μ, |G' x| ≤ KG) (hΓG : Integrable (G T G' G') T.μ)
    (hLG : Integrable (T.L G') T.μ) (hk : k ∈ T.A) {K : ℝ} (hkb : ∀ᵐ x ∂T.μ, |k x| ≤ K)
    (hΓk : Integrable (G T k k) T.μ) :
    ∫ x, G T G' k x ∂T.μ = -∫ x, k x * T.L G' x ∂T.μ :=
  (ibp_bdd hG (memLp_of_bdd hG hGb) (memQ_of_bdd hG hGb hΓG) hLG hk (memLp_of_bdd hk hkb)
    (memQ_of_bdd hk hkb hΓk) hkb).2

/-- `Γ(fh) ≤ 2f²Γ(h) + 2h²Γ(f)` a.e. -/
lemma Γ_prod_le {f h : E → ℝ} (hf : f ∈ T.A) (hh : h ∈ T.A) :
    ∀ᵐ x ∂T.μ, G T (f * h) (f * h) x ≤ 2 * f x ^ 2 * G T h h x + 2 * h x ^ 2 * G T f f x := by
  have hfh : f * h ∈ T.A := T.A.mul_mem hf hh
  filter_upwards [G_mul_left hf hh hfh, G_mul_left hf hh hh, G_mul_left hf hh hf,
    ExtendedAlgebra.ΓA_cs T.extendedAlgebra hf hh, T.ΓA_nonneg f hf, T.ΓA_nonneg h hh]
    with x e1 e2 e3 cs a b
  have c1 : G T h (f * h) x = G T (f * h) h x := congrFun (G_comm (T := T) h (f * h)) x
  have c2 : G T f (f * h) x = G T (f * h) f x := congrFun (G_comm (T := T) f (f * h)) x
  have c3 : G T h f x = G T f h x := congrFun (G_comm (T := T) h f) x
  have a' : 0 ≤ G T f f x := a
  have b' : 0 ≤ G T h h x := b
  have cs' : G T f h x ^ 2 ≤ G T f f x * G T h h x := cs
  have e : G T (f * h) (f * h) x = f x ^ 2 * G T h h x + 2 * f x * h x * G T f h x +
      h x ^ 2 * G T f f x := by
    rw [e1, c1, c2, e2, e3, c3]; ring
  rw [e]
  have key : 2 * f x * h x * G T f h x ≤ f x ^ 2 * G T h h x + h x ^ 2 * G T f f x := by
    have hsq : (2 * f x * h x * G T f h x) ^ 2 ≤ (f x ^ 2 * G T h h x + h x ^ 2 * G T f f x) ^ 2 := by
      have : 0 ≤ (f x * h x) ^ 2 * (G T f f x * G T h h x - G T f h x ^ 2) :=
        mul_nonneg (sq_nonneg _) (by linarith)
      nlinarith [sq_nonneg (f x ^ 2 * G T h h x - h x ^ 2 * G T f f x)]
    have := abs_le_of_sq_le_sq' hsq (by positivity)
    exact this.2
  linarith

end FullTriple

end MarkovTriple.BGL
