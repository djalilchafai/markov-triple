import Mathlib
import MarkovTriple.BGL.Consistency

/-!
# Fundamental identity (3.1.1) and chain rule for `L` (3.1.8) for a bare `DiffusionTriple`

(Not frozen.)  Both are *consequences* of the fields (the book says so), proved here:

* `fundamental_identity_ae`, `fundamental_identity`: `Γ(f², g) + 2 g Γ(f) = 2 Γ(f g, f)` (a.e.,
  hence also after integration), from the diffusion property (Leibniz rule) and symmetry.
* `chain_rule_L`: for smooth `ψ : ℝᵏ → ℝ` with `ψ(0) = 0` and `f₁,…,f_k ∈ 𝒜₀`,
  `L ψ(f) = Σᵢ ∂ᵢψ(f) L fᵢ + Σᵢⱼ ∂²ᵢⱼψ(f) Γ(fᵢ, fⱼ)` a.e.  Proof: both sides are in `𝒜₀` (use
  `ψᵢ − ψᵢ(0)` and `comp_mem`), and they have the same integral against every `g ∈ 𝒜₀` (integration by
  parts, the diffusion property for `ψ`, and the Leibniz rule applied to `(ψᵢ − ψᵢ(0))(f) · g`), so
  they coincide a.e. by density (`ae_zero_of_orth`).
-/

open MeasureTheory

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

/-! ### Fundamental identity -/

/-- **BGL (3.1.1)**, pointwise a.e. form: `Γ(f²,g) + 2 g Γ(f) = 2 Γ(fg, f)`. -/
theorem fundamental_identity_ae {f g : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀) :
    T.Γ (f * f) g + (2 : ℝ) • (g * T.Γ f f) =ᵐ[T.μ] (2 : ℝ) • T.Γ (f * g) f := by
  filter_upwards [Γ_mul_left T hf hf hg, Γ_mul_left T hf hg hf, T.Γ_symm g hg f hf] with x h1 h2 h3
  simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 h3 ⊢
  rw [h1, h2, h3]; ring

/-- **BGL (3.1.1)** (integrated form, as in Definition 3.1.1): for `f, g ∈ 𝒜₀`,
`∫ Γ(f², g) dμ + 2 ∫ g Γ(f) dμ = 2 ∫ Γ(f g, f) dμ`. -/
theorem fundamental_identity {f g : E → ℝ} (hf : f ∈ T.A₀) (hg : g ∈ T.A₀) :
    ∫ x, T.Γ (f * f) g x ∂T.μ + 2 * ∫ x, g x * T.Γ f f x ∂T.μ =
      2 * ∫ x, T.Γ (f * g) f x ∂T.μ := by
  have i1 := integrable_of_mem T (T.Γ_mem _ (T.A₀.mul_mem hf hf) _ hg)
  have i2 := integrable_of_mem T (T.A₀.mul_mem hg (T.Γ_mem _ hf _ hf))
  have i3 := integrable_of_mem T (T.Γ_mem _ (T.A₀.mul_mem hf hg) _ hf)
  have h := integral_congr_ae (fundamental_identity_ae T hf hg)
  have e1 : ∫ x, (T.Γ (f * f) g + (2 : ℝ) • (g * T.Γ f f)) x ∂T.μ =
      ∫ x, T.Γ (f * f) g x ∂T.μ + 2 * ∫ x, g x * T.Γ f f x ∂T.μ := by
    simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
    rw [integral_add (f := fun x => T.Γ (f * f) g x) (g := fun x => 2 * (g x * T.Γ f f x)) i1
      (i2.const_mul 2), integral_const_mul]
  have e2 : ∫ x, ((2 : ℝ) • T.Γ (f * g) f) x ∂T.μ = 2 * ∫ x, T.Γ (f * g) f x ∂T.μ := by
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [integral_const_mul]
  rw [← e1, ← e2]; exact h

/-! ### Chain rule for `L` -/

lemma contDiff_pderiv {k : ℕ} {ψ : (Fin k → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin k) :
    ContDiff ℝ (⊤ : ℕ∞) (pderiv ψ i) := by
  unfold pderiv
  exact (hψ.fderiv_right (by simp)).clm_apply contDiff_const

/-- Composition with `χ ∘ f` (χ smooth, no vanishing condition) times a test function stays in `𝒜₀`. -/
lemma comp_mul_mem {k : ℕ} (χ : (Fin k → ℝ) → ℝ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (f : Fin k → E → ℝ) (hf : ∀ i, f i ∈ T.A₀) {a : E → ℝ} (ha : a ∈ T.A₀) :
    (fun x => χ (fun i => f i x) * a x) ∈ T.A₀ := by
  have h1 := T.comp_mem k (fun z => χ z - χ 0) (hχ.sub contDiff_const) (by simp) f hf
  have : (fun x => χ (fun i => f i x) * a x) =
      (fun x => χ (fun i => f i x) - χ 0) * a + (χ 0) • a := by
    funext x; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]; ring
  rw [this]
  exact T.A₀.add_mem (T.A₀.mul_mem h1 ha) (T.A₀.smul_mem _ ha)

lemma sum_fn_mem {ι : Type*} (s : Finset ι) (G : ι → E → ℝ) (hG : ∀ i ∈ s, G i ∈ T.A₀) :
    (fun x => ∑ i ∈ s, G i x) ∈ T.A₀ := by
  have : (fun x => ∑ i ∈ s, G i x) = ∑ i ∈ s, G i := by
    funext x; simp [Finset.sum_apply]
  rw [this]
  exact sum_mem hG

lemma integral_mul_sum {ι : Type*} (s : Finset ι) (G : ι → E → ℝ) (hG : ∀ i ∈ s, G i ∈ T.A₀)
    {g : E → ℝ} (hg : g ∈ T.A₀) :
    ∫ x, g x * ∑ i ∈ s, G i x ∂T.μ = ∑ i ∈ s, ∫ x, g x * G i x ∂T.μ := by
  simp only [Finset.mul_sum]
  exact integral_finsetSum _ (fun i hi => integrable_of_mem T (T.A₀.mul_mem hg (hG i hi)))

lemma term_ibp {fi φ g : E → ℝ} (hfi : fi ∈ T.A₀) (hφ : φ ∈ T.A₀) (hg : g ∈ T.A₀) (c : ℝ) :
    -∫ x, (φ x + c) * T.Γ fi g x ∂T.μ =
      ∫ x, g x * ((φ x + c) * T.L fi x) ∂T.μ + ∫ x, g x * T.Γ fi φ x ∂T.μ := by
  have hφg : φ * g ∈ T.A₀ := T.A₀.mul_mem hφ hg
  have iA := integrable_of_mem T (T.A₀.mul_mem hφ (T.Γ_mem _ hfi _ hg))
  have iB := integrable_of_mem T (T.A₀.mul_mem hg (T.Γ_mem _ hfi _ hφ))
  have iC := integrable_of_mem T (T.Γ_mem _ hfi _ hg)
  have iD := integrable_of_mem T (T.A₀.mul_mem hg (T.L_mem _ hfi))
  have iE := integrable_of_mem T (T.A₀.mul_mem hφg (T.L_mem _ hfi))
  have hae : T.Γ fi (φ * g) =ᵐ[T.μ] φ * T.Γ fi g + g * T.Γ fi φ := by
    filter_upwards [T.Γ_symm fi hfi _ hφg, Γ_mul_left T hφ hg hfi, T.Γ_symm g hg fi hfi,
      T.Γ_symm φ hφ fi hfi] with x a1 a2 a3 a4
    simp only [Pi.add_apply, Pi.mul_apply] at a2 ⊢
    rw [a1, a2, a3, a4]
  have k1 := T.ibp fi hfi (φ * g) hφg
  have hsum : ∫ x, (φ * T.Γ fi g + g * T.Γ fi φ) x ∂T.μ =
      ∫ x, φ x * T.Γ fi g x ∂T.μ + ∫ x, g x * T.Γ fi φ x ∂T.μ := integral_add iA iB
  rw [integral_congr_ae hae, hsum] at k1
  have k2 := T.ibp fi hfi g hg
  have e1 : ∫ x, (φ x + c) * T.Γ fi g x ∂T.μ =
      ∫ x, φ x * T.Γ fi g x ∂T.μ + c * ∫ x, T.Γ fi g x ∂T.μ := by
    have : (fun x => (φ x + c) * T.Γ fi g x) = fun x => φ x * T.Γ fi g x + c * T.Γ fi g x := by
      funext x; ring
    rw [this, integral_add (f := fun x => φ x * T.Γ fi g x) (g := fun x => c * T.Γ fi g x) iA
      (iC.const_mul c), integral_const_mul]
  have e2 : ∫ x, g x * ((φ x + c) * T.L fi x) ∂T.μ =
      ∫ x, (φ * g) x * T.L fi x ∂T.μ + c * ∫ x, g x * T.L fi x ∂T.μ := by
    have : (fun x => g x * ((φ x + c) * T.L fi x)) =
        fun x => (φ * g) x * T.L fi x + c * (g x * T.L fi x) := by
      funext x; simp only [Pi.mul_apply]; ring
    rw [this, integral_add (f := fun x => (φ * g) x * T.L fi x) (g := fun x => c * (g x * T.L fi x))
      iE (iD.const_mul c), integral_const_mul]
  rw [e1, e2, k1, k2]; ring

theorem chain_rule_L {k : ℕ} (ψ : (Fin k → ℝ) → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (h0 : ψ 0 = 0)
    (f : Fin k → E → ℝ) (hf : ∀ i, f i ∈ T.A₀) :
    T.L (fun x => ψ (fun i => f i x)) =ᵐ[T.μ]
      fun x => ∑ i, pderiv ψ i (fun j => f j x) * T.L (f i) x +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * T.Γ (f i) (f j) x := by
  set F : E → ℝ := fun x => ψ (fun i => f i x) with hFdef
  have hF : F ∈ T.A₀ := T.comp_mem k ψ hψ h0 f hf
  set p : Fin k → E → ℝ := fun i x => pderiv ψ i (fun j => f j x) with hp
  set q : Fin k → Fin k → E → ℝ := fun i j x => pderiv₂ ψ i j (fun l => f l x) with hq
  have hψi : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (pderiv ψ i) := contDiff_pderiv hψ
  have hψij : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun z => pderiv₂ ψ i j z) := fun i j => by
    unfold pderiv₂
    exact ((hψi i).fderiv_right (by simp)).clm_apply contDiff_const
  -- the pieces of the right-hand side
  set G1 : Fin k → E → ℝ := fun i x => p i x * T.L (f i) x with hG1
  set G2 : Fin k → E → ℝ := fun i x => ∑ j, q i j x * T.Γ (f i) (f j) x with hG2
  have hG1m : ∀ i ∈ (Finset.univ : Finset (Fin k)), G1 i ∈ T.A₀ := fun i _ =>
    comp_mul_mem T (pderiv ψ i) (hψi i) f hf (T.L_mem _ (hf i))
  have hG2m : ∀ i ∈ (Finset.univ : Finset (Fin k)), G2 i ∈ T.A₀ := fun i _ =>
    sum_fn_mem T _ _ (fun j _ => comp_mul_mem T _ (hψij i j) f hf (T.Γ_mem _ (hf i) _ (hf j)))
  have hS1 : (fun x => ∑ i, G1 i x) ∈ T.A₀ := sum_fn_mem T _ _ hG1m
  have hS2 : (fun x => ∑ i, G2 i x) ∈ T.A₀ := sum_fn_mem T _ _ hG2m
  have hR : (fun x => ∑ i, pderiv ψ i (fun j => f j x) * T.L (f i) x +
      ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * T.Γ (f i) (f j) x) ∈ T.A₀ := by
    have := T.A₀.add_mem hS1 hS2
    exact this
  have hd : T.L F - (fun x => ∑ i, pderiv ψ i (fun j => f j x) * T.L (f i) x +
      ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * T.Γ (f i) (f j) x) ∈ T.A₀ :=
    T.A₀.sub_mem (T.L_mem _ hF) hR
  have key := ae_zero_of_orth T hd (fun g hg => by
    have iLF := integrable_of_mem T (T.A₀.mul_mem hg (T.L_mem _ hF))
    have iR' : Integrable (fun x => g x * (∑ i, G1 i x + ∑ i, G2 i x)) T.μ :=
      integrable_of_mem T (T.A₀.mul_mem hg hR)
    have e1 : (fun x => g x * (T.L F - (fun x => ∑ i, pderiv ψ i (fun j => f j x) * T.L (f i) x +
        ∑ i, ∑ j, pderiv₂ ψ i j (fun l => f l x) * T.Γ (f i) (f j) x)) x) =
        fun x => g x * T.L F x - g x * (∑ i, G1 i x + ∑ i, G2 i x) := by
      funext x; simp only [Pi.sub_apply, hG1, hG2]; ring
    rw [e1, integral_sub (f := fun x => g x * T.L F x)
      (g := fun x => g x * (∑ i, G1 i x + ∑ i, G2 i x)) iLF iR']
    have hsplit : ∫ x, g x * (∑ i, G1 i x + ∑ i, G2 i x) ∂T.μ =
        ∫ x, g x * ∑ i, G1 i x ∂T.μ + ∫ x, g x * ∑ i, G2 i x ∂T.μ := by
      simp only [mul_add]
      exact integral_add (integrable_of_mem T (T.A₀.mul_mem hg hS1))
        (integrable_of_mem T (T.A₀.mul_mem hg hS2))
    rw [hsplit, integral_mul_sum T _ G1 hG1m hg, integral_mul_sum T _ G2 hG2m hg]
    -- main computation
    have hdiff := T.diffusion k ψ hψ h0 f hf g hg
    have step1 : ∫ x, g x * T.L F x ∂T.μ = -∑ i, ∫ x, p i x * T.Γ (f i) g x ∂T.μ := by
      rw [T.ibp F hF g hg, integral_congr_ae hdiff]
      have : ∫ x, ∑ i, p i x * T.Γ (f i) g x ∂T.μ = ∑ i, ∫ x, p i x * T.Γ (f i) g x ∂T.μ :=
        integral_finsetSum _ (fun i _ => by
          have := comp_mul_mem T (pderiv ψ i) (hψi i) f hf (T.Γ_mem _ (hf i) _ hg)
          exact integrable_of_mem T this)
      rw [this]
    have step2 : ∀ i, -∫ x, p i x * T.Γ (f i) g x ∂T.μ =
        ∫ x, g x * G1 i x ∂T.μ + ∫ x, g x * G2 i x ∂T.μ := by
      intro i
      set φ : E → ℝ := fun x => pderiv ψ i (fun j => f j x) - pderiv ψ i 0 with hφ
      have hφm : φ ∈ T.A₀ := T.comp_mem k (fun z => pderiv ψ i z - pderiv ψ i 0)
        ((hψi i).sub contDiff_const) (by simp) f hf
      have ht := term_ibp T (hf i) hφm hg (pderiv ψ i 0)
      simp only [hφ, sub_add_cancel] at ht
      have hΓφ : T.Γ (f i) φ =ᵐ[T.μ] G2 i := by
        have hχ : ContDiff ℝ (⊤ : ℕ∞) (fun z => pderiv ψ i z - pderiv ψ i 0) :=
          (hψi i).sub contDiff_const
        have hd2 := T.diffusion k (fun z => pderiv ψ i z - pderiv ψ i 0) hχ (by simp) f hf
          (f i) (hf i)
        have hsym : ∀ j, ∀ᵐ x ∂T.μ, T.Γ (f j) (f i) x = T.Γ (f i) (f j) x := fun j =>
          T.Γ_symm _ (hf j) _ (hf i)
        have hsym' := ae_all_iff.2 hsym
        filter_upwards [T.Γ_symm (f i) (hf i) φ hφm, hd2, hsym'] with x a1 a2 a3
        rw [a1]
        have : (fun x => (fun z => pderiv ψ i z - pderiv ψ i 0) (fun j => f j x)) = φ := rfl
        simp only [this] at a2
        rw [a2]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [a3 j]
        congr 1
        simp only [pderiv, fderiv_sub_const]
        rfl
      have : ∫ x, g x * T.Γ (f i) φ x ∂T.μ = ∫ x, g x * G2 i x ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [hΓφ] with x hx
        rw [hx]
      rw [this] at ht
      exact ht
    rw [step1]
    have hs : ∑ i, (-∫ x, p i x * T.Γ (f i) g x ∂T.μ) =
        ∑ i, (∫ x, g x * G1 i x ∂T.μ + ∫ x, g x * G2 i x ∂T.μ) :=
      Finset.sum_congr rfl (fun i _ => step2 i)
    rw [Finset.sum_neg_distrib, Finset.sum_add_distrib] at hs
    linarith)
  filter_upwards [key] with x hx
  simp only [Pi.sub_apply, Pi.zero_apply] at hx
  linarith

end DiffusionTriple

end MarkovTriple.BGL
