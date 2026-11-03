import Mathlib
import MarkovTriple.BGL.Theory.Extension.HessExt

/-!
# Prop. 3.3.16 (vi), (viii) (BGL p. 160): Leibniz rule and the extended inequality (3.3.7) for `H` on `𝒟(L) × 𝒟(ℰ) × 𝒜₀`
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma G1_ae (a : T.A₀) : (G1 T a : E → ℝ) =ᵐ[T.μ] G T a.1 a.1 := Integrable.coeFn_toL1 _

lemma G2cls_ae (a : T.A₀) : (G2cls T a : E → ℝ) =ᵐ[T.μ] T.toDiffusionTriple.Γ₂ a.1 a.1 :=
  Integrable.coeFn_toL1 _

/-- **BGL Prop. 3.3.16 (vi)**: for `f ∈ 𝒟(L)`, `h, k ∈ 𝒜₀`, `g ∈ 𝒟(ℰ)`:
`H(f)(k g, h) = k H(f)(g,h) + g H(f)(k,h)` a.e. -/
theorem hessE_mulE {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (k h : T.A₀) (g : T.formDomain) :
    (hessE hCD u hu (mulE k g) h : E → ℝ) =ᵐ[T.μ] fun x =>
      k.1 x * (hessE hCD u hu g h : E → ℝ) x +
        ((g : Lp ℝ 2 T.μ) : E → ℝ) x * (hessE hCD u hu (T.toDiffusionTriple.clsQ k) h : E → ℝ) x := by
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨b, hb⟩ := exists_formConv g
  have s1 := hessE_tendsto hCD h ha hb
  have s2 := hessE_tendsto hCD h ha (formConv_const k)
  have s3 := FormConv.cls hb
  have s4 := hessE_tendsto hCD h ha (mulE_formConv k hb)
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨φ, hφ, a1, a2⟩ := Lp_ae_subseq_two s1 s2
  obtain ⟨ψ, hψ, a3, a4⟩ := Lp_ae_subseq_two (s3.comp hφ.tendsto_atTop) (s4.comp hφ.tendsto_atTop)
  have hall : ∀ᵐ x ∂T.μ, ∀ m, (HH T (a m) (k * b m) h : E → ℝ) x =
      k.1 x * (HH T (a m) (b m) h : E → ℝ) x +
        ((T.toDiffusionTriple.cls (b m) : Lp ℝ 2 T.μ) : E → ℝ) x * (HH T (a m) k h : E → ℝ) x := by
    rw [ae_all_iff]
    intro m
    filter_upwards [HH_ae (a m) (k * b m) h, HH_ae (a m) (b m) h, HH_ae (a m) k h,
      DiffusionTriple.coeFn_cls T.toDiffusionTriple (b m),
      Hess_mul_mid (A₀_memA (a m).2) (A₀_memA (b m).2) (A₀_memA k.2) (A₀_memA h.2)] with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4]
    exact h5
  filter_upwards [a1, a2, a3, a4, hall] with x h1 h2 h3 h4 h5
  have h6 : Tendsto (fun m => (HH T (a (φ (ψ m))) (k * b (φ (ψ m))) h : E → ℝ) x) atTop
      (𝓝 (k.1 x * (hessE hCD u hu g h : E → ℝ) x +
        ((g : Lp ℝ 2 T.μ) : E → ℝ) x * (hessE hCD u hu (T.toDiffusionTriple.clsQ k) h : E → ℝ) x)) := by
    have e1 := (h1.comp hψ.tendsto_atTop).const_mul (k.1 x)
    have e2 := h3.mul (h2.comp hψ.tendsto_atTop)
    exact (e1.add e2).congr (fun m => (h5 (φ (ψ m))).symm)
  exact tendsto_nhds_unique h4 h6

/-- **BGL Prop. 3.3.16 (viii)**: the extended inequality (3.3.7).  If `a_k → f` in `𝒟(L)` (graph), and
`γ₁, γ₂` are the `L¹`-limits of `Γ(a_k)`, `Γ₂(a_k)` (Prop. 3.3.16 (i)–(iii), `gamma_limits`), then for
`g ∈ 𝒟(ℰ)`, `h ∈ 𝒜₀`:
`H(f)(g,h)² ≤ (γ₂ − ργ₁) · Γ(g) · Γ(h)` a.e., with `Γ(g) = gammaE g g`. -/
theorem hessE_ineq {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u : Lp ℝ 2 T.μ}
    {hu : u ∈ T.toDiffusionTriple.generator.domain} {a : ℕ → T.A₀} (ha : GraphConv T a u hu)
    {γ₁ γ₂ : Lp ℝ 1 T.μ} (hγ₁ : Tendsto (fun k => G1 T (a k)) atTop (𝓝 γ₁))
    (hγ₂ : Tendsto (fun k => G2cls T (a k)) atTop (𝓝 γ₂)) (g : T.formDomain) (h : T.A₀) :
    ∀ᵐ x ∂T.μ, ((hessE hCD u hu g h : Lp ℝ 1 T.μ) : E → ℝ) x ^ 2 ≤
      (((γ₂ : Lp ℝ 1 T.μ) : E → ℝ) x - ρ * ((γ₁ : Lp ℝ 1 T.μ) : E → ℝ) x) *
        (((gammaE T g g : Lp ℝ 1 T.μ) : E → ℝ) x * G T h.1 h.1 x) := by
  obtain ⟨b, hb⟩ := exists_formConv g
  have s1 := hessE_tendsto hCD h ha hb
  have s2 := gammaE_tendsto hb hb
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨φ, hφ, a1, a2⟩ := Lp_ae_subseq_two s1 s2
  obtain ⟨ψ, hψ, a3, a4⟩ := Lp_ae_subseq_two (hγ₁.comp hφ.tendsto_atTop) (hγ₂.comp hφ.tendsto_atTop)
  have hall : ∀ᵐ x ∂T.μ, ∀ m,
      ((HH T (a m) (b m) h : Lp ℝ 1 T.μ) : E → ℝ) x ^ 2 ≤
        (((G2cls T (a m) : Lp ℝ 1 T.μ) : E → ℝ) x - ρ * ((G1 T (a m) : Lp ℝ 1 T.μ) : E → ℝ) x) *
          (((GG T (b m) (b m) : Lp ℝ 1 T.μ) : E → ℝ) x * G T h.1 h.1 x) := by
    rw [ae_all_iff]
    intro m
    filter_upwards [HH_ae (a m) (b m) h, G1_ae (a m), G2cls_ae (a m), GG_ae (b m) (b m),
      hessian_general_ineq hCD (A₀_memA (a m).2) (A₀_memA (b m).2) (A₀_memA h.2)] with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4]
    exact h5
  filter_upwards [a1, a2, a3, a4, hall] with x h1 h2 h3 h4 h5
  have l1 := (h1.comp hψ.tendsto_atTop).pow 2
  have l2 := ((h4.sub (h3.const_mul ρ)).mul ((h2.comp hψ.tendsto_atTop).mul_const (G T h.1 h.1 x)))
  refine le_of_tendsto_of_tendsto' l1 ?_ (fun m => h5 (φ (ψ m)))
  exact l2

end FullTriple

end MarkovTriple.BGL
