import Mathlib
import MarkovTriple.BGL.Theory.Extension.MulDomain

/-!
# Prop. 3.3.16 (vii) (BGL p. 160): `Γ₂(hf,g) = hΓ₂(f,g) + fΓ₂(h,g) + 2H(g)(f,h)` on `𝒟(L)`

for `h ∈ 𝒜₀`, `f, g ∈ 𝒟(L)` (with `hf ∈ 𝒟(L)` by `mulE_mem_domain`).  The book: "the change of variables formula (3.3.4)
goes to the limit".  Here `Γ₂` is the bilinear `gamma2E` and `H(g)(f,h)` is `hessE` with `f ∈ 𝒟(L) ⊂ 𝒟(ℰ)` in the middle slot.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace LinearPMap

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma graphConv_const (k : T.A₀) :
    GraphConv T (fun _ => k) (T.toDiffusionTriple.cls k)
      (DiffusionTriple.cls_mem_generator_domain T.toDiffusionTriple k) := by
  unfold GraphConv
  rw [DiffusionTriple.generator_cls]
  exact tendsto_const_nhds

/-- **BGL Prop. 3.3.16 (vii)** (`Γ₂` part). -/
theorem gamma2E_mulE {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (k : T.A₀) {u v : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (hv : v ∈ T.toDiffusionTriple.generator.domain)
    (hdom : ((mulE k ⟨u, domain_subset_formDomain hu⟩ : T.formDomain) : Lp ℝ 2 T.μ) ∈
      T.toDiffusionTriple.generator.domain) :
    (gamma2E hCD _ v hdom hv : E → ℝ) =ᵐ[T.μ] fun x =>
      k.1 x * (gamma2E hCD u v hu hv : E → ℝ) x +
        (u : E → ℝ) x * (gamma2E hCD (T.toDiffusionTriple.cls k) v
          (DiffusionTriple.cls_mem_generator_domain T.toDiffusionTriple k) hv : E → ℝ) x +
        2 * (hessE hCD v hv ⟨u, domain_subset_formDomain hu⟩ k : E → ℝ) x := by
  obtain ⟨hd, hg⟩ := mulE_mem_domain k hu
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨c, hc⟩ := exists_graphConv v hv
  obtain ⟨_, hfc⟩ := ha.formConv
  have s1 := gamma2E_tendsto hCD ha hc
  have s2 := gamma2E_tendsto hCD (graphConv_const k) hc
  have s3 := GraphConv.cls ha
  have s4 := hessE_tendsto hCD k hc hfc
  have s5 := gamma2E_tendsto hCD (hg a ha) hc
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨φ, hφ, a1, a2⟩ := Lp_ae_subseq_two s1 s2
  obtain ⟨ψ, hψ, a3, a4⟩ := Lp_ae_subseq_two (s3.comp hφ.tendsto_atTop) (s4.comp hφ.tendsto_atTop)
  obtain ⟨χ, hχ, a5⟩ := Lp_ae_subseq ((s5.comp hφ.tendsto_atTop).comp hψ.tendsto_atTop)
  have hall : ∀ᵐ x ∂T.μ, ∀ m, (GG2 T (k * a m) (c m) : E → ℝ) x =
      k.1 x * (GG2 T (a m) (c m) : E → ℝ) x +
        ((T.toDiffusionTriple.cls (a m) : Lp ℝ 2 T.μ) : E → ℝ) x * (GG2 T k (c m) : E → ℝ) x +
          2 * (HH T (c m) (a m) k : E → ℝ) x := by
    rw [ae_all_iff]
    intro m
    filter_upwards [GG2_ae (k * a m) (c m), GG2_ae (a m) (c m), GG2_ae k (c m),
      DiffusionTriple.coeFn_cls T.toDiffusionTriple (a m), HH_ae (c m) (a m) k,
      Γ₂_mul_Hess (A₀_memA k.2) (A₀_memA (a m).2) (A₀_memA (c m).2)] with x h1 h2 h3 h4 h5 h6
    rw [h1, h2, h3, h4, h5, ← Hess_symm]
    exact h6
  filter_upwards [a1, a2, a3, a4, a5, hall] with x h1 h2 h3 h4 h5 h6
  have h7 : Tendsto (fun m => (GG2 T (k * a (φ (ψ (χ m)))) (c (φ (ψ (χ m)))) : E → ℝ) x) atTop
      (𝓝 (k.1 x * (gamma2E hCD u v hu hv : E → ℝ) x +
        (u : E → ℝ) x * (gamma2E hCD (T.toDiffusionTriple.cls k) v
          (DiffusionTriple.cls_mem_generator_domain T.toDiffusionTriple k) hv : E → ℝ) x +
        2 * (hessE hCD v hv ⟨u, domain_subset_formDomain hu⟩ k : E → ℝ) x)) := by
    have e1 := ((h1.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop).const_mul (k.1 x)
    have e2 := (h3.comp hχ.tendsto_atTop).mul ((h2.comp hψ.tendsto_atTop).comp hχ.tendsto_atTop)
    have e3 := (h4.comp hχ.tendsto_atTop).const_mul 2
    exact ((e1.add e2).add e3).congr (fun m => (h6 _).symm)
  exact tendsto_nhds_unique h5 h7

end FullTriple

end MarkovTriple.BGL
