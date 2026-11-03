import Mathlib
import MarkovTriple.BGL.Theory.Extension.Gamma2E
import MarkovTriple.BGL.Theory.Extension.SeqLin
import MarkovTriple.BGL.Theory.Extension.HessExtLin

/-!
# The bilinear `Γ₂` on `𝒟(L) × 𝒟(L)`: bilinearity, symmetry, bound, and the link with the quadratic `Γ₂`
(BGL Prop. 3.3.16 (i)–(iii), p. 160; Prop. 3.3.17)

Round 15 gap closure; statements fixed in `Extension/STATEMENTS_R15_Gaps.md` (3a).  `GG2_self` links the bilinear `𝒜₀`-level
class `GG2 a a` with the class `G2cls a` of `Γ₂(a)` used by `gamma_limits` and `Γ₂_ext_eq`; `gamma2E_self_tendsto` and
`Γ₂_ext_eq_gamma2E` then identify the quadratic limit `γ₂` of `gamma_limits` with the diagonal `gamma2E u u`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- `GG2 a a` is the class `G2cls a` of `Γ₂(a)` (`Γ₂(a) = Γ₂(a,a)`). -/
lemma GG2_self (a : T.A₀) : GG2 T a a = G2cls T a := by
  refine Lp.ext ?_
  filter_upwards [GG2_ae a a, G2cls_ae a] with x h1 h2
  rw [h1, h2]

lemma GG2_lin_left (a a' b : T.A₀) (c : ℝ) : GG2 T (a + c • a') b = GG2 T a b + c • GG2 T a' b := by
  refine Lp.ext ?_
  filter_upwards [GG2_ae (a + c • a') b, GG2_ae a b, GG2_ae a' b,
    Lp.coeFn_add (GG2 T a b) (c • GG2 T a' b), Lp.coeFn_smul c (GG2 T a' b),
    Γ₂_lin_left (A₀_memA a.2) (A₀_memA a'.2) (A₀_memA b.2) c] with x e1 e2 e3 e4 e5 e6
  rw [e4, Pi.add_apply, e5, Pi.smul_apply, e1, e2, e3, coe_lin, e6]
  rfl

/-- **Symmetry of the extended bilinear `Γ₂`.** -/
theorem gamma2E_comm {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u v : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (hv : v ∈ T.toDiffusionTriple.generator.domain) :
    gamma2E hCD u v hu hv = gamma2E hCD v u hv hu := by
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨b, hb⟩ := exists_graphConv v hv
  refine tendsto_nhds_unique (gamma2E_tendsto hCD ha hb) ?_
  exact (gamma2E_tendsto hCD hb ha).congr (fun k => GG2_comm _ _)

/-- **Linearity of the extended `Γ₂` in the first slot.** -/
theorem gamma2E_lin_left {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u u' w v : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (hu' : u' ∈ T.toDiffusionTriple.generator.domain)
    (hw : w ∈ T.toDiffusionTriple.generator.domain) (hv : v ∈ T.toDiffusionTriple.generator.domain)
    (c : ℝ) (hwe : w = u + c • u') :
    gamma2E hCD w v hw hv = gamma2E hCD u v hu hv + c • gamma2E hCD u' v hu' hv := by
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨a', ha'⟩ := exists_graphConv u' hu'
  obtain ⟨b, hb⟩ := exists_graphConv v hv
  have t1 := gamma2E_tendsto hCD (hu := hw) (ha.lin (hw := hw) c hwe ha') hb
  have t2 := (gamma2E_tendsto hCD ha hb).add ((gamma2E_tendsto hCD ha' hb).const_smul c)
  exact tendsto_nhds_unique t1 (t2.congr (fun k => (GG2_lin_left (a k) (a' k) (b k) c).symm))

/-- **Linearity of the extended `Γ₂` in the second slot** (from symmetry). -/
theorem gamma2E_lin_right {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u v v' w : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (hv : v ∈ T.toDiffusionTriple.generator.domain)
    (hv' : v' ∈ T.toDiffusionTriple.generator.domain) (hw : w ∈ T.toDiffusionTriple.generator.domain)
    (c : ℝ) (hwe : w = v + c • v') :
    gamma2E hCD u w hu hw = gamma2E hCD u v hu hv + c • gamma2E hCD u v' hu hv' := by
  rw [gamma2E_comm hCD hu hw, gamma2E_comm hCD hu hv, gamma2E_comm hCD hu hv']
  exact gamma2E_lin_left hCD hv hv' hw hu c hwe

/-- **Boundedness of the extended `Γ₂`**: `‖Γ₂(u,v)‖₁ ≤ (2(1+|ρ|)+4|ρ|) ‖(u,Lu)‖ ‖(v,Lv)‖`. -/
theorem gamma2E_bound {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u v : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (hv : v ∈ T.toDiffusionTriple.generator.domain) :
    ‖gamma2E hCD u v hu hv‖ ≤ (2 * (1 + |ρ|) + 4 * |ρ|) * ‖(u, T.toDiffusionTriple.generator ⟨u, hu⟩)‖ *
      ‖(v, T.toDiffusionTriple.generator ⟨v, hv⟩)‖ := by
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨b, hb⟩ := exists_graphConv v hv
  have t1 := (gamma2E_tendsto hCD ha hb).norm
  have t2 : Tendsto (fun k => (2 * (1 + |ρ|) + 4 * |ρ|) * ‖jL T (a k)‖ * ‖jL T (b k)‖) atTop
      (𝓝 ((2 * (1 + |ρ|) + 4 * |ρ|) * ‖(u, T.toDiffusionTriple.generator ⟨u, hu⟩)‖ *
        ‖(v, T.toDiffusionTriple.generator ⟨v, hv⟩)‖)) :=
    ((ha.norm).const_mul _).mul hb.norm
  exact le_of_tendsto_of_tendsto' t1 t2 (fun k => norm_GG2_le hCD (a k) (b k))

/-- **Identification on `𝒜₀`**: `Γ₂([a],[b]) = [Γ₂(a,b)]`. -/
theorem gamma2E_cls {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (a b : T.A₀) :
    gamma2E hCD (T.toDiffusionTriple.cls a) (T.toDiffusionTriple.cls b)
      (T.toDiffusionTriple.cls_mem_generator_domain a) (T.toDiffusionTriple.cls_mem_generator_domain b) =
      GG2 T a b := by
  have hg : ∀ c : T.A₀, GraphConv T (fun _ => c) (T.toDiffusionTriple.cls c)
      (T.toDiffusionTriple.cls_mem_generator_domain c) := by
    intro c
    unfold GraphConv
    rw [DiffusionTriple.generator_cls T.toDiffusionTriple c (T.toDiffusionTriple.cls_mem_generator_domain c)]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (gamma2E_tendsto hCD (hg a) (hg b)) tendsto_const_nhds

/-- The quadratic `Γ₂` of `gamma_limits` is the diagonal of the bilinear `gamma2E`:
`Γ₂(a_k) = Γ₂(a_k, a_k) → Γ₂(u,u)` in `L¹` along every graph-convergent `a_k → u`. -/
theorem gamma2E_self_tendsto {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u : Lp ℝ 2 T.μ}
    {hu : u ∈ T.toDiffusionTriple.generator.domain} {a : ℕ → T.A₀} (ha : GraphConv T a u hu) :
    Tendsto (fun k => G2cls T (a k)) atTop (𝓝 (gamma2E hCD u u hu hu)) :=
  (gamma2E_tendsto hCD ha ha).congr (fun k => GG2_self (a k))

/-- **`Γ₂_ext_eq` for the bilinear `Γ₂`** (BGL Prop. 3.3.17): for `f ∈ 𝒜 ∩ 𝒟(L)`, `gamma2E [f] [f] = Γ₂^𝒜(f)` a.e. -/
theorem Γ₂_ext_eq_gamma2E {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A)
    (hf2 : MemLp f 2 T.μ) (hu : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain) :
    (gamma2E hCD (hf2.toLp f) (hf2.toLp f) hu hu : E → ℝ) =ᵐ[T.μ] T.toDiffusionTriple.Γ₂ f f := by
  obtain ⟨a, ha⟩ := exists_graphConv (hf2.toLp f) hu
  exact Γ₂_ext_eq hf hf2 hu ha (gamma2E_self_tendsto hCD ha)

end FullTriple

end MarkovTriple.BGL
