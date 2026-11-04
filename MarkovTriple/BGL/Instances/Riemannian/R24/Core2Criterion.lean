import Mathlib
import MarkovTriple.BGL.Theory.Extension.Core2Reduce
import MarkovTriple.BGL.Theory.Poincare

/-!
# Round 24 (stream D), part A: `Core2` as a duality statement (abstract, any `FullTriple`)

* `FullTriple.core2_orth` : a continuous-functional obstruction criterion: `Core2` forces every `L²`-pair `(g,h)`
  that annihilates `((1-L)b, L(1-L)b)`, `b ∈ 𝒜₀`, to annihilate `([a], [La])`, `a ∈ 𝒜₀`.
* `FullTriple.core2_iff_dense` : `Core2 ↔ (1-L)²𝒜₀ is dense in L²` (the converse of `core2_of_dense`, from ESA F10).

See `STATEMENTS_R24_D.md`.  No new axioms.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- **Obstruction criterion** (D-A1).  If `Core2` holds, a pair `(g,h) ∈ L² × L²` with
`⟨[b]-[Lb], g⟩ + ⟨[Lb]-[LLb], h⟩ = 0` for all `b ∈ 𝒜₀` also satisfies `⟨[a], g⟩ + ⟨[La], h⟩ = 0` for all `a ∈ 𝒜₀`.
Contrapositive: a pair violating the conclusion refutes `Core2`. -/
theorem core2_orth (hC : T.Core2) (g h : Lp ℝ 2 T.μ)
    (hb : ∀ b : T.A₀, inner ℝ (T.toDiffusionTriple.cls b - T.toDiffusionTriple.Lcls b) g +
      inner ℝ (T.toDiffusionTriple.Lcls b - LLₗ T b) h = 0) (a : T.A₀) :
    inner ℝ (T.toDiffusionTriple.cls a) g + inner ℝ (T.toDiffusionTriple.Lcls a) h = 0 := by
  obtain ⟨b, h1, h2⟩ := hC a
  have hc : Tendsto (fun n => inner ℝ (T.toDiffusionTriple.cls (b n) - T.toDiffusionTriple.Lcls (b n)) g +
      inner ℝ (T.toDiffusionTriple.Lcls (b n) - LLₗ T (b n)) h) atTop
      (𝓝 (inner ℝ (T.toDiffusionTriple.cls a) g + inner ℝ (T.toDiffusionTriple.Lcls a) h)) :=
    (((continuous_id.inner continuous_const).tendsto _).comp h1).add
      (((continuous_id.inner continuous_const).tendsto _).comp h2)
  have h0 : Tendsto (fun n => inner ℝ (T.toDiffusionTriple.cls (b n) - T.toDiffusionTriple.Lcls (b n)) g +
      inner ℝ (T.toDiffusionTriple.Lcls (b n) - LLₗ T (b n)) h) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun n => (hb (b n)).symm
  exact tendsto_nhds_unique hc h0

/-- **`Core2 ↔` density of `(1-L)²𝒜₀`** (D-A2): the converse of `core2_of_dense`, using F10. -/
theorem core2_iff_dense : T.Core2 ↔ Dense (Set.range (Ψₗ T)) := by
  refine ⟨fun hC => ?_, core2_of_dense⟩
  have hsub : ∀ a : T.A₀, Φₗ T a ∈ closure (Set.range (Ψₗ T)) := fun a => by
    obtain ⟨b, h1, h2⟩ := hC a
    have hl : Tendsto (fun n => Ψₗ T (b n)) atTop (𝓝 (Φₗ T a)) := by
      have := h1.sub h2
      exact this.congr fun n => rfl
    exact mem_closure_of_tendsto hl (Eventually.of_forall fun n => ⟨b n, rfl⟩)
  rw [dense_iff_closure_eq, eq_univ_iff_forall]
  intro w
  have hw := DiffusionTriple.mem_closure_range_one_sub_L T.toDiffusionTriple T.esaProp w
  refine closure_minimal ?_ isClosed_closure hw
  rintro y ⟨a, rfl⟩
  exact hsub a


section pairing

/-- `⟨[b], [f]⟩ = ∫ b f`. -/
lemma inner_cls_f {f : E → ℝ} (hf2 : MemLp f 2 T.μ) (b : T.A₀) :
    inner ℝ (T.toDiffusionTriple.cls b) (hf2.toLp f) = ∫ x, b.1 x * f x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_cls T.toDiffusionTriple b] with x h1 h2
  rw [h1, h2]

/-- `⟨[L b], [f]⟩ = ∫ (L b) f`. -/
lemma inner_Lcls_f {f : E → ℝ} (hf2 : MemLp f 2 T.μ) (b : T.A₀) :
    inner ℝ (T.toDiffusionTriple.Lcls b) (hf2.toLp f) = ∫ x, T.L b.1 x * f x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b] with x h1 h2
  rw [h1, h2]

/-- `⟨[L L b], [f]⟩ = ∫ (L L b) f`. -/
lemma inner_LL_f {f : E → ℝ} (hf2 : MemLp f 2 T.μ) (b : T.A₀) :
    inner ℝ (LLₗ T b) (hf2.toLp f) = ∫ x, T.L (T.L b.1) x * f x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple
    (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀)] with x h1 h2
  show (T.toDiffusionTriple.Lcls (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀) : E → ℝ) x * _ = _
  rw [h1, h2]

end pairing

end FullTriple

end MarkovTriple.BGL
