import Mathlib
import MarkovTriple.BGL.Theory.Extension.IdentIBP
import MarkovTriple.BGL.Theory.Extension.HessExt2

/-!
# Prop. 3.3.17 (first part, BGL pp. 161–162): the two definitions of the Hessian coincide on `𝒜 ∩ 𝒟(L)`

Hypotheses: ESA (F10) and `CD(ρ,n)`.  For `f ∈ 𝒜 ∩ 𝒟(L)` (i.e. `f ∈ 𝒜 ∩ L²` whose class is in `𝒟(L)`):

* `hessE_eq_Hess`: for `g, h ∈ 𝒜₀`, the extended Hessian `H(f)(g,h)` (`hessE`, `Prop 3.3.16 (iv)`) equals the
  `𝒜`-Hessian `Hess f g h` a.e.  (book: `∫ k H(f)(g,h) = ∫ f E(g,h,k) = ∫ k H_𝒜(f)(g,h)`, then the limit
  `f_ℓ → f` in `𝒟(L)`);
* `hessE_eq_Hess'`: the same for `g ∈ 𝒜 ∩ 𝒟(ℰ)` (book: "replacing `g ∈ 𝒜₀` by `g ∈ 𝒟(ℰ)`, the same procedure using the
  other chain rule" — here the first-order property (vi) of the extension and of `Hess`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- `ψ ↦ ∫ k ψ` is continuous on `L¹` for bounded measurable `k`. -/
lemma tendsto_int_mul_L1 {k : E → ℝ} (hkm : Measurable k) {M : ℝ} (hk : ∀ x, |k x| ≤ M)
    {F : ℕ → Lp ℝ 1 T.μ} {ψ : Lp ℝ 1 T.μ} (h : Tendsto F atTop (𝓝 ψ)) :
    Tendsto (fun n => ∫ x, k x * (F n : E → ℝ) x ∂T.μ) atTop (𝓝 (∫ x, k x * (ψ : E → ℝ) x ∂T.μ)) := by
  have hb : ∀ᵐ x ∂T.μ, ‖k x‖ ≤ M := Eventually.of_forall fun x => by simpa using hk x
  have iF : ∀ n, Integrable (fun x => k x * (F n : E → ℝ) x) T.μ := fun n =>
    (L1.integrable_coeFn (F n)).bdd_mul hkm.aestronglyMeasurable hb
  have iψ : Integrable (fun x => k x * (ψ : E → ℝ) x) T.μ :=
    (L1.integrable_coeFn ψ).bdd_mul hkm.aestronglyMeasurable hb
  rw [tendsto_iff_dist_tendsto_zero] at h ⊢
  have key : ∀ n, dist (∫ x, k x * (F n : E → ℝ) x ∂T.μ) (∫ x, k x * (ψ : E → ℝ) x ∂T.μ) ≤
      |M| * dist (F n) ψ := by
    intro n
    have iD : Integrable (fun x => |(F n : E → ℝ) x - (ψ : E → ℝ) x|) T.μ :=
      ((L1.integrable_coeFn (F n)).sub (L1.integrable_coeFn ψ)).abs
    rw [Real.dist_eq, dist_eq_norm, L1.norm_eq_integral_norm]
    have e1 : ∫ x, k x * (F n : E → ℝ) x ∂T.μ - ∫ x, k x * (ψ : E → ℝ) x ∂T.μ =
        ∫ x, k x * ((F n : E → ℝ) x - (ψ : E → ℝ) x) ∂T.μ := by
      rw [← integral_sub (iF n) iψ]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      ring
    have e2 : ∫ x, ‖((F n - ψ : Lp ℝ 1 T.μ) : E → ℝ) x‖ ∂T.μ =
        ∫ x, |(F n : E → ℝ) x - (ψ : E → ℝ) x| ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (F n) ψ] with x hx
      rw [hx]; rfl
    rw [e1, e2]
    have iprod : Integrable (fun x => k x * ((F n : E → ℝ) x - (ψ : E → ℝ) x)) T.μ :=
      ((L1.integrable_coeFn (F n)).sub (L1.integrable_coeFn ψ)).bdd_mul hkm.aestronglyMeasurable hb
    calc |∫ x, k x * ((F n : E → ℝ) x - (ψ : E → ℝ) x) ∂T.μ|
        ≤ ∫ x, |k x * ((F n : E → ℝ) x - (ψ : E → ℝ) x)| ∂T.μ := abs_integral_le_integral_abs
      _ ≤ ∫ x, |M| * |(F n : E → ℝ) x - (ψ : E → ℝ) x| ∂T.μ := by
          refine integral_mono iprod.abs (iD.const_mul _) (fun x => ?_)
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right ((hk x).trans (le_abs_self M)) (abs_nonneg _)
      _ = |M| * ∫ x, |(F n : E → ℝ) x - (ψ : E → ℝ) x| ∂T.μ := integral_const_mul _ _
  refine squeeze_zero (fun n => dist_nonneg) key ?_
  simpa using h.const_mul |M|

lemma inner_cls_eq_int {F : E → ℝ} (hF : F ∈ T.A₀) (a : T.A₀) :
    inner ℝ (T.toDiffusionTriple.cls a)
      ((DiffusionTriple.memLp2 T.toDiffusionTriple hF).toLp F) = ∫ x, a.1 x * F x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple a,
    (DiffusionTriple.memLp2 T.toDiffusionTriple hF).coeFn_toLp] with x h1 h2
  rw [h1, h2]

/-- **BGL Prop. 3.3.17 (Hessian, `g, h ∈ 𝒜₀`)**: for `f ∈ 𝒜 ∩ 𝒟(L)`, the extended Hessian of Prop. 3.3.16 (iv)
equals the `𝒜`-Hessian `Hess f g h` a.e. -/
theorem hessE_eq_Hess {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A)
    (hf2 : MemLp f 2 T.μ) (hu : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain) (g h : T.A₀) :
    (hessE hCD (hf2.toLp f) hu (T.toDiffusionTriple.clsQ g) h : E → ℝ) =ᵐ[T.μ] Hess T f g.1 h.1 := by
  obtain ⟨a, ha⟩ := exists_graphConv (hf2.toLp f) hu
  have hT := hessE_tendsto hCD h ha (formConv_const g)
  have hHm : Hess T f g.1 h.1 ∈ T.A₀ := Hess_memA₀ hf (A₀_memA g.2) h.2
  have iHess : Integrable (Hess T f g.1 h.1) T.μ := intA₀ hHm
  have key : ∀ k : T.A₀, ∫ x, k.1 x * (hessE hCD (hf2.toLp f) hu (T.toDiffusionTriple.clsQ g) h : E → ℝ) x ∂T.μ =
      ∫ x, k.1 x * Hess T f g.1 h.1 x ∂T.μ := by
    intro k
    obtain ⟨C, hC⟩ := T.bounded k.1 k.2
    have hkm := T.measurable k.1 k.2
    have t1 := tendsto_int_mul_L1 hkm hC hT
    have hE3 := E3_memA₀ g.2 h.2 k.2
    set e3 : Lp ℝ 2 T.μ := (DiffusionTriple.memLp2 T.toDiffusionTriple hE3).toLp (E3 T g.1 h.1 k.1) with he3
    have en : ∀ m, ∫ x, k.1 x * (HH T (a m) g h : E → ℝ) x ∂T.μ =
        (1 / 2 : ℝ) * inner ℝ (T.toDiffusionTriple.cls (a m)) e3 := by
      intro m
      rw [inner_cls_eq_int hE3 (a m), ← int_mul_Hess (A₀_memA (a m).2) g.2 h.2 k.2]
      refine integral_congr_ae ?_
      filter_upwards [HH_ae (a m) g h] with x hx
      rw [hx]
    have t2 : Tendsto (fun m => (1 / 2 : ℝ) * inner ℝ (T.toDiffusionTriple.cls (a m)) e3) atTop
        (𝓝 ((1 / 2 : ℝ) * inner ℝ (hf2.toLp f) e3)) :=
      ((GraphConv.cls ha).inner tendsto_const_nhds).const_mul _
    have hlim := tendsto_nhds_unique (t1.congr (fun m => en m)) t2
    rw [hlim]
    have e4 : inner ℝ (hf2.toLp f) e3 = ∫ x, f x * E3 T g.1 h.1 k.1 x ∂T.μ := by
      rw [L2_inner_eq]
      refine integral_congr_ae ?_
      filter_upwards [hf2.coeFn_toLp, (DiffusionTriple.memLp2 T.toDiffusionTriple hE3).coeFn_toLp]
        with x h1 h2
      rw [h1, h2]
    rw [e4, int_mul_Hess hf g.2 h.2 k.2]
  have iφ : Integrable (fun x => (hessE hCD (hf2.toLp f) hu (T.toDiffusionTriple.clsQ g) h : E → ℝ) x -
      Hess T f g.1 h.1 x) T.μ := (L1.integrable_coeFn _).sub iHess
  have hz := ae_zero_of_forall_integral_A₀ iφ (fun k => by
    obtain ⟨C, hC⟩ := T.bounded k.1 k.2
    have hkm := T.measurable k.1 k.2
    have hb : ∀ᵐ x ∂T.μ, ‖k.1 x‖ ≤ C := Eventually.of_forall fun x => by simpa using hC x
    have i1 : Integrable (fun x => k.1 x * (hessE hCD (hf2.toLp f) hu (T.toDiffusionTriple.clsQ g) h : E → ℝ) x) T.μ :=
      (L1.integrable_coeFn _).bdd_mul hkm.aestronglyMeasurable hb
    have i2 : Integrable (fun x => k.1 x * Hess T f g.1 h.1 x) T.μ := intA₀ (mulA₀' k.2 hHm)
    have : (fun x => k.1 x * ((hessE hCD (hf2.toLp f) hu (T.toDiffusionTriple.clsQ g) h : E → ℝ) x -
        Hess T f g.1 h.1 x)) = fun x => k.1 x * (hessE hCD (hf2.toLp f) hu (T.toDiffusionTriple.clsQ g) h : E → ℝ) x -
          k.1 x * Hess T f g.1 h.1 x := by funext x; ring
    rw [this, integral_sub i1 i2, key k, sub_self])
  filter_upwards [hz] with x hx
  simp only [Pi.zero_apply] at hx
  linarith

/-- **BGL Prop. 3.3.17 (Hessian, `g ∈ 𝒜 ∩ 𝒟(ℰ)`, `h ∈ 𝒜₀`)**: for `f ∈ 𝒜 ∩ 𝒟(L)` the extended Hessian equals the
`𝒜`-Hessian `Hess f g h` a.e. -/
theorem hessE_eq_Hess' {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A)
    (hf2 : MemLp f 2 T.μ) (hu : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain)
    {g : E → ℝ} (hg : g ∈ T.A) (hg2 : MemLp g 2 T.μ) (hQg : hg2.toLp g ∈ T.formDomain) (h : T.A₀) :
    (hessE hCD (hf2.toLp f) hu ⟨hg2.toLp g, hQg⟩ h : E → ℝ) =ᵐ[T.μ] Hess T f g h.1 := by
  refine ae_eq_of_mul_A₀ (fun k => ?_)
  have hk := A₀_memA k.2
  have e1 := hessE_mulE hCD (hf2.toLp f) hu k h (⟨hg2.toLp g, hQg⟩ : T.formDomain)
  have hm := mulE_eq_clsQ k hg hg2 hQg
  rw [hm] at e1
  have s1 := hessE_eq_Hess hCD hf hf2 hu ⟨k.1 * g, T.ideal g hg k.1 k.2⟩ h
  have s2 := hessE_eq_Hess hCD hf hf2 hu k h
  have s3 := Hess_mul_mid hf hg hk (A₀_memA h.2)
  have e6 := hg2.coeFn_toLp
  filter_upwards [e1, s1, s2, s3, e6] with x h1 h2 h3 h4 h6
  have h6' : (((⟨hg2.toLp g, hQg⟩ : T.formDomain) : Lp ℝ 2 T.μ) : E → ℝ) x = g x := h6
  rw [h2, h3, h6'] at h1
  show k.1 x * (hessE hCD (hf2.toLp f) hu ⟨hg2.toLp g, hQg⟩ h : E → ℝ) x = k.1 x * Hess T f g h.1 x
  have h4' : Hess T f (k.1 * g) h.1 x = k.1 x * Hess T f g h.1 x + g x * Hess T f k.1 h.1 x := h4
  linarith

/-- **BGL Prop. 3.3.17, integrability of `Γ(f)`** (second paragraph): for `f ∈ 𝒜 ∩ 𝒟(L)`, `Γ_𝒜(f) ∈ L¹` and
`∫ Γ_𝒜(f) = −⟪L f, f⟫`.  (The statement `Γ₂(f) ∈ L¹`, `∫Γ₂(f) = ∫ (Lf)²` needs the identification of `Γ₂`, see
`STATEMENTS_R14.md`.) -/
theorem integrable_ΓA_of_domain {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hu : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain) :
    Integrable (G T f f) T.μ ∧ ∫ x, G T f f x ∂T.μ =
      -inner ℝ (T.toDiffusionTriple.generator ⟨hf2.toLp f, hu⟩) (hf2.toLp f) := by
  obtain ⟨hQ, hform⟩ := (DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form hu
  have h1 := gammaE_self_eq_ΓA hf hf2 hQ
  refine ⟨(L1.integrable_coeFn _).congr h1, ?_⟩
  rw [← integral_congr_ae h1, gammaE_integral]
  exact hform ⟨_, hQ⟩

end FullTriple

end MarkovTriple.BGL
