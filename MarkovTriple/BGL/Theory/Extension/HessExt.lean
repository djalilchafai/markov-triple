import Mathlib
import MarkovTriple.BGL.Theory.Extension.HessLin
import MarkovTriple.BGL.Theory.Extension.ClosedDetect

/-!
# Prop. 3.3.16 (iv), (v) (BGL p. 160): the Hessian `H(f)(g,h)` on `𝒟(L) × 𝒟(ℰ) × 𝒜₀`

Hypotheses: ESA (F10) and `CD(ρ,n)` (the book's `CD(ρ,∞)`; the inequality (3.3.7) holds for every `n ≥ 1`).

* `jL a = ([a], [La]) ∈ L² × L²` (the graph embedding) and `GraphConv a u hu`: `a_k → u` in `𝒟(L)` for the graph norm,
  as in the book's statement (iii)–(v) "`(f_ℓ) ⊂ 𝒜₀` converging to `f ∈ 𝒟(L)`" (`𝒟(L)` carries the graph norm).
* `HH a b h ∈ L¹`: the class of `H(a)(b,h)`, `a,b,h ∈ 𝒜₀`.  Bilinear and bounded:
  `‖HH a b h‖₁ ≤ C_h ‖jL a‖ ‖jE b‖` (by (3.3.7) and Cauchy–Schwarz).
* `hessE hCD u hu g h ∈ L¹`: **the extension of `H` to `𝒟(L) × 𝒟(ℰ) × 𝒜₀`**; `hessE_tendsto`: it is the `L¹`-limit of
  `H(a_k)(b_k)(h)` along any graph-convergent `a_k → u` and form-convergent `b_k → g` (this is (iv) and the `L¹`
  statements of (v), simultaneously in `f` and `g`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- the graph embedding `a ↦ ([a], [L a])`. -/
noncomputable def jL (T : FullTriple E) : T.A₀ →+ Lp ℝ 2 T.μ × Lp ℝ 2 T.μ :=
  ((DiffusionTriple.clsₗ T.toDiffusionTriple).prod (DiffusionTriple.Lclsₗ T.toDiffusionTriple)).toAddMonoidHom

lemma jL_apply (a : T.A₀) :
    jL T a = (T.toDiffusionTriple.cls a, T.toDiffusionTriple.Lcls a) := rfl

lemma graphSq_le (a : T.A₀) : graphSq T a ≤ 2 * ‖jL T a‖ ^ 2 := by
  unfold graphSq
  have h1 : ‖T.toDiffusionTriple.cls a‖ ≤ ‖jL T a‖ := norm_fst_le (jL T a)
  have h2 : ‖T.toDiffusionTriple.Lcls a‖ ≤ ‖jL T a‖ := norm_snd_le (jL T a)
  nlinarith [norm_nonneg (T.toDiffusionTriple.cls a), norm_nonneg (T.toDiffusionTriple.Lcls a)]

/-- `a_k → u` in `𝒟(L)` (graph norm): `[a_k] → u`, `[L a_k] → L u` in `L²` (cf. F10). -/
def GraphConv (T : FullTriple E) (a : ℕ → T.A₀) (u : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) : Prop :=
  Tendsto (fun k => jL T (a k)) atTop (𝓝 (u, T.toDiffusionTriple.generator ⟨u, hu⟩))

lemma exists_graphConv (u : Lp ℝ 2 T.μ) (hu : u ∈ T.toDiffusionTriple.generator.domain) :
    ∃ a : ℕ → T.A₀, GraphConv T a u hu := by
  obtain ⟨a, h1, h2⟩ := T.esa u hu
  exact ⟨a, h1.prodMk_nhds h2⟩

lemma GraphConv.cls {a : ℕ → T.A₀} {u : Lp ℝ 2 T.μ} {hu : u ∈ T.toDiffusionTriple.generator.domain}
    (h : GraphConv T a u hu) :
    Tendsto (fun k => T.toDiffusionTriple.cls (a k)) atTop (𝓝 u) := (Tendsto.fst_nhds h :)

lemma GraphConv.Lcls {a : ℕ → T.A₀} {u : Lp ℝ 2 T.μ} {hu : u ∈ T.toDiffusionTriple.generator.domain}
    (h : GraphConv T a u hu) :
    Tendsto (fun k => T.toDiffusionTriple.Lcls (a k)) atTop
      (𝓝 (T.toDiffusionTriple.generator ⟨u, hu⟩)) := (Tendsto.snd_nhds h :)

/-- the `L¹`-class of `H(a)(b,h)`, `a, b, h ∈ 𝒜₀`. -/
noncomputable def HH (T : FullTriple E) (a b h : T.A₀) : Lp ℝ 1 T.μ :=
  (integrable_A₀ (Hess_memA₀ (A₀_memA a.2) (A₀_memA b.2) h.2)).toL1 (Hess T a.1 b.1 h.1)

lemma HH_ae (a b h : T.A₀) : (HH T a b h : E → ℝ) =ᵐ[T.μ] Hess T a.1 b.1 h.1 :=
  Integrable.coeFn_toL1 _

lemma HH_sub_left (a a' b h : T.A₀) : HH T (a - a') b h = HH T a b h - HH T a' b h := by
  refine Lp.ext ?_
  filter_upwards [HH_ae (a - a') b h, HH_ae a b h, HH_ae a' b h,
    Lp.coeFn_sub (HH T a b h) (HH T a' b h),
    Hess_lin_left (A₀_memA a.2) (A₀_memA a'.2) (A₀_memA b.2) (A₀_memA h.2) (-1)] with x e1 e2 e3 e4 e5
  rw [e4, Pi.sub_apply, e1, e2, e3, coe_sub']
  rw [e5]; ring

lemma HH_sub_right (a b b' h : T.A₀) : HH T a (b - b') h = HH T a b h - HH T a b' h := by
  refine Lp.ext ?_
  filter_upwards [HH_ae a (b - b') h, HH_ae a b h, HH_ae a b' h,
    Lp.coeFn_sub (HH T a b h) (HH T a b' h),
    Hess_lin_mid (A₀_memA a.2) (A₀_memA b.2) (A₀_memA b'.2) (A₀_memA h.2) (-1)] with x e1 e2 e3 e4 e5
  rw [e4, Pi.sub_apply, e1, e2, e3, coe_sub']
  rw [e5]; ring

lemma norm_HH (a b h : T.A₀) : ‖HH T a b h‖ = ∫ x, |Hess T a.1 b.1 h.1 x| ∂T.μ := by
  rw [L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [HH_ae a b h] with x hx
  rw [hx]; rfl

/-- **Boundedness of `H` for the graph × form norms** (consequence of (3.3.7)). -/
lemma HH_bound {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (h : T.A₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : T.A₀, ‖HH T a b h‖ ≤ C * ‖jL T a‖ * ‖jE T b‖ := by
  obtain ⟨B, hB⟩ := T.bounded (G T h.1 h.1) (T.ΓA_self_mem_A₀ h.2)
  set B' := |B| with hB'
  have hGB : ∀ x, G T h.1 h.1 x ≤ B' := fun x => (le_abs_self _).trans ((hB x).trans (le_abs_self B))
  refine ⟨√(2 * (1 + |ρ|)) * √B', by positivity, fun a b => ?_⟩
  have hHm := Hess_memA₀ (T := T) (A₀_memA a.2) (A₀_memA b.2) h.2
  have iK := integrable_A₀ (Kf_memA₀ (T := T) ρ a.2)
  have iG := integrable_G b b
  have hK0 := Kf_nonneg hCD a.1 (A₀_memA a.2)
  have hb0 := T.ΓA_nonneg _ (A₀_memA b.2)
  have hineq := hessian_general_ineq hCD (A₀_memA a.2) (A₀_memA b.2) (A₀_memA h.2)
  have hpt : ∀ᵐ x ∂T.μ, (Hess T a.1 b.1 h.1 x) ^ 2 ≤ Kf T ρ a.1 a.1 x * (B' * G T b.1 b.1 x) := by
    filter_upwards [hineq, hK0, hb0] with x h1 h2 h3
    simp only [Pi.zero_apply] at h2 h3
    refine h1.trans ?_
    have : G T b.1 b.1 x * G T h.1 h.1 x ≤ B' * G T b.1 b.1 x := by
      nlinarith [mul_le_mul_of_nonneg_left (hGB x) h3]
    exact mul_le_mul_of_nonneg_left this h2
  have key := int_abs_le_sqrt iK (iG.const_mul B') (integrable_A₀ hHm).1 hK0
    (by filter_upwards [hb0] with x hx; exact mul_nonneg (abs_nonneg _) hx) hpt
  rw [norm_HH]
  refine key.2.trans ?_
  have e1 : ∫ x, Kf T ρ a.1 a.1 x ∂T.μ ≤ 2 * (1 + |ρ|) * ‖jL T a‖ ^ 2 := by
    refine (eK_le ρ a).trans ?_
    have := graphSq_le a
    nlinarith [abs_nonneg ρ]
  have e2 : ∫ x, B' * G T b.1 b.1 x ∂T.μ ≤ B' * ‖jE T b‖ ^ 2 := by
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (int_G_le_norm_jE b) (abs_nonneg _)
  have s1 : √(∫ x, Kf T ρ a.1 a.1 x ∂T.μ) ≤ √(2 * (1 + |ρ|)) * ‖jL T a‖ := by
    calc √(∫ x, Kf T ρ a.1 a.1 x ∂T.μ) ≤ √(2 * (1 + |ρ|) * ‖jL T a‖ ^ 2) := Real.sqrt_le_sqrt e1
      _ = √(2 * (1 + |ρ|)) * ‖jL T a‖ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have s2 : √(∫ x, B' * G T b.1 b.1 x ∂T.μ) ≤ √B' * ‖jE T b‖ := by
    calc √(∫ x, B' * G T b.1 b.1 x ∂T.μ) ≤ √(B' * ‖jE T b‖ ^ 2) := Real.sqrt_le_sqrt e2
      _ = √B' * ‖jE T b‖ := by
          rw [Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)]
  calc √(∫ x, Kf T ρ a.1 a.1 x ∂T.μ) * √(∫ x, B' * G T b.1 b.1 x ∂T.μ)
      ≤ (√(2 * (1 + |ρ|)) * ‖jL T a‖) * (√B' * ‖jE T b‖) :=
        mul_le_mul s1 s2 (Real.sqrt_nonneg _) (by positivity)
    _ = √(2 * (1 + |ρ|)) * √B' * ‖jL T a‖ * ‖jE T b‖ := by ring

/-- **BGL Prop. 3.3.16 (iv), (v) (existence)**: for `f ∈ 𝒟(L)`, `g ∈ 𝒟(ℰ)`, `h ∈ 𝒜₀`, the `L¹`-limit of
`H(a_k)(b_k)(h)` exists for graph-convergent `a_k → f` and form-convergent `b_k → g`, and does not depend on the
sequences. -/
theorem hessE_exists {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (g : T.formDomain) (h : T.A₀) :
    ∃ γ : Lp ℝ 1 T.μ, ∀ (a b : ℕ → T.A₀), GraphConv T a u hu → FormConv T b g →
      Tendsto (fun k => HH T (a k) (b k) h) atTop (𝓝 γ) := by
  obtain ⟨C, hC0, hC⟩ := HH_bound hCD h
  obtain ⟨a0, ha0⟩ := exists_graphConv u hu
  obtain ⟨b0, hb0⟩ := exists_formConv g
  exact bil_spec (jL T) (jE T) (fun a b => HH T a b h) hC0 (fun x x' y => HH_sub_left x x' y h)
    (fun x y y' => HH_sub_right x y y' h) hC ⟨a0, b0, ha0, hb0⟩

/-- **The extended Hessian** `H(f)(g,h)`, `f ∈ 𝒟(L)`, `g ∈ 𝒟(ℰ)`, `h ∈ 𝒜₀` (BGL Prop. 3.3.16 (iv)). -/
noncomputable def hessE {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (g : T.formDomain) (h : T.A₀) : Lp ℝ 1 T.μ :=
  Classical.choose (hessE_exists hCD u hu g h)

/-- **BGL Prop. 3.3.16 (v)**: `H(a_k)(b_k)(h) → H(f)(g,h)` in `L¹` (for `g ∈ 𝒜₀` this is the `L¹` form of the
first statement of (v); `b_k = const` gives the dependence on `f` only, `a_k = const` the dependence on `g` only
in the third statement, when `f ∈ 𝒜₀`). -/
theorem hessE_tendsto {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u : Lp ℝ 2 T.μ}
    {hu : u ∈ T.toDiffusionTriple.generator.domain} {g : T.formDomain} (h : T.A₀)
    {a b : ℕ → T.A₀} (ha : GraphConv T a u hu) (hb : FormConv T b g) :
    Tendsto (fun k => HH T (a k) (b k) h) atTop (𝓝 (hessE hCD u hu g h)) :=
  Classical.choose_spec (hessE_exists hCD u hu g h) a b ha hb

end FullTriple

end MarkovTriple.BGL
