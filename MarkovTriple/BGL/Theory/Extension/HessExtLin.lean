import Mathlib
import MarkovTriple.BGL.Theory.Extension.HessExt2
import MarkovTriple.BGL.Theory.Extension.SeqLin

/-!
# Prop. 3.3.16 (iv), (v) (BGL p. 160): `H` is a bounded bilinear operator on `𝒟(L) × 𝒟(ℰ) × 𝒜₀`; continuity statements

Round 15 gap closure.  Statements fixed in `Extension/STATEMENTS_R15_Gaps.md` (1), (2):
linearity of `hessE` in each of the three slots (`hessE_lin_left/mid/right`), the estimate
`‖H(f)(g,h)‖₁ ≤ C_h ‖(f,Lf)‖ ‖g‖_{𝒟(ℰ)}` (`hessE_bound`), the identification with the `𝒜₀`-level class
(`hessE_cls`), and the second and third statements of (v) (`hessE_tendsto_left`, `hessE_tendsto_mid`).
As in the book, the proofs are: linearity and the bound on the dense class `𝒜₀` (`HH`, (3.3.7)), then passage to the limit.
`Classical.choose` enters only through `hessE_tendsto` (the specification of `hessE`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma coe_lin (a a' : T.A₀) (c : ℝ) : ((a + c • a' : T.A₀) : E → ℝ) = fun x => a.1 x + c * a'.1 x := rfl

lemma HH_lin_left (a a' b h : T.A₀) (c : ℝ) :
    HH T (a + c • a') b h = HH T a b h + c • HH T a' b h := by
  refine Lp.ext ?_
  filter_upwards [HH_ae (a + c • a') b h, HH_ae a b h, HH_ae a' b h,
    Lp.coeFn_add (HH T a b h) (c • HH T a' b h), Lp.coeFn_smul c (HH T a' b h),
    Hess_lin_left (A₀_memA a.2) (A₀_memA a'.2) (A₀_memA b.2) (A₀_memA h.2) c] with x e1 e2 e3 e4 e5 e6
  rw [e4, Pi.add_apply, e5, Pi.smul_apply, e1, e2, e3, coe_lin, e6]
  rfl

lemma HH_lin_mid (a b b' h : T.A₀) (c : ℝ) :
    HH T a (b + c • b') h = HH T a b h + c • HH T a b' h := by
  refine Lp.ext ?_
  filter_upwards [HH_ae a (b + c • b') h, HH_ae a b h, HH_ae a b' h,
    Lp.coeFn_add (HH T a b h) (c • HH T a b' h), Lp.coeFn_smul c (HH T a b' h),
    Hess_lin_mid (A₀_memA a.2) (A₀_memA b.2) (A₀_memA b'.2) (A₀_memA h.2) c] with x e1 e2 e3 e4 e5 e6
  rw [e4, Pi.add_apply, e5, Pi.smul_apply, e1, e2, e3, coe_lin, e6]
  rfl

lemma HH_lin_right (a b h h' : T.A₀) (c : ℝ) :
    HH T a b (h + c • h') = HH T a b h + c • HH T a b h' := by
  refine Lp.ext ?_
  filter_upwards [HH_ae a b (h + c • h'), HH_ae a b h, HH_ae a b h',
    Lp.coeFn_add (HH T a b h) (c • HH T a b h'), Lp.coeFn_smul c (HH T a b h'),
    Hess_lin_right (A₀_memA a.2) (A₀_memA b.2) (A₀_memA h.2) (A₀_memA h'.2) c] with x e1 e2 e3 e4 e5 e6
  rw [e4, Pi.add_apply, e5, Pi.smul_apply, e1, e2, e3, coe_lin, e6]
  rfl

/-- **Linearity of `H(f)(g,h)` in `f ∈ 𝒟(L)`** (BGL Prop. 3.3.16 (iv)). -/
theorem hessE_lin_left {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u u' w : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (hu' : u' ∈ T.toDiffusionTriple.generator.domain)
    (hw : w ∈ T.toDiffusionTriple.generator.domain) (c : ℝ) (hwe : w = u + c • u')
    (g : T.formDomain) (h : T.A₀) :
    hessE hCD w hw g h = hessE hCD u hu g h + c • hessE hCD u' hu' g h := by
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨a', ha'⟩ := exists_graphConv u' hu'
  obtain ⟨b, hb⟩ := exists_formConv g
  have t1 := hessE_tendsto hCD (hu := hw) h (ha.lin (hw := hw) c hwe ha') hb
  have t2 := (hessE_tendsto hCD h ha hb).add ((hessE_tendsto hCD h ha' hb).const_smul c)
  exact tendsto_nhds_unique t1 (t2.congr (fun k => (HH_lin_left (a k) (a' k) (b k) h c).symm))

/-- **Linearity of `H(f)(g,h)` in `g ∈ 𝒟(ℰ)`** (BGL Prop. 3.3.16 (iv)). -/
theorem hessE_lin_mid {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) {g g' w : T.formDomain} (c : ℝ)
    (hwe : w = g + c • g') (h : T.A₀) :
    hessE hCD u hu w h = hessE hCD u hu g h + c • hessE hCD u hu g' h := by
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨b, hb⟩ := exists_formConv g
  obtain ⟨b', hb'⟩ := exists_formConv g'
  have t1 := hessE_tendsto hCD h ha (hb.lin c hwe hb')
  have t2 := (hessE_tendsto hCD h ha hb).add ((hessE_tendsto hCD h ha hb').const_smul c)
  exact tendsto_nhds_unique t1 (t2.congr (fun k => (HH_lin_mid (a k) (b k) (b' k) h c).symm))

/-- **Linearity of `H(f)(g,h)` in `h ∈ 𝒜₀`** (BGL Prop. 3.3.16 (iv)). -/
theorem hessE_lin_right {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (g : T.formDomain) {h h' h'' : T.A₀} (c : ℝ)
    (hwe : h'' = h + c • h') :
    hessE hCD u hu g h'' = hessE hCD u hu g h + c • hessE hCD u hu g h' := by
  subst hwe
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨b, hb⟩ := exists_formConv g
  have t1 := hessE_tendsto hCD (h + c • h') ha hb
  have t2 := (hessE_tendsto hCD h ha hb).add ((hessE_tendsto hCD h' ha hb).const_smul c)
  exact tendsto_nhds_unique t1 (t2.congr (fun k => (HH_lin_right (a k) (b k) h h' c).symm))

/-- **Boundedness of `H`** (BGL Prop. 3.3.16 (iv)): `‖H(f)(g,h)‖₁ ≤ C_h ‖(f,Lf)‖ ‖g‖_{𝒟(ℰ)}`. -/
theorem hessE_bound {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (h : T.A₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Lp ℝ 2 T.μ) (hu : u ∈ T.toDiffusionTriple.generator.domain)
      (g : T.formDomain),
      ‖hessE hCD u hu g h‖ ≤ C * ‖(u, T.toDiffusionTriple.generator ⟨u, hu⟩)‖ *
        ‖(DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm g‖ := by
  obtain ⟨C, hC0, hC⟩ := HH_bound hCD h
  refine ⟨C, hC0, fun u hu g => ?_⟩
  obtain ⟨a, ha⟩ := exists_graphConv u hu
  obtain ⟨b, hb⟩ := exists_formConv g
  have t1 := (hessE_tendsto hCD h ha hb).norm
  have t2 : Tendsto (fun k => C * ‖jL T (a k)‖ * ‖jE T (b k)‖) atTop
      (𝓝 (C * ‖(u, T.toDiffusionTriple.generator ⟨u, hu⟩)‖ *
        ‖(DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm g‖)) :=
    ((ha.norm).const_mul C).mul hb.norm
  exact le_of_tendsto_of_tendsto' t1 t2 (fun k => hC (a k) (b k))

/-- **Identification on `𝒜₀`** (BGL Prop. 3.3.16 (iv): the extension agrees with `H` on `𝒜₀ × 𝒜₀ × 𝒜₀`). -/
theorem hessE_cls {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (a b h : T.A₀) :
    hessE hCD (T.toDiffusionTriple.cls a) (T.toDiffusionTriple.cls_mem_generator_domain a)
      (T.toDiffusionTriple.clsQ b) h = HH T a b h := by
  have hg : GraphConv T (fun _ => a) (T.toDiffusionTriple.cls a)
      (T.toDiffusionTriple.cls_mem_generator_domain a) := by
    unfold GraphConv
    rw [DiffusionTriple.generator_cls T.toDiffusionTriple a (T.toDiffusionTriple.cls_mem_generator_domain a)]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique (hessE_tendsto hCD h hg (formConv_const b)) tendsto_const_nhds

/-- the same, a.e. as functions: `H(a)(b,h)` is the pointwise `Hess`. -/
theorem hessE_cls_ae {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (a b h : T.A₀) :
    (hessE hCD (T.toDiffusionTriple.cls a) (T.toDiffusionTriple.cls_mem_generator_domain a)
      (T.toDiffusionTriple.clsQ b) h : E → ℝ) =ᵐ[T.μ] Hess T a.1 b.1 h.1 := by
  rw [hessE_cls hCD a b h]; exact HH_ae a b h

/-- **BGL Prop. 3.3.16 (v), second statement**: if `f_ℓ → f` in `𝒟(L)` (graph norm), `g ∈ 𝒟(ℰ)` and `h ∈ 𝒜₀`
are fixed, then `H(f_ℓ)(g,h) → H(f)(g,h)` in `L¹`. -/
theorem hessE_tendsto_left {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {ι : Type*} {l : Filter ι}
    (f : ι → T.toDiffusionTriple.generator.domain) (f₀ : T.toDiffusionTriple.generator.domain)
    (hf : Tendsto (fun i => (((f i : Lp ℝ 2 T.μ)), T.toDiffusionTriple.generator (f i))) l
      (𝓝 ((f₀ : Lp ℝ 2 T.μ), T.toDiffusionTriple.generator f₀)))
    (g : T.formDomain) (h : T.A₀) :
    Tendsto (fun i => hessE hCD (f i : Lp ℝ 2 T.μ) (f i).2 g h) l
      (𝓝 (hessE hCD (f₀ : Lp ℝ 2 T.μ) f₀.2 g h)) := by
  obtain ⟨C, hC0, hC⟩ := hessE_bound hCD h
  set N := ‖(DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm g‖
  have hd : Tendsto (fun i => ‖((f i : Lp ℝ 2 T.μ), T.toDiffusionTriple.generator (f i)) -
      ((f₀ : Lp ℝ 2 T.μ), T.toDiffusionTriple.generator f₀)‖) l (𝓝 0) := by
    have := (hf.sub_const ((f₀ : Lp ℝ 2 T.μ), T.toDiffusionTriple.generator f₀)).norm
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) (by have := hd.const_mul (C * N); rwa [mul_zero] at this)
  have e := hessE_lin_left hCD (u := (f₀ : Lp ℝ 2 T.μ)) (u' := ((f i - f₀ : T.toDiffusionTriple.generator.domain) : Lp ℝ 2 T.μ))
    f₀.2 (f i - f₀).2 (f i).2 1 (by simp) g h
  have e2 : hessE hCD (f i : Lp ℝ 2 T.μ) (f i).2 g h - hessE hCD (f₀ : Lp ℝ 2 T.μ) f₀.2 g h =
      hessE hCD ((f i - f₀ : T.toDiffusionTriple.generator.domain) : Lp ℝ 2 T.μ) (f i - f₀).2 g h := by
    rw [e]; simp
  rw [e2]
  refine (hC _ (f i - f₀).2 g).trans ?_
  have e3 : ((((f i - f₀ : T.toDiffusionTriple.generator.domain) : Lp ℝ 2 T.μ)),
      T.toDiffusionTriple.generator (f i - f₀)) =
      ((f i : Lp ℝ 2 T.μ), T.toDiffusionTriple.generator (f i)) -
        ((f₀ : Lp ℝ 2 T.μ), T.toDiffusionTriple.generator f₀) := by
    rw [LinearPMap.map_sub]; rfl
  rw [e3]
  exact le_of_eq (by ring)

/-- **BGL Prop. 3.3.16 (v), third statement**: if `f ∈ 𝒟(L)` and `h ∈ 𝒜₀` are fixed and `g_ℓ → g` in `𝒟(ℰ)`
(i.e. in the Hilbert space `KE`), then `H(f)(g_ℓ,h) → H(f)(g,h)` in `L¹`. -/
theorem hessE_tendsto_mid {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u : Lp ℝ 2 T.μ}
    (hu : u ∈ T.toDiffusionTriple.generator.domain) {ι : Type*} {l : Filter ι}
    (g : ι → T.formDomain) (g₀ : T.formDomain)
    (hg : Tendsto (fun i => (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm (g i)) l
      (𝓝 ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm g₀))) (h : T.A₀) :
    Tendsto (fun i => hessE hCD u hu (g i) h) l (𝓝 (hessE hCD u hu g₀ h)) := by
  obtain ⟨C, hC0, hC⟩ := hessE_bound hCD h
  set N := ‖(u, T.toDiffusionTriple.generator ⟨u, hu⟩)‖
  have hd : Tendsto (fun i => ‖(DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm (g i) -
      (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm g₀‖) l (𝓝 0) := by
    have := (hg.sub_const ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm g₀)).norm
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun i => norm_nonneg _) (fun i => ?_) (by have := hd.const_mul (C * N); rwa [mul_zero] at this)
  have e := hessE_lin_mid hCD hu (g := g₀) (g' := g i - g₀) (w := g i) 1 (by simp) h
  have e2 : hessE hCD u hu (g i) h - hessE hCD u hu g₀ h = hessE hCD u hu (g i - g₀) h := by
    rw [e]; simp
  rw [e2]
  refine (hC u hu _).trans ?_
  erw [map_sub]

end FullTriple

end MarkovTriple.BGL
