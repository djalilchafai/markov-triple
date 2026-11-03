import Mathlib
import MarkovTriple.BGL.Theory.Extension.ClosedProd

/-!
# Props 3.3.5 (ii), (iii) and 3.3.6 (BGL pp. 155–156): identification of `Γ` on `𝒜 ∩ 𝒟(ℰ)`, and domains

Hypotheses: `T : FullTriple E` (F1–F10).  `f ∈ 𝒜 ∩ L²` is identified with its class `[f] = hf.toLp f ∈ L²`.
Statements in `Extension/STATEMENTS_R14.md` (S1, S2).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace LinearPMap

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- `ℰ(u,v) = ⟪u,v⟫_K − ⟪u,v⟫_{L²}`. -/
lemma closedForm_eq_inner (u v : T.formDomain) :
    T.toDiffusionTriple.closedForm u v =
      inner ℝ ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u)
        ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm v) -
      inner ℝ (u : Lp ℝ 2 T.μ) (v : Lp ℝ 2 T.μ) := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  show S.E u v = _
  have := Hilbert.FormData.E_eq S (S.qEquiv.symm u) (S.qEquiv.symm v)
  have g1 := S.qEquiv.apply_symm_apply u
  have g2 := S.qEquiv.apply_symm_apply v
  rw [g1, g2] at this
  rw [this]
  have h1 : S.ι (S.qEquiv.symm u) = u := by
    have := Hilbert.FormData.qEquiv_apply S (S.qEquiv.symm u)
    rw [g1] at this
    exact this.symm
  have h2 : S.ι (S.qEquiv.symm v) = v := by
    have := Hilbert.FormData.qEquiv_apply S (S.qEquiv.symm v)
    rw [g2] at this
    exact this.symm
  rw [h1, h2]

/-- `E(clsQ a_n, clsQ b_n) → E(u,v)` along form-convergent sequences. -/
lemma closedForm_tendsto {u v : T.formDomain} {a b : ℕ → T.A₀} (ha : FormConv T a u)
    (hb : FormConv T b v) :
    Tendsto (fun k => T.toDiffusionTriple.closedForm (T.toDiffusionTriple.clsQ (a k))
      (T.toDiffusionTriple.clsQ (b k))) atTop (𝓝 (T.toDiffusionTriple.closedForm u v)) := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  have e1 : ∀ k, T.toDiffusionTriple.closedForm (T.toDiffusionTriple.clsQ (a k))
      (T.toDiffusionTriple.clsQ (b k)) =
      inner ℝ (jE T (a k)) (jE T (b k)) - inner ℝ (T.toDiffusionTriple.cls (a k))
        (T.toDiffusionTriple.cls (b k)) := by
    intro k
    show S.E _ _ = _
    rw [← qEquiv_jE (a k), ← qEquiv_jE (b k), Hilbert.FormData.E_eq, ι_jE, ι_jE]
  have e2 := closedForm_eq_inner u v
  simp only [e1, e2]
  exact (ha.inner hb).sub ((FormConv.cls ha).inner (FormConv.cls hb))

/-- `∫ Γ(u,v) = ℰ(u,v)` on `𝒟(ℰ)`. -/
theorem gammaE_integral (u v : T.formDomain) :
    ∫ x, (gammaE T u v : E → ℝ) x ∂T.μ = T.toDiffusionTriple.closedForm u v := by
  obtain ⟨a, ha⟩ := exists_formConv u
  obtain ⟨b, hb⟩ := exists_formConv v
  have h1 : Tendsto (fun k => ∫ x, (GG T (a k) (b k) : E → ℝ) x ∂T.μ) atTop
      (𝓝 (∫ x, (gammaE T u v : E → ℝ) x ∂T.μ)) :=
    ((MeasureTheory.continuous_integral (μ := T.μ) (G := ℝ)).tendsto _).comp (gammaE_tendsto ha hb)
  have h2 := closedForm_tendsto ha hb
  refine tendsto_nhds_unique h1 (h2.congr (fun k => ?_))
  show _ = _
  rw [DiffusionTriple.closedForm_clsQ, DiffusionTriple.ℰ_eq]
  refine (integral_congr_ae ?_).symm
  filter_upwards [GG_ae (a k) (b k), DiffusionTriple.ΓA_ae_eq T.toDiffusionTriple (a k).2 (b k).2]
    with x h1 h2
  rw [h1]; exact h2

/-- exhaustion: `k φ = k ψ` a.e. for every `k ∈ 𝒜₀` implies `φ = ψ` a.e. (Def. 3.1.1). -/
lemma ae_eq_of_mul_A₀ {φ ψ : E → ℝ}
    (h : ∀ k : T.A₀, (fun x => k.1 x * φ x) =ᵐ[T.μ] fun x => k.1 x * ψ x) : φ =ᵐ[T.μ] ψ := by
  obtain ⟨u, hu1, _, hu3⟩ := T.exhaustion
  have hall := ae_all_iff.2 (fun n => h ⟨u n, hu1 n⟩)
  filter_upwards [hall, hu3] with x hx hlim
  have h1 : Tendsto (fun n => u n x * φ x) atTop (𝓝 (1 * φ x)) := hlim.mul_const _
  have h2 : Tendsto (fun n => u n x * ψ x) atTop (𝓝 (1 * ψ x)) := hlim.mul_const _
  have h3 : Tendsto (fun n => u n x * ψ x) atTop (𝓝 (1 * φ x)) := h1.congr (fun n => hx n)
  simpa using tendsto_nhds_unique h3 h2

/-- the product of `k ∈ 𝒜₀` with `[f]`, `f ∈ 𝒜 ∩ 𝒟(ℰ)`, is the class of the test function `k f`
(ideal property F1). -/
lemma mulE_eq_clsQ (k : T.A₀) {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hQ : hf2.toLp f ∈ T.formDomain) :
    mulE k ⟨hf2.toLp f, hQ⟩ = T.toDiffusionTriple.clsQ ⟨k.1 * f, T.ideal f hf k.1 k.2⟩ := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [mulE_ae k ⟨hf2.toLp f, hQ⟩, hf2.coeFn_toLp,
    DiffusionTriple.coeFn_cls T.toDiffusionTriple ⟨k.1 * f, T.ideal f hf k.1 k.2⟩] with x h1 h2 h3
  rw [h1]
  show k.1 x * ((hf2.toLp f : Lp ℝ 2 T.μ) : E → ℝ) x = ((T.toDiffusionTriple.cls _ : Lp ℝ 2 T.μ) : E → ℝ) x
  rw [h2, h3]; rfl

/-- **BGL Prop. 3.3.5 (ii), first step**: for `f ∈ 𝒜 ∩ 𝒟(ℰ)` and `h ∈ 𝒜₀`, the `𝒟(ℰ)`-extension of `Γ` and
the `𝒜`-definition agree: `Γ_{𝒟(ℰ)}([f],[h]) = Γ_𝒜(f,h)` a.e. -/
theorem gammaE_clsQ_eq {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hQ : hf2.toLp f ∈ T.formDomain) (h : T.A₀) :
    (gammaE T ⟨hf2.toLp f, hQ⟩ (T.toDiffusionTriple.clsQ h) : E → ℝ) =ᵐ[T.μ] G T f h.1 := by
  refine ae_eq_of_mul_A₀ (fun k => ?_)
  have hk := A₀_memA k.2
  have hh := A₀_memA h.2
  have e1 := gammaE_mulE k (T.toDiffusionTriple.clsQ h) (⟨hf2.toLp f, hQ⟩ : T.formDomain)
  have hm := mulE_eq_clsQ k hf hf2 hQ
  have hc1 : gammaE T (T.toDiffusionTriple.clsQ h) (⟨hf2.toLp f, hQ⟩ : T.formDomain) =
      gammaE T (⟨hf2.toLp f, hQ⟩ : T.formDomain) (T.toDiffusionTriple.clsQ h) := gammaE_comm _ _
  have hc2 := gammaE_cls (T := T) h k
  have hc3 := gammaE_cls (T := T) h ⟨k.1 * f, T.ideal f hf k.1 k.2⟩
  rw [hm, hc3, hc1, hc2] at e1
  have e3 := G_mul_left (T := T) hk hf hh
  have e4 : (GG T h ⟨k.1 * f, T.ideal f hf k.1 k.2⟩ : E → ℝ) =ᵐ[T.μ] G T h.1 (k.1 * f) := GG_ae _ _
  have e5 := GG_ae (T := T) h k
  have e6 := hf2.coeFn_toLp
  filter_upwards [e1, e3, e4, e5, e6] with x h1 h3 h4 h5 h6
  have c1 : G T h.1 (k.1 * f) x = G T (k.1 * f) h.1 x := congrFun (G_comm _ _) x
  have c2 : G T h.1 k.1 x = G T k.1 h.1 x := congrFun (G_comm _ _) x
  have h6' : (((⟨hf2.toLp f, hQ⟩ : T.formDomain) : Lp ℝ 2 T.μ) : E → ℝ) x = f x := h6
  rw [h4, c1, h3, h5, c2, h6'] at h1
  show k.1 x * (gammaE T (⟨hf2.toLp f, hQ⟩ : T.formDomain) (T.toDiffusionTriple.clsQ h) : E → ℝ) x =
    k.1 x * G T f h.1 x
  linarith

/-- **BGL Prop. 3.3.5 (ii)** (bilinear form): for `f, g ∈ 𝒜 ∩ 𝒟(ℰ)`, the two definitions of `Γ(f,g)`, in `𝒟(ℰ)`
(`gammaE`, the closure of `Γ` on `𝒜₀`) and in `𝒜` (the formula `ΓA`), coincide a.e. -/
theorem gammaE_eq_ΓA {f g : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hQ : hf2.toLp f ∈ T.formDomain) (hg : g ∈ T.A) (hg2 : MemLp g 2 T.μ)
    (hQg : hg2.toLp g ∈ T.formDomain) :
    (gammaE T ⟨hf2.toLp f, hQ⟩ ⟨hg2.toLp g, hQg⟩ : E → ℝ) =ᵐ[T.μ] G T f g := by
  refine ae_eq_of_mul_A₀ (fun k => ?_)
  have hk := A₀_memA k.2
  have e1 := gammaE_mulE k (⟨hf2.toLp f, hQ⟩ : T.formDomain) (⟨hg2.toLp g, hQg⟩ : T.formDomain)
  have hm := mulE_eq_clsQ k hg hg2 hQg
  rw [hm] at e1
  have s1 := gammaE_clsQ_eq hf hf2 hQ ⟨k.1 * g, T.ideal g hg k.1 k.2⟩
  have s2 := gammaE_clsQ_eq hf hf2 hQ k
  have e3 := G_mul_left (T := T) hk hg hf
  have e6 := hg2.coeFn_toLp
  filter_upwards [e1, s1, s2, e3, e6] with x h1 h2 h3 h4 h6
  have c1 : G T f (k.1 * g) x = G T (k.1 * g) f x := congrFun (G_comm _ _) x
  have c2 : G T g f x = G T f g x := congrFun (G_comm _ _) x
  have c3 : G T k.1 f x = G T f k.1 x := congrFun (G_comm _ _) x
  have h6' : (((⟨hg2.toLp g, hQg⟩ : T.formDomain) : Lp ℝ 2 T.μ) : E → ℝ) x = g x := h6
  rw [h2, c1, h4, h3, h6', c2, c3] at h1
  show k.1 x * (gammaE T (⟨hf2.toLp f, hQ⟩ : T.formDomain) (⟨hg2.toLp g, hQg⟩ : T.formDomain) : E → ℝ) x =
    k.1 x * G T f g x
  linarith

/-- **BGL Prop. 3.3.5 (ii)**: for `f ∈ 𝒜 ∩ 𝒟(ℰ)`, `Γ_{𝒟(ℰ)}(f) = Γ_𝒜(f)` a.e. -/
theorem gammaE_self_eq_ΓA {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hQ : hf2.toLp f ∈ T.formDomain) :
    (gammaE T ⟨hf2.toLp f, hQ⟩ ⟨hf2.toLp f, hQ⟩ : E → ℝ) =ᵐ[T.μ] G T f f :=
  gammaE_eq_ΓA hf hf2 hQ hf hf2 hQ

/-- **`𝒟(L*) = 𝒟(L)` (ESA, F10), operator form.**  If `F, y ∈ L²` satisfy `⟪F, L a⟫ = ⟪y, a⟫` for every
`a ∈ 𝒜₀` (that is `F ∈ 𝒟(L*)`, `L*F = y`, Def. 3.1.9), then `F ∈ 𝒟(L)` and `L F = y`.  This is the step
"`𝒟(L*) = 𝒟(L)` by ESA" of the proofs of Prop. 3.3.6. -/
theorem mem_domain_of_adjoint (F y : Lp ℝ 2 T.μ)
    (hadj : ∀ a : T.A₀, inner ℝ F (T.toDiffusionTriple.Lcls a) =
      inner ℝ y (T.toDiffusionTriple.cls a)) :
    ∃ hF : F ∈ T.toDiffusionTriple.generator.domain,
      T.toDiffusionTriple.generator ⟨F, hF⟩ = y := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  have hR : S.R (F - y) = F := by
    refine ext_inner_right ℝ (fun φ => ?_)
    have hsym : inner ℝ (S.R (F - y)) φ = inner ℝ (F - y) (S.R φ) :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 S.R_isSelfAdjoint (F - y) φ
    rw [hsym]
    obtain ⟨hRφ, hGRφ⟩ := Hilbert.FormData.generator_R S φ
    obtain ⟨a, ha1, ha2⟩ := T.esa (S.R φ) hRφ
    have hG : T.toDiffusionTriple.generator ⟨S.R φ, hRφ⟩ = S.R φ - φ := hGRφ
    rw [hG] at ha2
    have l1 : Tendsto (fun n => inner ℝ (F - y) (T.toDiffusionTriple.cls (a n))) atTop
        (𝓝 (inner ℝ (F - y) (S.R φ))) := tendsto_const_nhds.inner ha1
    have l2 : Tendsto (fun n => inner ℝ F (T.toDiffusionTriple.cls (a n) -
        T.toDiffusionTriple.Lcls (a n))) atTop (𝓝 (inner ℝ F (S.R φ - (S.R φ - φ)))) :=
      tendsto_const_nhds.inner (ha1.sub ha2)
    have e : ∀ n, inner ℝ (F - y) (T.toDiffusionTriple.cls (a n)) =
        inner ℝ F (T.toDiffusionTriple.cls (a n) - T.toDiffusionTriple.Lcls (a n)) := by
      intro n
      rw [inner_sub_left, inner_sub_right, hadj]
    have := tendsto_nhds_unique l1 (l2.congr (fun n => (e n).symm))
    rw [this]
    congr 1; abel
  have hdom : F ∈ S.generator.domain := (S.mem_domain_generator_iff F).2 ⟨y, hR⟩
  exact ⟨hdom, (S.generator_apply_eq_iff hdom y).2 hR⟩

/-- the adjoint relation for `f ∈ 𝒜 ∩ L²` with `L f ∈ L²` (F7). -/
lemma adjoint_of_L2 {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ) (hLf2 : MemLp (T.L f) 2 T.μ)
    (a : T.A₀) : inner ℝ (hf2.toLp f) (T.toDiffusionTriple.Lcls a) =
      inner ℝ (hLf2.toLp (T.L f)) (T.toDiffusionTriple.cls a) := by
  rw [L2_inner_eq, L2_inner_eq]
  have h7 := T.ibp_A f hf a.1 a.2
  have i1 : ∫ x, (hf2.toLp f : E → ℝ) x * (T.toDiffusionTriple.Lcls a : E → ℝ) x ∂T.μ =
      ∫ x, f x * T.L a.1 x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple a] with x h1 h2
    rw [h1, h2]
  have i2 : ∫ x, (hLf2.toLp (T.L f) : E → ℝ) x * (T.toDiffusionTriple.cls a : E → ℝ) x ∂T.μ =
      ∫ x, a.1 x * T.L f x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [hLf2.coeFn_toLp, DiffusionTriple.coeFn_cls T.toDiffusionTriple a] with x h1 h2
    rw [h1, h2]; ring
  rw [i1, i2]
  linarith [h7.1, h7.2]

/-- **BGL Prop. 3.3.6 (i)** (ESA): `f ∈ 𝒜 ∩ L²` with `L f ∈ L²` belongs to `𝒟(L)` and `L[f] = [Lf]`. -/
theorem mem_domain_of_ESA {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hLf2 : MemLp (T.L f) 2 T.μ) :
    ∃ hF : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain,
      T.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ = hLf2.toLp (T.L f) :=
  mem_domain_of_adjoint _ _ (adjoint_of_L2 hf hf2 hLf2)

lemma closedForm_comm (u v : T.formDomain) :
    T.toDiffusionTriple.closedForm u v = T.toDiffusionTriple.closedForm v u := by
  rw [closedForm_eq_inner, closedForm_eq_inner, real_inner_comm, real_inner_comm (u : Lp ℝ 2 T.μ)]

lemma symm_clsQ (a : T.A₀) :
    (DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm (T.toDiffusionTriple.clsQ a) =
      jE T a := by
  rw [← qEquiv_jE]; simp

lemma closedForm_tendsto_left {v : T.formDomain} {a : ℕ → T.A₀} (ha : FormConv T a v)
    (u : T.formDomain) :
    Tendsto (fun k => T.toDiffusionTriple.closedForm (T.toDiffusionTriple.clsQ (a k)) u) atTop
      (𝓝 (T.toDiffusionTriple.closedForm v u)) := by
  have e : ∀ k, T.toDiffusionTriple.closedForm (T.toDiffusionTriple.clsQ (a k)) u =
      inner ℝ (jE T (a k)) ((DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u) -
        inner ℝ (T.toDiffusionTriple.cls (a k)) (u : Lp ℝ 2 T.μ) := by
    intro k
    rw [closedForm_eq_inner, symm_clsQ]; rfl
  simp only [e, closedForm_eq_inner v u]
  exact (ha.inner tendsto_const_nhds).sub ((FormConv.cls ha).inner tendsto_const_nhds)

/-- `ℰ([h],[f]) = −∫ h Lf` for `f ∈ 𝒜 ∩ 𝒟(ℰ)` and `h ∈ 𝒜₀` (Prop. 3.3.5 (ii) + F7). -/
lemma closedForm_clsQ_eq {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hQ : hf2.toLp f ∈ T.formDomain) (h : T.A₀) :
    T.toDiffusionTriple.closedForm (T.toDiffusionTriple.clsQ h) ⟨hf2.toLp f, hQ⟩ =
      -∫ x, h.1 x * T.L f x ∂T.μ := by
  rw [← gammaE_integral, gammaE_comm, (integral_congr_ae (gammaE_clsQ_eq hf hf2 hQ h))]
  exact (T.ibp_A f hf h.1 h.2).1.trans (by rfl)

/-- **BGL Prop. 3.3.5 (iii)**: `f ∈ 𝒜 ∩ 𝒟(ℰ)` with `L f ∈ L²` belongs to `𝒟(L)`, `L[f] = [Lf]`. -/
theorem mem_domain_of_formDomain {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hQ : hf2.toLp f ∈ T.formDomain) (hLf2 : MemLp (T.L f) 2 T.μ) :
    ∃ hF : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain,
      T.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ = hLf2.toLp (T.L f) := by
  refine (DiffusionTriple.generator_iff_form T.toDiffusionTriple _ _).2 ⟨hQ, fun v => ?_⟩
  rw [closedForm_comm]
  obtain ⟨a, ha⟩ := exists_formConv v
  have l1 := closedForm_tendsto_left ha (⟨hf2.toLp f, hQ⟩ : T.formDomain)
  have l2 : Tendsto (fun k => -inner ℝ (hLf2.toLp (T.L f)) (T.toDiffusionTriple.cls (a k))) atTop
      (𝓝 (-inner ℝ (hLf2.toLp (T.L f)) (v : Lp ℝ 2 T.μ))) :=
    (tendsto_const_nhds.inner (FormConv.cls ha)).neg
  have e : ∀ k, T.toDiffusionTriple.closedForm (T.toDiffusionTriple.clsQ (a k))
      (⟨hf2.toLp f, hQ⟩ : T.formDomain) =
      -inner ℝ (hLf2.toLp (T.L f)) (T.toDiffusionTriple.cls (a k)) := by
    intro k
    rw [closedForm_clsQ_eq hf hf2 hQ, L2_inner_eq]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hLf2.coeFn_toLp, DiffusionTriple.coeFn_cls T.toDiffusionTriple (a k)] with x h1 h2
    show _ = ((hLf2.toLp (T.L f) : Lp ℝ 2 T.μ) : E → ℝ) x *
      ((T.toDiffusionTriple.cls (a k) : Lp ℝ 2 T.μ) : E → ℝ) x
    rw [h1, h2]; ring
  exact tendsto_nhds_unique l1 (l2.congr (fun k => (e k).symm))

/-- `jE` as a linear map. -/
noncomputable def jEₗ (T : FullTriple E) : T.A₀ →ₗ[ℝ] KE T where
  toFun := jE T
  map_add' := (jE T).map_add
  map_smul' c a := by
    show ((domElt T (c • a) : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T) =
      c • ((domElt T a : (DiffusionTriple.formData T.toDiffusionTriple).Dom) : KE T)
    have : domElt T (c • a) = c • domElt T a := by
      apply Subtype.ext
      show DiffusionTriple.clsₗ T.toDiffusionTriple (c • a) = c • DiffusionTriple.clsₗ T.toDiffusionTriple a
      simp
    rw [this, UniformSpace.Completion.coe_smul]

lemma denseRange_jE : DenseRange (jEₗ T) := by
  have hs : Function.Surjective (domElt T) := by
    rintro ⟨_, a, rfl⟩
    exact ⟨a, rfl⟩
  exact UniformSpace.Completion.denseRange_coe.comp hs.denseRange (UniformSpace.Completion.continuous_coe _)

/-- **BGL Prop. 3.3.6 (ii)** (ESA): `f ∈ 𝒜 ∩ L²` with `Γ_𝒜(f) ∈ L¹` belongs to `𝒟(ℰ)`.
Deviation (routine, recorded in `STATEMENTS_R14.md`): the Riesz representation of `h ↦ ∫ h Lf` is taken in the
Hilbert space `K` of `𝒟(ℰ)` (form `ℰ + ⟪·,·⟫`), and then `f + g ∈ 𝒟(L*) = 𝒟(L)` as in the book. -/
theorem mem_formDomain_of_ESA {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hΓ : Integrable (G T f f) T.μ) : hf2.toLp f ∈ T.formDomain := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  set F0 : Lp ℝ 2 T.μ := hf2.toLp f with hF0
  let ℓ : T.A₀ →ₗ[ℝ] ℝ := (innerₗ (Lp ℝ 2 T.μ) F0).comp (DiffusionTriple.Lclsₗ T.toDiffusionTriple)
  have hℓ : ∀ a : T.A₀, ℓ a = ∫ x, f x * T.L a.1 x ∂T.μ := by
    intro a
    show inner ℝ F0 (T.toDiffusionTriple.Lcls a) = _
    rw [L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple a] with x h1 h2
    rw [h1, h2]
  have hbd : ∀ a : T.A₀, ‖ℓ a‖ ≤ √(∫ x, G T f f x ∂T.μ) * ‖jEₗ T a‖ := by
    intro a
    have hfa := (T.ibp_A f hf a.1 a.2).2
    have hI := integrable_F7 T hf a.2
    have cs := ExtendedAlgebra.ΓA_cs T.extendedAlgebra hf (A₀_memA a.2)
    have key := int_abs_le_sqrt hΓ (integrable_G a a) hI.1.1 (T.ΓA_nonneg _ hf)
      (T.ΓA_nonneg _ (A₀_memA a.2)) cs
    rw [hℓ, Real.norm_eq_abs]
    have e : ∫ x, f x * T.L a.1 x ∂T.μ = -∫ x, G T f a.1 x ∂T.μ := by linarith [hfa]
    rw [e, abs_neg]
    refine (abs_integral_le_integral_abs).trans (key.2.trans ?_)
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_iff.2 ⟨norm_nonneg _, int_G_le_norm_jE a⟩)
      (Real.sqrt_nonneg _)
  have hdense := denseRange_jE (T := T)
  let ℓ' := ℓ.extendOfNorm (jEₗ T)
  have hℓ' : ∀ a : T.A₀, ℓ' (jEₗ T a) = ℓ a :=
    fun a => LinearMap.extendOfNorm_eq hdense ⟨_, hbd⟩ a
  set g : KE T := (InnerProductSpace.toDual ℝ (KE T)).symm ℓ' with hg
  set g' : T.formDomain := S.qEquiv g with hg'
  have hgg : ∀ a : T.A₀, inner ℝ g (jE T a) = ℓ a := by
    intro a
    rw [hg, InnerProductSpace.toDual_symm_apply]
    exact hℓ' a
  -- the adjoint relation
  have hadj : ∀ a : T.A₀, inner ℝ (F0 + (g' : Lp ℝ 2 T.μ)) (T.toDiffusionTriple.Lcls a) =
      inner ℝ (g' : Lp ℝ 2 T.μ) (T.toDiffusionTriple.cls a) := by
    intro a
    have h1 : inner ℝ F0 (T.toDiffusionTriple.Lcls a) = ℓ a := rfl
    have h2 : inner ℝ g (jE T a) = T.toDiffusionTriple.closedForm g' (T.toDiffusionTriple.clsQ a) +
        inner ℝ (g' : Lp ℝ 2 T.μ) (T.toDiffusionTriple.cls a) := by
      rw [closedForm_eq_inner, hg', LinearEquiv.symm_apply_apply, symm_clsQ]
      show _ = inner ℝ g (jE T a) - inner ℝ (g' : Lp ℝ 2 T.μ) (T.toDiffusionTriple.cls a) +
        inner ℝ (g' : Lp ℝ 2 T.μ) (T.toDiffusionTriple.cls a)
      ring
    have hdoma := DiffusionTriple.cls_mem_generator_domain T.toDiffusionTriple a
    obtain ⟨hQa, hform⟩ := S.generator_mem_Q_and_form hdoma
    have h3 := hform g'
    have h5 : S.generator ⟨T.toDiffusionTriple.cls a, hdoma⟩ = T.toDiffusionTriple.Lcls a :=
      DiffusionTriple.generator_cls T.toDiffusionTriple a hdoma
    rw [h5] at h3
    have h4 : T.toDiffusionTriple.closedForm g' (T.toDiffusionTriple.clsQ a) =
        -inner ℝ (T.toDiffusionTriple.Lcls a) (g' : Lp ℝ 2 T.μ) := by
      rw [closedForm_comm]
      exact h3
    rw [inner_add_left, h1, ← hgg a, h2, h4, real_inner_comm]
    ring
  obtain ⟨hdom, _⟩ := mem_domain_of_adjoint (F0 + (g' : Lp ℝ 2 T.μ)) (g' : Lp ℝ 2 T.μ) hadj
  obtain ⟨hQ, _⟩ := S.generator_mem_Q_and_form hdom
  have := S.Q.sub_mem hQ g'.2
  show F0 ∈ S.Q
  simpa using this

end FullTriple

end MarkovTriple.BGL
