import Mathlib
import MarkovTriple.BGL.Theory.Extension.Ident

/-!
# Prop. 3.3.17 (second part, BGL pp. 161–162): the two definitions of `Γ₂` coincide on `𝒜 ∩ 𝒟(L)`

Route (the book says "the identity of the `Γ₂` operators follows along the same lines" as for the Hessians): for
`m ∈ 𝒜₀` and `a ∈ 𝒜`,
`∫ m Γ₂(a) = ½ ∫ (L m) Γ(a) + ∫ m (L a)² + ∫ (L a) Γ(a,m)`  (F1, F7 only, `int_m_Γ₂`),
every term of which passes to the graph limit `a_k → f ∈ 𝒜 ∩ 𝒟(L)` (`Γ(a_k) → Γ(f)` by Prop. 3.3.5 (ii), `L a_k → L f` by
Prop. 3.3.5 (i)), and then the `𝒜₀`-detection of `L¹`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma norm_jE_le (x : T.A₀) : ‖jE T x‖ ≤ 2 * ‖jL T x‖ := by
  have h1 : ‖T.toDiffusionTriple.cls x‖ ≤ ‖jL T x‖ := norm_fst_le (jL T x)
  have h2 : ‖T.toDiffusionTriple.Lcls x‖ ≤ ‖jL T x‖ := norm_snd_le (jL T x)
  have h3 := int_G_self_le (T := T) x.2
  have h4 : ∫ y, G T x.1 x.1 y ∂T.μ ≤ ‖jL T x‖ ^ 2 := by
    have : ‖T.toDiffusionTriple.cls ⟨T.L x.1, T.L_mem x.1 x.2⟩‖ = ‖T.toDiffusionTriple.Lcls x‖ := by
      rw [Lcls_eq_cls]
    rw [this] at h3
    nlinarith [norm_nonneg (T.toDiffusionTriple.cls x), norm_nonneg (T.toDiffusionTriple.Lcls x)]
  have h5 : ‖jE T x‖ ^ 2 ≤ (2 * ‖jL T x‖) ^ 2 := by
    rw [norm_jE_sq]
    nlinarith [norm_nonneg (T.toDiffusionTriple.cls x)]
  exact abs_le_of_sq_le_sq' h5 (by positivity) |>.2

/-- graph convergence implies form convergence (`𝒟(L) ⊂ 𝒟(ℰ)`, with the graph norm finer than the form norm). -/
theorem GraphConv.formConv {a : ℕ → T.A₀} {u : Lp ℝ 2 T.μ}
    {hu : u ∈ T.toDiffusionTriple.generator.domain} (h : GraphConv T a u hu) :
    ∃ hQ : u ∈ T.formDomain, FormConv T a ⟨u, hQ⟩ := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  have hcs : CauchySeq (fun k => jE T (a k)) := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have c1 := cauchySeq_iff_tendsto_dist_atTop_0.1 (Tendsto.cauchySeq h)
    have lim := c1.const_mul 2
    simp only [mul_zero] at lim
    refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) lim
    rw [dist_eq_norm, ← map_sub]
    refine (norm_jE_le _).trans ?_
    rw [map_sub, ← dist_eq_norm]
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcs
  have hι : S.ι z = u := by
    have := (S.ι.continuous.tendsto z).comp hz
    exact tendsto_nhds_unique (this.congr (fun k => ι_jE (a k))) (GraphConv.cls h)
  have hQ : u ∈ T.formDomain := ⟨z, hι⟩
  refine ⟨hQ, ?_⟩
  unfold FormConv
  have : S.qEquiv.symm ⟨u, hQ⟩ = z := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [Hilbert.FormData.qEquiv_apply]; exact hι.symm)
  show Tendsto _ atTop (𝓝 (S.qEquiv.symm ⟨u, hQ⟩))
  rw [this]; exact hz

lemma mulA₀₁ {u v : E → ℝ} (hu : u ∈ T.A₀) (hv : v ∈ T.A) : (fun x => u x * v x) ∈ T.A₀ :=
  T.ideal v hv u hu

lemma Γ₂_memA {a : E → ℝ} (ha : a ∈ T.A) : T.toDiffusionTriple.Γ₂ a a ∈ T.A := by
  have h1 := T.L_mem_A _ (G_mem ha ha)
  have h2 := G_mem ha (T.L_mem_A a ha)
  have : T.toDiffusionTriple.Γ₂ a a = (1 / 2 : ℝ) • (T.L (G T a a) - (2 : ℝ) • G T a (T.L a)) := by
    funext x
    simp only [DiffusionTriple.Γ₂, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [show T.toDiffusionTriple.ΓA (T.L a) a x = T.toDiffusionTriple.ΓA a (T.L a) x from
      congrFun (DiffusionTriple.ΓA_comm T.toDiffusionTriple (T.L a) a) x]
    simp only [G]
    ring
  rw [this]
  exact T.A.smul_mem (T.A.sub_mem h1 (T.A.smul_mem h2 _)) _

/-- **Integrated `Γ₂`** (F1, F7): for `a ∈ 𝒜`, `m ∈ 𝒜₀`,
`∫ m Γ₂(a) = ½ ∫ (L m) Γ(a) + ∫ m (L a)² + ∫ (L a) Γ(a,m)`. -/
theorem int_m_Γ₂ {a m : E → ℝ} (ha : a ∈ T.A) (hm : m ∈ T.A₀) :
    ∫ x, m x * T.toDiffusionTriple.Γ₂ a a x ∂T.μ =
      (1 / 2 : ℝ) * ∫ x, T.L m x * G T a a x ∂T.μ + ∫ x, m x * (T.L a x) ^ 2 ∂T.μ +
        ∫ x, T.L a x * G T a m x ∂T.μ := by
  have hmA := A₀_memA hm
  have hw := G_mem ha ha
  have hb' := L_memA ha
  have h1 := T.ibp_A (G T a a) hw m hm
  have hq : m * T.L a ∈ T.A₀ := T.ideal _ hb' m hm
  have h2 := (T.ibp_A a ha (m * T.L a) hq).1
  have e := G_mul_right (T := T) hmA hb' ha
  have iLw : Integrable (fun x => m x * T.L (G T a a) x) T.μ := intA₀ (mulA₀₁ hm (L_memA hw))
  have iGab : Integrable (fun x => m x * G T a (T.L a) x) T.μ := intA₀ (mulA₀₁ hm (G_mem ha hb'))
  have iLmw : Integrable (fun x => T.L m x * G T a a x) T.μ := intA₀ (mulA₀₁ (L_memA₀ hm) hw)
  have iB : Integrable (fun x => m x * (T.L a x) ^ 2) T.μ :=
    intA₀ (mulA₀₁ hm (by
      have : (fun x => (T.L a x) ^ 2) = T.L a * T.L a := by funext x; simp [sq]
      show (fun x => (T.L a x) ^ 2) ∈ T.A
      rw [this]; exact T.A.mul_mem hb' hb'))
  have iC : Integrable (fun x => T.L a x * G T a m x) T.μ := intA₀ (mulA₀ hb' (G_memA₀ ha hm))
  have iD : Integrable (fun x => m x * G T a (T.L a) x) T.μ := iGab
  -- (a) ∫ m L w = ∫ L m · w
  have ha1 : ∫ x, m x * T.L (G T a a) x ∂T.μ = ∫ x, T.L m x * G T a a x ∂T.μ := by
    have := h1.1.symm.trans h1.2
    have e2 : ∫ x, m x * T.L (G T a a) x ∂T.μ = ∫ x, G T a a x * T.L m x ∂T.μ := by linarith
    rw [e2]; exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  -- (b) ∫ m Γ(a,La) = -∫ m (La)^2 - ∫ La Γ(a,m)
  have iG1 : Integrable (fun x => m x * G T a (T.L a) x) T.μ := iGab
  have iG2 : Integrable (fun x => T.L a x * G T a m x) T.μ := iC
  have hb2 : ∫ x, m x * G T a (T.L a) x ∂T.μ =
      -∫ x, m x * (T.L a x) ^ 2 ∂T.μ - ∫ x, T.L a x * G T a m x ∂T.μ := by
    have e3 : ∫ x, G T a (m * T.L a) x ∂T.μ =
        ∫ x, m x * G T a (T.L a) x ∂T.μ + ∫ x, T.L a x * G T a m x ∂T.μ := by
      rw [← integral_add iG1 iG2]; exact integral_congr_ae e
    have e4 : ∫ x, (m * T.L a) x * T.L a x ∂T.μ = ∫ x, m x * (T.L a x) ^ 2 ∂T.μ :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
    linarith [e3, h2, e4]
  -- assemble
  have hΓ : ∀ x, m x * T.toDiffusionTriple.Γ₂ a a x =
      (1 / 2 : ℝ) * (m x * T.L (G T a a) x) - m x * G T a (T.L a) x := by
    intro x
    simp only [DiffusionTriple.Γ₂]
    rw [show T.toDiffusionTriple.ΓA (T.L a) a x = T.toDiffusionTriple.ΓA a (T.L a) x from
      congrFun (DiffusionTriple.ΓA_comm T.toDiffusionTriple (T.L a) a) x]
    simp only [G]
    ring
  have : ∫ x, m x * T.toDiffusionTriple.Γ₂ a a x ∂T.μ =
      (1 / 2 : ℝ) * ∫ x, m x * T.L (G T a a) x ∂T.μ - ∫ x, m x * G T a (T.L a) x ∂T.μ := by
    rw [← integral_const_mul, ← integral_sub (iLw.const_mul _) iD]
    exact integral_congr_ae (Eventually.of_forall hΓ)
  rw [this, ha1, hb2]
  ring

/-- the `L²`-class of `Γ(a,m)`, `a, m ∈ 𝒜₀`. -/
noncomputable def Gm (T : FullTriple E) (m a : T.A₀) : Lp ℝ 2 T.μ :=
  (DiffusionTriple.memLp2 T.toDiffusionTriple (G_memA₀ (A₀_memA a.2) m.2)).toLp (G T a.1 m.1)

lemma Gm_ae (m a : T.A₀) : (Gm T m a : E → ℝ) =ᵐ[T.μ] G T a.1 m.1 := MemLp.coeFn_toLp _

lemma Gm_sub (m a b : T.A₀) : Gm T m (a - b) = Gm T m a - Gm T m b := by
  refine Lp.ext ?_
  filter_upwards [Gm_ae m (a - b), Gm_ae m a, Gm_ae m b, Lp.coeFn_sub (Gm T m a) (Gm T m b),
    G_lin_left (A₀_memA a.2) (A₀_memA b.2) (-1) (A₀_memA m.2)] with x e1 e2 e3 e4 e5
  rw [e4, Pi.sub_apply, e1, e2, e3, coe_sub']
  rw [e5]; ring

lemma norm_Gm_le (m : T.A₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : T.A₀, ‖Gm T m a‖ ≤ C * ‖jE T a‖ := by
  obtain ⟨B, hB⟩ := T.bounded (G T m.1 m.1) (T.ΓA_self_mem_A₀ m.2)
  set B' := |B| with hB'
  refine ⟨√B', Real.sqrt_nonneg _, fun a => ?_⟩
  have h1 : ‖Gm T m a‖ ^ 2 = ∫ x, (G T a.1 m.1 x) ^ 2 ∂T.μ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [Gm_ae m a] with x hx
    rw [hx]; ring
  have h2 := sq_int_G_le (T := T) a.2 m.2 (B := B')
    (Eventually.of_forall fun x => (le_abs_self _).trans ((hB x).trans (le_abs_self B)))
  have h3 : ‖Gm T m a‖ ^ 2 ≤ B' * ‖jE T a‖ ^ 2 := by
    rw [h1]
    refine h2.trans ?_
    exact mul_le_mul_of_nonneg_left (int_G_le_norm_jE a) (abs_nonneg _)
  calc ‖Gm T m a‖ = √(‖Gm T m a‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √(B' * ‖jE T a‖ ^ 2) := Real.sqrt_le_sqrt h3
    _ = √B' * ‖jE T a‖ := by rw [Real.sqrt_mul (abs_nonneg _), Real.sqrt_sq (norm_nonneg _)]

/-- `⟪f, L a⟫ = ⟪L f, a⟫` for the generator on `u ∈ 𝒟(L)` and `a ∈ 𝒜₀`. -/
lemma inner_generator_cls (u : Lp ℝ 2 T.μ) (hu : u ∈ T.toDiffusionTriple.generator.domain) (a : T.A₀) :
    inner ℝ u (T.toDiffusionTriple.Lcls a) =
      inner ℝ (T.toDiffusionTriple.generator ⟨u, hu⟩) (T.toDiffusionTriple.cls a) := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  obtain ⟨hQu, hfu⟩ := S.generator_mem_Q_and_form hu
  have hdoma := DiffusionTriple.cls_mem_generator_domain T.toDiffusionTriple a
  obtain ⟨hQa, hfa⟩ := S.generator_mem_Q_and_form hdoma
  have e1 := hfu (T.toDiffusionTriple.clsQ a)
  have e2 := hfa ⟨u, hQu⟩
  have h5 : S.generator ⟨T.toDiffusionTriple.cls a, hdoma⟩ = T.toDiffusionTriple.Lcls a :=
    DiffusionTriple.generator_cls T.toDiffusionTriple a hdoma
  rw [h5] at e2
  have e3 : T.toDiffusionTriple.closedForm ⟨u, hQu⟩ (T.toDiffusionTriple.clsQ a) =
      T.toDiffusionTriple.closedForm (T.toDiffusionTriple.clsQ a) ⟨u, hQu⟩ := closedForm_comm _ _
  have e1' : T.toDiffusionTriple.closedForm ⟨u, hQu⟩ (T.toDiffusionTriple.clsQ a) =
      -inner ℝ (T.toDiffusionTriple.generator ⟨u, hu⟩) (T.toDiffusionTriple.cls a) := e1
  have e2' : T.toDiffusionTriple.closedForm (T.toDiffusionTriple.clsQ a) ⟨u, hQu⟩ =
      -inner ℝ (T.toDiffusionTriple.Lcls a) u := e2
  rw [e3, e2'] at e1'
  rw [real_inner_comm]; linarith

/-- **BGL Prop. 3.3.17, `Γ₂`**: let `f ∈ 𝒜 ∩ 𝒟(L)` and `a_k → f` in `𝒟(L)`; if `γ₂` is the `L¹`-limit of
`Γ₂(a_k)` (the extended `Γ₂(f)` of Prop. 3.3.16 (i)–(iii), `gamma_limits`), then `γ₂ = Γ₂^𝒜(f)` a.e. -/
theorem Γ₂_ext_eq {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hu : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain) {a : ℕ → T.A₀}
    (ha : GraphConv T a (hf2.toLp f) hu) {γ₂ : Lp ℝ 1 T.μ}
    (hγ₂ : Tendsto (fun k => G2cls T (a k)) atTop (𝓝 γ₂)) :
    (γ₂ : E → ℝ) =ᵐ[T.μ] T.toDiffusionTriple.Γ₂ f f := by
  set u : Lp ℝ 2 T.μ := hf2.toLp f with hudef
  set w := T.toDiffusionTriple.generator ⟨u, hu⟩ with hw
  obtain ⟨hQ, hfc⟩ := ha.formConv
  have hLf2 : (w : E → ℝ) =ᵐ[T.μ] T.L f := by
    refine adjoint_eq_L hf hf2 w (fun a' => ?_)
    exact inner_generator_cls u hu a'
  have hGff := gammaE_self_eq_ΓA hf hf2 hQ
  have gE := gammaE_tendsto hfc hfc
  have gEm : ∀ m : T.A₀, Tendsto (fun k => GG T (a k) m) atTop
      (𝓝 (gammaE T ⟨u, hQ⟩ (T.toDiffusionTriple.clsQ m))) := fun m =>
    gammaE_tendsto hfc (formConv_const m)
  -- the key integrated identity
  have key : ∀ m : T.A₀, ∫ x, m.1 x * (γ₂ : E → ℝ) x ∂T.μ = ∫ x, m.1 x * T.toDiffusionTriple.Γ₂ f f x ∂T.μ := by
    intro m
    obtain ⟨Cm, hCm⟩ := T.bounded m.1 m.2
    obtain ⟨CLm, hCLm⟩ := T.bounded (T.L m.1) (T.L_mem m.1 m.2)
    have hmm := T.measurable m.1 m.2
    have hLmm := T.measurable (T.L m.1) (T.L_mem m.1 m.2)
    -- (T0) the left side
    have t0 := tendsto_int_mul_L1 hmm hCm hγ₂
    -- (T1)
    have t1 := tendsto_int_mul_L1 hLmm hCLm gE
    -- (T2)
    have t2 := tendsto_int_mul_L1 hmm hCm (tendsto_Sq (T := T) (ha.Lcls))
    -- (T3) : L² convergence of Gm
    obtain ⟨CG, hCG0, hCG⟩ := norm_Gm_le m
    have hcsG : CauchySeq (fun k => Gm T m (a k)) := by
      rw [cauchySeq_iff_tendsto_dist_atTop_0]
      have c1 := cauchySeq_iff_tendsto_dist_atTop_0.1 (Tendsto.cauchySeq hfc)
      have lim := c1.const_mul CG
      simp only [mul_zero] at lim
      refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) lim
      rw [dist_eq_norm, ← Gm_sub]
      refine (hCG _).trans ?_
      rw [map_sub, ← dist_eq_norm]
    obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hcsG
    have t3 : Tendsto (fun k => inner ℝ (T.toDiffusionTriple.Lcls (a k)) (Gm T m (a k))) atTop
        (𝓝 (inner ℝ w ℓ)) := (ha.Lcls).inner hℓ
    -- identification of ℓ
    have hℓe : (ℓ : E → ℝ) =ᵐ[T.μ] G T f m.1 := by
      have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
      have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
      obtain ⟨φ, hφ, a1, a2⟩ := Lp_ae_subseq_two hℓ (gEm m)
      have hall : ∀ᵐ x ∂T.μ, ∀ n, (Gm T m (a n) : E → ℝ) x = (GG T (a n) m : E → ℝ) x := by
        rw [ae_all_iff]; intro n
        filter_upwards [Gm_ae m (a n), GG_ae (a n) m] with x h1 h2
        rw [h1, h2]
      have hid := gammaE_clsQ_eq hf hf2 hQ m
      filter_upwards [a1, a2, hall, hid] with x h1 h2 h3 h4
      have h5 : Tendsto (fun n => (Gm T m (a (φ n)) : E → ℝ) x) atTop
          (𝓝 ((gammaE T ⟨u, hQ⟩ (T.toDiffusionTriple.clsQ m) : E → ℝ) x)) :=
        h2.congr (fun n => (h3 (φ n)).symm)
      rw [← h4]
      exact tendsto_nhds_unique h1 h5
    -- the sequence identity
    have hseq : ∀ k, ∫ x, m.1 x * (G2cls T (a k) : E → ℝ) x ∂T.μ =
        (1 / 2 : ℝ) * ∫ x, T.L m.1 x * (GG T (a k) (a k) : E → ℝ) x ∂T.μ +
          ∫ x, m.1 x * (Sq (T.toDiffusionTriple.Lcls (a k)) : E → ℝ) x ∂T.μ +
          inner ℝ (T.toDiffusionTriple.Lcls (a k)) (Gm T m (a k)) := by
      intro k
      have e0 := int_m_Γ₂ (A₀_memA (a k).2) m.2
      have c0 : ∫ x, m.1 x * (G2cls T (a k) : E → ℝ) x ∂T.μ =
          ∫ x, m.1 x * T.toDiffusionTriple.Γ₂ (a k).1 (a k).1 x ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [G2cls_ae (a k)] with x hx
        rw [hx]
      have c1 : ∫ x, T.L m.1 x * (GG T (a k) (a k) : E → ℝ) x ∂T.μ =
          ∫ x, T.L m.1 x * G T (a k).1 (a k).1 x ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [GG_ae (a k) (a k)] with x hx
        rw [hx]
      have c2 : ∫ x, m.1 x * (Sq (T.toDiffusionTriple.Lcls (a k)) : E → ℝ) x ∂T.μ =
          ∫ x, m.1 x * (T.L (a k).1 x) ^ 2 ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [Integrable.coeFn_toL1 (Lp.memLp (T.toDiffusionTriple.Lcls (a k))).integrable_sq,
          DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (a k)] with x h1 h2
        show m.1 x * ((Lp.memLp (T.toDiffusionTriple.Lcls (a k))).integrable_sq.toL1 _ : E → ℝ) x = _
        rw [h1, h2]
      have c3 : inner ℝ (T.toDiffusionTriple.Lcls (a k)) (Gm T m (a k)) =
          ∫ x, T.L (a k).1 x * G T (a k).1 m.1 x ∂T.μ := by
        rw [L2_inner_eq]
        refine integral_congr_ae ?_
        filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (a k), Gm_ae m (a k)] with x h1 h2
        rw [h1, h2]
      rw [c0, c1, c2, c3]
      exact e0
    -- limit of the right side
    have lhs := tendsto_nhds_unique t0 (by
      have := ((t1.const_mul (1 / 2 : ℝ)).add t2).add t3
      exact this.congr (fun k => (hseq k).symm))
    rw [lhs]
    -- evaluate the limits
    have e1 : ∫ x, T.L m.1 x * (gammaE T ⟨u, hQ⟩ ⟨u, hQ⟩ : E → ℝ) x ∂T.μ =
        ∫ x, T.L m.1 x * G T f f x ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hGff] with x hx
      rw [hx]
    have e2 : ∫ x, m.1 x * (Sq w : E → ℝ) x ∂T.μ = ∫ x, m.1 x * (T.L f x) ^ 2 ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [Integrable.coeFn_toL1 (Lp.memLp w).integrable_sq, hLf2] with x h1 h2
      show m.1 x * ((Lp.memLp w).integrable_sq.toL1 _ : E → ℝ) x = _
      rw [h1, h2]
    have e3 : inner ℝ w ℓ = ∫ x, T.L f x * G T f m.1 x ∂T.μ := by
      rw [L2_inner_eq]
      refine integral_congr_ae ?_
      filter_upwards [hLf2, hℓe] with x h1 h2
      rw [h1, h2]
    rw [e1, e2, e3, int_m_Γ₂ hf m.2]
  -- from the integrated identity to the a.e. identity
  refine ae_eq_of_mul_A₀ (fun k => ?_)
  obtain ⟨Ck, hCk⟩ := T.bounded k.1 k.2
  have hkm := T.measurable k.1 k.2
  have hb : ∀ᵐ x ∂T.μ, ‖k.1 x‖ ≤ Ck := Eventually.of_forall fun x => by simpa using hCk x
  have hΓ2 : T.toDiffusionTriple.Γ₂ f f ∈ T.A := Γ₂_memA hf
  have i1 : Integrable (fun x => k.1 x * (γ₂ : E → ℝ) x) T.μ :=
    (L1.integrable_coeFn _).bdd_mul hkm.aestronglyMeasurable hb
  have i2 : Integrable (fun x => k.1 x * T.toDiffusionTriple.Γ₂ f f x) T.μ := intA₀ (mulA₀₁ k.2 hΓ2)
  have iφ : Integrable (fun x => k.1 x * ((γ₂ : E → ℝ) x - T.toDiffusionTriple.Γ₂ f f x)) T.μ := by
    refine (i1.sub i2).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]; ring
  have hz := ae_zero_of_forall_integral_A₀ iφ (fun m => by
    obtain ⟨Cm, hCm⟩ := T.bounded m.1 m.2
    have hmk : (m * k).1 = fun x => m.1 x * k.1 x := rfl
    have := key (m * k)
    have e : ∀ F : E → ℝ, (fun x => m.1 x * (k.1 x * F x)) = fun x => (m * k).1 x * F x := by
      intro F; funext x; rw [hmk]; ring
    have j1 : Integrable (fun x => (m * k).1 x * (γ₂ : E → ℝ) x) T.μ := by
      obtain ⟨C', hC'⟩ := T.bounded (m * k).1 (m * k).2
      exact (L1.integrable_coeFn _).bdd_mul (T.measurable _ (m * k).2).aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa using hC' x)
    have j2 : Integrable (fun x => (m * k).1 x * T.toDiffusionTriple.Γ₂ f f x) T.μ :=
      intA₀ (mulA₀₁ (m * k).2 hΓ2)
    have ee : (fun x => m.1 x * (k.1 x * ((γ₂ : E → ℝ) x - T.toDiffusionTriple.Γ₂ f f x))) =
        fun x => (m * k).1 x * (γ₂ : E → ℝ) x - (m * k).1 x * T.toDiffusionTriple.Γ₂ f f x := by
      funext x; rw [hmk]; ring
    rw [ee, integral_sub j1 j2, this, sub_self])
  filter_upwards [hz] with x hx
  simp only [Pi.zero_apply] at hx
  have : k.1 x * ((γ₂ : E → ℝ) x - T.toDiffusionTriple.Γ₂ f f x) = 0 := hx
  linarith

/-- the generator acts as `L` on `𝒜 ∩ 𝒟(L)` (Prop. 3.3.5 (i)): `L[f] = [L f]`. -/
theorem generator_ae_L {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ)
    (hu : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain) :
    ((T.toDiffusionTriple.generator ⟨hf2.toLp f, hu⟩ : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] T.L f :=
  adjoint_eq_L hf hf2 _ (fun a' => inner_generator_cls _ hu a')

/-- **BGL Prop. 3.3.17 (second paragraph)**: for `f ∈ 𝒜 ∩ 𝒟(L)` (under ESA and `CD(ρ,n)`): `Γ_𝒜(f) ∈ L¹`,
`Γ₂^𝒜(f) ∈ L¹` and `∫ Γ₂^𝒜(f) = ∫ (L f)²`. -/
theorem integrable_Γ₂_of_domain {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A)
    (hf2 : MemLp f 2 T.μ) (hu : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain) :
    Integrable (G T f f) T.μ ∧ Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ ∧
      ∫ x, T.toDiffusionTriple.Γ₂ f f x ∂T.μ = ∫ x, (T.L f x) ^ 2 ∂T.μ := by
  obtain ⟨γ₁, γ₂, hseq, ⟨a, ha1, ha2⟩, hint2, -, -⟩ := gamma_limits hCD (hf2.toLp f) hu
  have ha : GraphConv T a (hf2.toLp f) hu := ha1.prodMk_nhds ha2
  obtain ⟨-, hG2⟩ := hseq a ha1 ha2
  have hae := Γ₂_ext_eq hf hf2 hu ha hG2
  refine ⟨(integrable_ΓA_of_domain hf hf2 hu).1, (L1.integrable_coeFn γ₂).congr hae, ?_⟩
  rw [← integral_congr_ae hae, hint2]
  have hw := generator_ae_L hf hf2 hu
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hw] with x hx
  rw [hx]; ring

/-- **Symmetric integration by parts on `𝒜 ∩ 𝒟(L)` against `𝒜 ∩ 𝒟(ℰ)`** (BGL (3.3.1), extended as announced after
Def. 3.3.1 and in Prop. 3.3.17): for `k ∈ 𝒜 ∩ 𝒟(L)` and `g ∈ 𝒜 ∩ 𝒟(ℰ)`,
`Γ_𝒜(k,g) ∈ L¹` and `∫ (L k) g dμ = −∫ Γ_𝒜(k,g) dμ`. -/
theorem ibp_of_domain {k g : E → ℝ} (hk : k ∈ T.A) (hk2 : MemLp k 2 T.μ)
    (hku : hk2.toLp k ∈ T.toDiffusionTriple.generator.domain) (hg : g ∈ T.A) (hg2 : MemLp g 2 T.μ)
    (hQg : hg2.toLp g ∈ T.formDomain) :
    Integrable (G T k g) T.μ ∧ ∫ x, T.L k x * g x ∂T.μ = -∫ x, G T k g x ∂T.μ := by
  obtain ⟨hQk, hform⟩ := (DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form hku
  have h1 := hform ⟨hg2.toLp g, hQg⟩
  have h2 := gammaE_eq_ΓA hk hk2 hQk hg hg2 hQg
  have h3 := gammaE_integral (T := T) ⟨hk2.toLp k, hQk⟩ ⟨hg2.toLp g, hQg⟩
  refine ⟨(L1.integrable_coeFn _).congr h2, ?_⟩
  have h4 : T.toDiffusionTriple.closedForm ⟨hk2.toLp k, hQk⟩ ⟨hg2.toLp g, hQg⟩ =
      -inner ℝ (T.toDiffusionTriple.generator ⟨hk2.toLp k, hku⟩) (hg2.toLp g) := h1
  rw [← integral_congr_ae h2, h3, h4, L2_inner_eq, ← integral_neg, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [generator_ae_L hk hk2 hku, hg2.coeFn_toLp] with x e1 e2
  rw [e1, e2]
  simp

end FullTriple

end MarkovTriple.BGL
