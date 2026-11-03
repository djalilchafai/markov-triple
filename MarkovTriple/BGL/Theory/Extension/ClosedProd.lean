import Mathlib
import MarkovTriple.BGL.Theory.Extension.ClosedGamma

/-!
# Multiplication by a test function on `𝒟(ℰ)` and the Leibniz rule for `Γ` on `𝒟(ℰ)` (BGL Prop. 3.1.5)

For `k ∈ 𝒜₀`, `u, v ∈ 𝒟(ℰ)`: `k v ∈ 𝒟(ℰ)` and `Γ(u, kv) = k Γ(u,v) + v Γ(u,k)` a.e.  This is the book's
"By Proposition 3.1.5, `kf ∈ 𝒟(ℰ)` and `Γ(kf,h) = kΓ(f,h) + fΓ(k,h)`" in the proof of Prop. 3.3.5 (ii).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- a convergent sequence in `Lᵖ` has an a.e.-convergent subsequence. -/
lemma Lp_ae_subseq {μ : Measure E} {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℕ → Lp ℝ p μ} {g : Lp ℝ p μ}
    (h : Tendsto f atTop (𝓝 g)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ᵐ x ∂μ, Tendsto (fun n => (f (φ n) : E → ℝ) x) atTop (𝓝 ((g : E → ℝ) x)) :=
  (tendstoInMeasure_of_tendsto_Lp h).exists_seq_tendsto_ae

/-- identification of an `L¹`-limit with an a.e.-limit along a subsequence. -/
lemma ae_eq_of_tendsto_subseq {μ : Measure E} {F : ℕ → Lp ℝ 1 μ} {ψ : Lp ℝ 1 μ}
    (h : Tendsto F atTop (𝓝 ψ)) {φ : ℕ → ℕ} (hφ : StrictMono φ) {m : E → ℝ}
    (hm : ∀ᵐ x ∂μ, Tendsto (fun n => (F (φ n) : E → ℝ) x) atTop (𝓝 (m x))) :
    (ψ : E → ℝ) =ᵐ[μ] m := by
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨ns, hns, hlim⟩ := Lp_ae_subseq (h.comp hφ.tendsto_atTop)
  filter_upwards [hlim, hm] with x h1 h2
  exact tendsto_nhds_unique h1 (h2.comp hns.tendsto_atTop)

/-- two convergent sequences in `Lᵖ`, `L^q` have a common a.e.-convergent subsequence. -/
lemma Lp_ae_subseq_two {μ : Measure E} {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    {f : ℕ → Lp ℝ p μ} {g : Lp ℝ p μ} {f' : ℕ → Lp ℝ q μ} {g' : Lp ℝ q μ}
    (h : Tendsto f atTop (𝓝 g)) (h' : Tendsto f' atTop (𝓝 g')) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => (f (φ n) : E → ℝ) x) atTop (𝓝 ((g : E → ℝ) x))) ∧
      (∀ᵐ x ∂μ, Tendsto (fun n => (f' (φ n) : E → ℝ) x) atTop (𝓝 ((g' : E → ℝ) x))) := by
  obtain ⟨φ1, h1, a1⟩ := Lp_ae_subseq h
  obtain ⟨φ2, h2, a2⟩ := Lp_ae_subseq (h'.comp h1.tendsto_atTop)
  exact ⟨φ1 ∘ φ2, h1.comp h2, a1.mono fun x hx => hx.comp h2.tendsto_atTop, a2⟩

namespace FullTriple

variable {T : FullTriple E}

lemma integrable_sq_A₀ (a : T.A₀) : Integrable (fun x => (a.1 x) ^ 2) T.μ :=
  (DiffusionTriple.memLp2 T.toDiffusionTriple a.2).integrable_sq

lemma norm_cls_sq (a : T.A₀) : ‖T.toDiffusionTriple.cls a‖ ^ 2 = ∫ x, (a.1 x) ^ 2 ∂T.μ := by
  rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple a] with x hx
  rw [hx]; ring

lemma two_mul_le_aux (k b c P Q : ℝ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (h : c ^ 2 ≤ P * Q) :
    2 * k * b * c ≤ k ^ 2 * P + b ^ 2 * Q := by
  have h1 : (2 * k * b * c) ^ 2 ≤ (k ^ 2 * P + b ^ 2 * Q) ^ 2 := by
    have : (2 * k * b * c) ^ 2 = 4 * k ^ 2 * b ^ 2 * c ^ 2 := by ring
    rw [this]
    have h2 : k ^ 2 * b ^ 2 * c ^ 2 ≤ k ^ 2 * b ^ 2 * (P * Q) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith [sq_nonneg (k ^ 2 * P - b ^ 2 * Q)]
  have h3 : 0 ≤ k ^ 2 * P + b ^ 2 * Q := by positivity
  exact (le_abs_self _).trans (abs_le_of_sq_le_sq h1 h3)

/-- pointwise: `Γ(kb) ≤ 2k²Γ(b) + 2b²Γ(k)` (consequence of the diffusion property). -/
lemma G_mul_self_le (k b : T.A₀) :
    ∀ᵐ x ∂T.μ, G T (k * b).1 (k * b).1 x ≤
      2 * (k.1 x) ^ 2 * G T b.1 b.1 x + 2 * (b.1 x) ^ 2 * G T k.1 k.1 x := by
  have hk := A₀_memA k.2
  have hb := A₀_memA b.2
  have hkb : (k * b).1 = k.1 * b.1 := rfl
  have hkbA : k.1 * b.1 ∈ T.A := T.A.mul_mem hk hb
  have e1 := G_mul_left (T := T) hk hb hkbA
  have e2 := G_mul_left (T := T) hk hb hb
  have e3 := G_mul_left (T := T) hk hb hk
  have cs := G_cs_A₀ k b
  have n1 := T.ΓA_nonneg _ hk
  have n2 := T.ΓA_nonneg _ hb
  rw [hkb]
  filter_upwards [e1, e2, e3, cs, n1, n2] with x h1 h2 h3 h4 h5 h6
  have c1 : G T b.1 (k.1 * b.1) x = G T (k.1 * b.1) b.1 x := congrFun (G_comm _ _) x
  have c2 : G T k.1 (k.1 * b.1) x = G T (k.1 * b.1) k.1 x := congrFun (G_comm _ _) x
  have c3 : G T b.1 k.1 x = G T k.1 b.1 x := congrFun (G_comm _ _) x
  rw [h1, c1, c2, h2, h3, c3]
  have := two_mul_le_aux (k.1 x) (b.1 x) (G T k.1 b.1 x) (G T b.1 b.1 x) (G T k.1 k.1 x) h6 h5 (by
    have := h4; nlinarith [this])
  nlinarith [this]

/-- multiplication by `k ∈ 𝒜₀` is bounded for the form norm. -/
lemma exists_mul_const (k : T.A₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : T.A₀, ‖jE T (k * b)‖ ≤ C * ‖jE T b‖ := by
  obtain ⟨M, hM⟩ := T.bounded k.1 k.2
  obtain ⟨B, hB⟩ := T.bounded (G T k.1 k.1) (T.ΓA_self_mem_A₀ k.2)
  set M' := |M| with hM'
  set B' := |B| with hB'
  have hkM : ∀ x, (k.1 x) ^ 2 ≤ M' ^ 2 := fun x => by
    have : |k.1 x| ≤ M' := (hM x).trans (le_abs_self M)
    exact sq_le_sq' (by linarith [abs_nonneg (k.1 x), neg_abs_le (k.1 x)]) (by linarith [le_abs_self (k.1 x)])
  have hGB : ∀ x, G T k.1 k.1 x ≤ B' := fun x => (le_abs_self _).trans ((hB x).trans (le_abs_self B))
  refine ⟨√(2 * M' ^ 2 + 2 * B'), Real.sqrt_nonneg _, fun b => ?_⟩
  have key : ‖jE T (k * b)‖ ^ 2 ≤ (2 * M' ^ 2 + 2 * B') * ‖jE T b‖ ^ 2 := by
    rw [norm_jE_sq, norm_jE_sq, norm_cls_sq, norm_cls_sq]
    have iB := integrable_sq_A₀ b
    have iG := integrable_G b b
    have iGk : Integrable (fun x => (b.1 x) ^ 2 * G T k.1 k.1 x) T.μ := by
      have := integrable_G k k
      have hb2 := (T.A₀.mul_mem b.2 b.2)
      have h3 : (fun x => (b.1 x) ^ 2 * G T k.1 k.1 x) = (b.1 * b.1) * G T k.1 k.1 := by
        funext x; simp [sq]
      rw [h3]
      exact integrable_A₀ (T.A₀.mul_mem hb2 (T.ΓA_self_mem_A₀ k.2))
    have iK : Integrable (fun x => (k.1 x) ^ 2 * G T b.1 b.1 x) T.μ := by
      have h3 : (fun x => (k.1 x) ^ 2 * G T b.1 b.1 x) = (k.1 * k.1) * G T b.1 b.1 := by
        funext x; simp [sq]
      rw [h3]
      exact integrable_A₀ (T.A₀.mul_mem (T.A₀.mul_mem k.2 k.2) (T.ΓA_self_mem_A₀ b.2))
    have iKB : Integrable (fun x => ((k * b).1 x) ^ 2) T.μ := integrable_sq_A₀ (k * b)
    have iGkb : Integrable (G T (k * b).1 (k * b).1) T.μ := integrable_G (k * b) (k * b)
    -- term 1
    have t1 : ∫ x, ((k * b).1 x) ^ 2 ∂T.μ ≤ M' ^ 2 * ∫ x, (b.1 x) ^ 2 ∂T.μ := by
      rw [← integral_const_mul]
      refine integral_mono iKB (iB.const_mul _) (fun x => ?_)
      show (k.1 x * b.1 x) ^ 2 ≤ M' ^ 2 * (b.1 x) ^ 2
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (hkM x) (sq_nonneg _)
    -- term 2
    have t2 : ∫ x, G T (k * b).1 (k * b).1 x ∂T.μ ≤
        2 * M' ^ 2 * ∫ x, G T b.1 b.1 x ∂T.μ + 2 * B' * ∫ x, (b.1 x) ^ 2 ∂T.μ := by
      have hint : Integrable (fun x => 2 * (k.1 x) ^ 2 * G T b.1 b.1 x +
          2 * (b.1 x) ^ 2 * G T k.1 k.1 x) T.μ := by
        have a1 := iK.const_mul 2
        have a2 := iGk.const_mul 2
        refine (a1.add a2).congr (Eventually.of_forall fun x => ?_)
        simp only [Pi.add_apply]; ring
      refine (integral_mono_ae iGkb hint (G_mul_self_le k b)).trans ?_
      have a1 : ∫ x, 2 * (k.1 x) ^ 2 * G T b.1 b.1 x ∂T.μ ≤
          2 * M' ^ 2 * ∫ x, G T b.1 b.1 x ∂T.μ := by
        rw [← integral_const_mul]
        refine integral_mono_ae (iK.const_mul 2 |>.congr (Eventually.of_forall fun x => by ring))
          (iG.const_mul _) ?_
        filter_upwards [T.ΓA_nonneg _ (A₀_memA b.2)] with x hx
        have := mul_le_mul_of_nonneg_right (hkM x) hx
        nlinarith [this]
      have a2 : ∫ x, 2 * (b.1 x) ^ 2 * G T k.1 k.1 x ∂T.μ ≤
          2 * B' * ∫ x, (b.1 x) ^ 2 ∂T.μ := by
        rw [← integral_const_mul]
        refine integral_mono_ae (iGk.const_mul 2 |>.congr (Eventually.of_forall fun x => by ring))
          (iB.const_mul _) (Eventually.of_forall fun x => ?_)
        have := mul_le_mul_of_nonneg_left (hGB x) (sq_nonneg (b.1 x))
        nlinarith [this]
      rw [integral_add (iK.const_mul 2 |>.congr (Eventually.of_forall fun x => by ring))
        (iGk.const_mul 2 |>.congr (Eventually.of_forall fun x => by ring))]
      linarith
    have n1 : 0 ≤ ∫ x, (b.1 x) ^ 2 ∂T.μ := integral_nonneg (fun x => sq_nonneg _)
    have n2 : 0 ≤ ∫ x, G T b.1 b.1 x ∂T.μ := integral_nonneg_of_ae (T.ΓA_nonneg _ (A₀_memA b.2))
    have hB0 : 0 ≤ B' := abs_nonneg _
    have hM0 : 0 ≤ M' ^ 2 := sq_nonneg _
    nlinarith [mul_nonneg hM0 n1, mul_nonneg hM0 n2, mul_nonneg hB0 n1, mul_nonneg hB0 n2]
  have h0 : 0 ≤ 2 * M' ^ 2 + 2 * B' := by positivity
  calc ‖jE T (k * b)‖ = √(‖jE T (k * b)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ √((2 * M' ^ 2 + 2 * B') * ‖jE T b‖ ^ 2) := Real.sqrt_le_sqrt key
    _ = √(2 * M' ^ 2 + 2 * B') * ‖jE T b‖ := by
        rw [Real.sqrt_mul h0, Real.sqrt_sq (norm_nonneg _)]

/-- **multiplication by `k ∈ 𝒜₀` on `𝒟(ℰ)`** (BGL Prop. 3.1.5): `k v ∈ 𝒟(ℰ)`, the limit of `k b_n` in the form
norm, and it is the product `k · v` a.e. -/
theorem mul_formDomain (k : T.A₀) (v : T.formDomain) :
    ∃ w : T.formDomain, (∀ b : ℕ → T.A₀, FormConv T b v → FormConv T (fun n => k * b n) w) ∧
      ((w : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] fun x => k.1 x * ((v : Lp ℝ 2 T.μ) : E → ℝ) x := by
  obtain ⟨C, hC0, hC⟩ := exists_mul_const k
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  -- existence of a candidate for every approximating sequence
  have key : ∀ b : ℕ → T.A₀, FormConv T b v → ∃ w : T.formDomain,
      FormConv T (fun n => k * b n) w ∧
        ((w : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] fun x => k.1 x * ((v : Lp ℝ 2 T.μ) : E → ℝ) x := by
    intro b hb
    have hcs : CauchySeq (fun n => jE T (k * b n)) := by
      rw [cauchySeq_iff_tendsto_dist_atTop_0]
      have c1 := cauchySeq_iff_tendsto_dist_atTop_0.1 (Tendsto.cauchySeq hb)
      have lim := c1.const_mul C
      simp only [mul_zero] at lim
      refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) lim
      rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← map_sub, ← mul_sub]
      exact hC _
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hcs
    refine ⟨S.qEquiv z, ?_, ?_⟩
    · unfold FormConv
      show Tendsto _ atTop (𝓝 (S.qEquiv.symm (S.qEquiv z)))
      rw [LinearEquiv.symm_apply_apply]; exact hz
    · have hL2 : Tendsto (fun n => T.toDiffusionTriple.cls (k * b n)) atTop
          (𝓝 ((S.qEquiv z : T.formDomain) : Lp ℝ 2 T.μ)) := by
        have := (S.ι.continuous.tendsto z).comp hz
        have e : ((S.qEquiv z : T.formDomain) : Lp ℝ 2 T.μ) = S.ι z := rfl
        rw [e]
        exact this.congr (fun n => ι_jE (k * b n))
      have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
      obtain ⟨φ, hφ, a1, a2⟩ := Lp_ae_subseq_two (FormConv.cls hb) hL2
      have hall : ∀ᵐ x ∂T.μ, ∀ n, ((T.toDiffusionTriple.cls (k * b n) : Lp ℝ 2 T.μ) : E → ℝ) x =
          k.1 x * ((T.toDiffusionTriple.cls (b n) : Lp ℝ 2 T.μ) : E → ℝ) x := by
        rw [ae_all_iff]
        intro n
        filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple (k * b n),
          DiffusionTriple.coeFn_cls T.toDiffusionTriple (b n)] with x h1 h2
        rw [h1, h2]; rfl
      filter_upwards [a1, a2, hall] with x h1 h2 h3
      have h4 : Tendsto (fun n => ((T.toDiffusionTriple.cls (k * b (φ n)) : Lp ℝ 2 T.μ) : E → ℝ) x)
          atTop (𝓝 (k.1 x * ((v : Lp ℝ 2 T.μ) : E → ℝ) x)) := by
        have := h1.const_mul (k.1 x)
        exact this.congr (fun n => (h3 (φ n)).symm)
      exact tendsto_nhds_unique h2 h4
  obtain ⟨b0, hb0⟩ := exists_formConv v
  obtain ⟨w0, hw0, hae0⟩ := key b0 hb0
  refine ⟨w0, fun b hb => ?_, hae0⟩
  obtain ⟨w1, hw1, hae1⟩ := key b hb
  have : w1 = w0 := by
    apply Subtype.ext
    apply Lp.ext
    filter_upwards [hae0, hae1] with x h0 h1
    rw [h0, h1]
  rw [← this]; exact hw1

/-- the product `k · v ∈ 𝒟(ℰ)`, `k ∈ 𝒜₀`, `v ∈ 𝒟(ℰ)`. -/
noncomputable def mulE (k : T.A₀) (v : T.formDomain) : T.formDomain :=
  Classical.choose (mul_formDomain k v)

theorem mulE_formConv (k : T.A₀) {v : T.formDomain} {b : ℕ → T.A₀} (hb : FormConv T b v) :
    FormConv T (fun n => k * b n) (mulE k v) :=
  (Classical.choose_spec (mul_formDomain k v)).1 b hb

theorem mulE_ae (k : T.A₀) (v : T.formDomain) :
    ((mulE k v : T.formDomain) : Lp ℝ 2 T.μ) =ᵐ[T.μ]
      fun x => k.1 x * ((v : Lp ℝ 2 T.μ) : E → ℝ) x :=
  (Classical.choose_spec (mul_formDomain k v)).2

/-- **Leibniz rule for `Γ` on `𝒟(ℰ)`** (BGL Prop. 3.1.5): `Γ(u, k v) = k Γ(u,v) + v Γ(u,k)` a.e. -/
theorem gammaE_mulE (k : T.A₀) (u v : T.formDomain) :
    (gammaE T u (mulE k v) : E → ℝ) =ᵐ[T.μ] fun x =>
      k.1 x * (gammaE T u v : E → ℝ) x +
        ((v : Lp ℝ 2 T.μ) : E → ℝ) x * (gammaE T u (T.toDiffusionTriple.clsQ k) : E → ℝ) x := by
  obtain ⟨a, ha⟩ := exists_formConv u
  obtain ⟨b, hb⟩ := exists_formConv v
  have s1 := gammaE_tendsto ha hb
  have s2 := gammaE_tendsto ha (formConv_const k)
  have s3 := FormConv.cls hb
  have s4 := gammaE_tendsto ha (mulE_formConv k hb)
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨one_le_two⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  obtain ⟨φ, hφ, a1, a2⟩ := Lp_ae_subseq_two s1 s2
  obtain ⟨ψ, hψ, a3, a4⟩ := Lp_ae_subseq_two (s3.comp hφ.tendsto_atTop) (s4.comp hφ.tendsto_atTop)
  have hall : ∀ᵐ x ∂T.μ, ∀ n, (GG T (a n) (k * b n) : E → ℝ) x =
      k.1 x * (GG T (a n) (b n) : E → ℝ) x +
        ((T.toDiffusionTriple.cls (b n) : Lp ℝ 2 T.μ) : E → ℝ) x * (GG T (a n) k : E → ℝ) x := by
    rw [ae_all_iff]
    intro n
    have hA := A₀_memA (a n).2
    have hK := A₀_memA k.2
    have hB := A₀_memA (b n).2
    have e1 := G_mul_left (T := T) hK hB hA
    filter_upwards [GG_ae (a n) (k * b n), GG_ae (a n) (b n), GG_ae (a n) k,
      DiffusionTriple.coeFn_cls T.toDiffusionTriple (b n), e1] with x h1 h2 h3 h4 h5
    rw [h1, h2, h3, h4]
    have c1 : G T (a n).1 (k * b n).1 x = G T (k.1 * (b n).1) (a n).1 x :=
      congrFun (G_comm _ _) x
    have c2 : G T (b n).1 (a n).1 x = G T (a n).1 (b n).1 x := congrFun (G_comm _ _) x
    have c3 : G T k.1 (a n).1 x = G T (a n).1 k.1 x := congrFun (G_comm _ _) x
    show G T (a n).1 (k.1 * (b n).1) x = _
    rw [show G T (a n).1 (k.1 * (b n).1) x = G T (k.1 * (b n).1) (a n).1 x from congrFun (G_comm _ _) x,
      h5, c2, c3]
  filter_upwards [a1, a2, a3, a4, hall] with x h1 h2 h3 h4 h5
  have h6 : Tendsto (fun n => (GG T (a (φ (ψ n))) (k * b (φ (ψ n))) : E → ℝ) x) atTop
      (𝓝 (k.1 x * (gammaE T u v : E → ℝ) x +
        ((v : Lp ℝ 2 T.μ) : E → ℝ) x * (gammaE T u (T.toDiffusionTriple.clsQ k) : E → ℝ) x)) := by
    have e1 := (h1.comp hψ.tendsto_atTop).const_mul (k.1 x)
    have e2 := h3.mul (h2.comp hψ.tendsto_atTop)
    exact (e1.add e2).congr (fun n => (h5 (φ (ψ n))).symm)
  exact tendsto_nhds_unique h4 h6

end FullTriple

end MarkovTriple.BGL
