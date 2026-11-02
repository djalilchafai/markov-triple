import Mathlib
import MarkovTriple.BGL.Theory.Extension.Gamma2

/-!
# Prop. 3.3.16 (i)–(iii), operator level: `Γ` and `Γ₂` extend to `𝒟(L)` as `L¹`-valued maps
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace LinearPMap

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- the `L¹` distance of `G1` in terms of the graph distance. -/
lemma dist_G1_le (a b : T.A₀) {l : ℝ} (hl : 0 < l) :
    dist (G1 T a) (G1 T b) ≤
      (l * (‖T.toDiffusionTriple.cls a - T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a - T.toDiffusionTriple.Lcls b‖ ^ 2) +
        (‖T.toDiffusionTriple.cls a + T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a + T.toDiffusionTriple.Lcls b‖ ^ 2) / l) / 4 := by
  unfold G1
  rw [dist_toL1]
  have h := int_G_diff_le (T := T) a.2 b.2 hl
  have hp := eG_le (T := T) ⟨_, sub_memA₀ a.2 b.2⟩
  have hq := eG_le (T := T) ⟨_, add_memA₀ a.2 b.2⟩
  unfold graphSq at hp hq
  rw [cls_sub, Lcls_sub] at hp
  rw [cls_add, Lcls_add] at hq
  have hq0 : (∫ x, G T (fun x => a.1 x + 1 * b.1 x) (fun x => a.1 x + 1 * b.1 x) x ∂T.μ) / l ≤
      ((‖T.toDiffusionTriple.cls a + T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a + T.toDiffusionTriple.Lcls b‖ ^ 2) / 2) / l :=
    div_le_div_of_nonneg_right hq hl.le
  have hp0 : l * (∫ x, G T (fun x => a.1 x + (-1) * b.1 x) (fun x => a.1 x + (-1) * b.1 x) x ∂T.μ) ≤
      l * ((‖T.toDiffusionTriple.cls a - T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a - T.toDiffusionTriple.Lcls b‖ ^ 2) / 2) :=
    mul_le_mul_of_nonneg_left hp hl.le
  refine h.trans ?_
  have : ((‖T.toDiffusionTriple.cls a + T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a + T.toDiffusionTriple.Lcls b‖ ^ 2) / 2) / l =
      ((‖T.toDiffusionTriple.cls a + T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a + T.toDiffusionTriple.Lcls b‖ ^ 2) / l) / 2 := by ring
  linarith

lemma dist_K1_le (ρ : ℝ) {n : ℝ≥0∞} (hCD : T.CD ρ n) (a b : T.A₀) {l : ℝ} (hl : 0 < l) :
    dist (K1cls T ρ a) (K1cls T ρ b) ≤ (1 + |ρ|) *
      (l * (‖T.toDiffusionTriple.cls a - T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a - T.toDiffusionTriple.Lcls b‖ ^ 2) +
        (‖T.toDiffusionTriple.cls a + T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a + T.toDiffusionTriple.Lcls b‖ ^ 2) / l) / 2 := by
  unfold K1cls
  rw [dist_toL1]
  have h := int_Kf_diff_le (T := T) hCD a.2 b.2 hl
  have hp := eK_le (T := T) ρ ⟨_, sub_memA₀ a.2 b.2⟩
  have hq := eK_le (T := T) ρ ⟨_, add_memA₀ a.2 b.2⟩
  unfold graphSq at hp hq
  rw [cls_sub, Lcls_sub] at hp
  rw [cls_add, Lcls_add] at hq
  have hc : 0 ≤ 1 + |ρ| := by positivity
  have hq0 := div_le_div_of_nonneg_right hq hl.le
  have hp0 := mul_le_mul_of_nonneg_left hp hl.le
  refine h.trans ?_
  have e1 : (1 + |ρ|) * (‖T.toDiffusionTriple.cls a + T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a + T.toDiffusionTriple.Lcls b‖ ^ 2) / l =
      (1 + |ρ|) * ((‖T.toDiffusionTriple.cls a + T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a + T.toDiffusionTriple.Lcls b‖ ^ 2) / l) := by ring
  rw [e1] at hq0
  have e2 : l * ((1 + |ρ|) * (‖T.toDiffusionTriple.cls a - T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a - T.toDiffusionTriple.Lcls b‖ ^ 2)) =
      (1 + |ρ|) * (l * (‖T.toDiffusionTriple.cls a - T.toDiffusionTriple.cls b‖ ^ 2 +
          ‖T.toDiffusionTriple.Lcls a - T.toDiffusionTriple.Lcls b‖ ^ 2)) := by ring
  rw [e2] at hp0
  nlinarith [hp0, hq0]

/-- the `L¹`-class of `Γ₂(a)`. -/
noncomputable def G2cls (T : FullTriple E) (a : T.A₀) : Lp ℝ 1 T.μ :=
  (integrable_A₀ (Γ₂_memA₀ a.2)).toL1 _

lemma G2cls_eq (ρ : ℝ) (a : T.A₀) : G2cls T a = K1cls T ρ a + ρ • G1 T a := by
  refine Lp.ext ?_
  filter_upwards [Integrable.coeFn_toL1 (integrable_A₀ (Γ₂_memA₀ a.2)),
    Lp.coeFn_add (K1cls T ρ a) (ρ • G1 T a), Lp.coeFn_smul ρ (G1 T a),
    Integrable.coeFn_toL1 (integrable_A₀ (Kf_memA₀ ρ a.2)),
    Integrable.coeFn_toL1 (integrable_A₀ (T.ΓA_self_mem_A₀ a.2))] with x h1 h2 h3 h4 h5
  unfold G2cls
  rw [h1, h2, Pi.add_apply, h3, Pi.smul_apply]
  unfold K1cls G1
  rw [h4, h5]
  simp only [Kf, smul_eq_mul]; ring

lemma tendsto_zero_of_amgm (d P Q : ℕ → ℝ) (S c : ℝ) (hc : 0 ≤ c) (hS : 0 ≤ S)
    (hP : Tendsto P atTop (𝓝 0)) (hP0 : ∀ k, 0 ≤ P k) (hQ : ∀ k, Q k ≤ S) (hd0 : ∀ k, 0 ≤ d k)
    (h : ∀ k, ∀ l : ℝ, 0 < l → d k ≤ (l * P k + Q k / l) * c) : Tendsto d atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨l, δ, hl, hδ, hsm⟩ := exists_small ε S c hε hS hc
  have := (Metric.tendsto_atTop.1 hP) δ hδ
  obtain ⟨N, hN⟩ := this
  refine ⟨N, fun n hn => ?_⟩
  have hPn : P n < δ := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hP0 n)] at this
    exact this
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hd0 n)]
  exact (h n l hl).trans_lt (hsm _ _ (hP0 n) hPn (hQ n))

lemma cauchy_of_amgm {X : Type*} [PseudoMetricSpace X] (s : ℕ → X) (P Q : ℕ → ℕ → ℝ) (S c : ℝ)
    (hc : 0 ≤ c) (hS : 0 ≤ S) (hP : ∀ δ : ℝ, 0 < δ → ∃ N, ∀ m ≥ N, ∀ n ≥ N, P m n < δ)
    (hP0 : ∀ m n, 0 ≤ P m n) (hQ : ∀ m n, Q m n ≤ S)
    (h : ∀ m n, ∀ l : ℝ, 0 < l → dist (s m) (s n) ≤ (l * P m n + Q m n / l) * c) : CauchySeq s := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨l, δ, hl, hδ, hsm⟩ := exists_small ε S c hε hS hc
  obtain ⟨N, hN⟩ := hP δ hδ
  exact ⟨N, fun m hm n hn => (h m n l hl).trans_lt (hsm _ _ (hP0 m n) (hN m hm n hn) (hQ m n))⟩

lemma P_small {H : Type*} [NormedAddCommGroup H] {u v : ℕ → H} (hu : CauchySeq u) (hv : CauchySeq v)
    (δ : ℝ) (hδ : 0 < δ) : ∃ N, ∀ m ≥ N, ∀ n ≥ N, ‖u m - u n‖ ^ 2 + ‖v m - v n‖ ^ 2 < δ := by
  set η := Real.sqrt (δ / 2) with hη
  have hηpos : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hη2 : η ^ 2 = δ / 2 := Real.sq_sqrt (by positivity)
  obtain ⟨N1, h1⟩ := Metric.cauchySeq_iff.1 hu η hηpos
  obtain ⟨N2, h2⟩ := Metric.cauchySeq_iff.1 hv η hηpos
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have a1 := h1 m (le_trans (le_max_left _ _) hm) n (le_trans (le_max_left _ _) hn)
  have a2 := h2 m (le_trans (le_max_right _ _) hm) n (le_trans (le_max_right _ _) hn)
  rw [dist_eq_norm] at a1 a2
  have b1 : ‖u m - u n‖ ^ 2 < η ^ 2 := pow_lt_pow_left₀ a1 (norm_nonneg _) (by norm_num)
  have b2 : ‖v m - v n‖ ^ 2 < η ^ 2 := pow_lt_pow_left₀ a2 (norm_nonneg _) (by norm_num)
  linarith

lemma bdd_sq {H : Type*} [NormedAddCommGroup H] {u : ℕ → H} {U : H} (hu : Tendsto u atTop (𝓝 U)) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ k, ‖u k‖ ≤ R := by
  obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le).1 (Metric.isBounded_range_of_tendsto u hu)
  exact ⟨max R 0, le_max_right _ _, fun k => (hR _ ⟨k, rfl⟩).trans (le_max_left _ _)⟩

/-- Cauchy-ness of `Γ(a_k)`, `K(a_k)` in `L¹` along graph-Cauchy sequences. -/
theorem cauchy_G1_K1 {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (a : ℕ → T.A₀) {U V : Lp ℝ 2 T.μ}
    (hu : Tendsto (fun k => T.toDiffusionTriple.cls (a k)) atTop (𝓝 U))
    (hv : Tendsto (fun k => T.toDiffusionTriple.Lcls (a k)) atTop (𝓝 V)) :
    CauchySeq (fun k => G1 T (a k)) ∧ CauchySeq (fun k => K1cls T ρ (a k)) := by
  obtain ⟨Ru, hRu0, hRu⟩ := bdd_sq hu
  obtain ⟨Rv, hRv0, hRv⟩ := bdd_sq hv
  set S : ℝ := (2 * Ru) ^ 2 + (2 * Rv) ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hQ : ∀ m n, ‖T.toDiffusionTriple.cls (a m) + T.toDiffusionTriple.cls (a n)‖ ^ 2 +
      ‖T.toDiffusionTriple.Lcls (a m) + T.toDiffusionTriple.Lcls (a n)‖ ^ 2 ≤ S := by
    intro m n
    have h1 : ‖T.toDiffusionTriple.cls (a m) + T.toDiffusionTriple.cls (a n)‖ ≤ 2 * Ru :=
      (norm_add_le _ _).trans (by linarith [hRu m, hRu n])
    have h2 : ‖T.toDiffusionTriple.Lcls (a m) + T.toDiffusionTriple.Lcls (a n)‖ ≤ 2 * Rv :=
      (norm_add_le _ _).trans (by linarith [hRv m, hRv n])
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    linarith
  have hP := fun δ hδ => P_small hu.cauchySeq hv.cauchySeq δ hδ
  have hP0 : ∀ m n, 0 ≤ ‖T.toDiffusionTriple.cls (a m) - T.toDiffusionTriple.cls (a n)‖ ^ 2 +
      ‖T.toDiffusionTriple.Lcls (a m) - T.toDiffusionTriple.Lcls (a n)‖ ^ 2 := fun m n => by positivity
  constructor
  · refine cauchy_of_amgm (fun k => G1 T (a k)) _ _ S (1 / 4) (by norm_num) hS0 hP hP0 hQ
      (fun m n l hl => ?_)
    have := dist_G1_le (a m) (a n) hl
    simpa [mul_comm, div_eq_mul_inv, mul_assoc, mul_left_comm] using this
  · refine cauchy_of_amgm (fun k => K1cls T ρ (a k)) _ _ S ((1 + |ρ|) / 2) (by positivity) hS0 hP hP0 hQ
      (fun m n l hl => ?_)
    have := dist_K1_le ρ hCD (a m) (a n) hl
    refine this.trans (le_of_eq ?_)
    ring

/-- the `L¹`-class of `w²`, `w ∈ L²`. -/
noncomputable def Sq (w : Lp ℝ 2 T.μ) : Lp ℝ 1 T.μ := (Lp.memLp w).integrable_sq.toL1 _

lemma tendsto_Sq {w : ℕ → Lp ℝ 2 T.μ} {W : Lp ℝ 2 T.μ} (hw : Tendsto w atTop (𝓝 W)) :
    Tendsto (fun k => Sq (w k)) atTop (𝓝 (Sq W)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  obtain ⟨R, hR0, hR⟩ := bdd_sq hw
  have hRW : ‖W‖ ≤ R + ‖W‖ := by linarith
  refine tendsto_zero_of_amgm _ (fun k => ‖w k - W‖ ^ 2) (fun k => ‖w k + W‖ ^ 2) ((R + ‖W‖) ^ 2) (1 / 2)
    (by norm_num) (by positivity) ?_ (fun k => by positivity) (fun k => ?_) (fun k => dist_nonneg)
    (fun k l hl => ?_)
  · have h1 := (tendsto_iff_norm_sub_tendsto_zero.1 hw)
    have := h1.pow 2
    simpa using this
  · exact pow_le_pow_left₀ (norm_nonneg _) ((norm_add_le _ _).trans (by linarith [hR k])) 2
  · unfold Sq
    rw [dist_toL1]
    have i1 := (Lp.memLp (w k)).integrable_sq
    have i2 := (Lp.memLp W).integrable_sq
    have i3 := (Lp.memLp (w k - W)).integrable_sq
    have i4 := (Lp.memLp (w k + W)).integrable_sq
    have e1 : ∫ x, ((w k - W : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ = ‖w k - W‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
      refine integral_congr_ae (Eventually.of_forall fun x => by simp [sq])
    have e2 : ∫ x, ((w k + W : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ = ‖w k + W‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
      refine integral_congr_ae (Eventually.of_forall fun x => by simp [sq])
    have iR : Integrable (fun x => (l * ((w k - W : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 +
        ((w k + W : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 / l) / 2) T.μ :=
      ((i3.const_mul l).add (i4.div_const l)).div_const 2
    have iL : Integrable (fun x => |((w k : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 -
        ((W : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2|) T.μ := (i1.sub i2).abs
    have hle : ∀ᵐ x ∂T.μ, |((w k : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 - ((W : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2| ≤
        (l * ((w k - W : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 + ((w k + W : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 / l) / 2 := by
      filter_upwards [Lp.coeFn_sub (w k) W, Lp.coeFn_add (w k) W] with x h1 h2
      rw [h1, h2]
      simp only [Pi.sub_apply, Pi.add_apply]
      generalize ((w k : Lp ℝ 2 T.μ) : E → ℝ) x = a
      generalize ((W : Lp ℝ 2 T.μ) : E → ℝ) x = b
      have := two_abs_le (c := a ^ 2 - b ^ 2) (x := (a - b) ^ 2) (y := (a + b) ^ 2) (l := l)
        (sq_nonneg _) (sq_nonneg _) hl (by nlinarith [sq_nonneg a, sq_nonneg b])
      linarith
    have hint := integral_mono_ae iL iR hle
    rw [integral_div, integral_add (i3.const_mul l) (i4.div_const l), integral_const_mul,
      integral_div, e1, e2] at hint
    linarith

/-- two graph-convergent sequences with the same limits have asymptotically equal `Γ`, `K`. -/
theorem cross_G1_K1 {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {a a' : ℕ → T.A₀} {U V : Lp ℝ 2 T.μ}
    (hu : Tendsto (fun k => T.toDiffusionTriple.cls (a k)) atTop (𝓝 U))
    (hv : Tendsto (fun k => T.toDiffusionTriple.Lcls (a k)) atTop (𝓝 V))
    (hu' : Tendsto (fun k => T.toDiffusionTriple.cls (a' k)) atTop (𝓝 U))
    (hv' : Tendsto (fun k => T.toDiffusionTriple.Lcls (a' k)) atTop (𝓝 V)) :
    Tendsto (fun k => dist (G1 T (a k)) (G1 T (a' k))) atTop (𝓝 0) ∧
      Tendsto (fun k => dist (K1cls T ρ (a k)) (K1cls T ρ (a' k))) atTop (𝓝 0) := by
  obtain ⟨Ru, hRu0, hRu⟩ := bdd_sq hu
  obtain ⟨Rv, hRv0, hRv⟩ := bdd_sq hv
  obtain ⟨Ru', hRu0', hRu'⟩ := bdd_sq hu'
  obtain ⟨Rv', hRv0', hRv'⟩ := bdd_sq hv'
  set S : ℝ := (Ru + Ru') ^ 2 + (Rv + Rv') ^ 2 with hS
  have hS0 : 0 ≤ S := by positivity
  have hQ : ∀ k, ‖T.toDiffusionTriple.cls (a k) + T.toDiffusionTriple.cls (a' k)‖ ^ 2 +
      ‖T.toDiffusionTriple.Lcls (a k) + T.toDiffusionTriple.Lcls (a' k)‖ ^ 2 ≤ S := by
    intro k
    have h1 : ‖T.toDiffusionTriple.cls (a k) + T.toDiffusionTriple.cls (a' k)‖ ≤ Ru + Ru' :=
      (norm_add_le _ _).trans (by linarith [hRu k, hRu' k])
    have h2 : ‖T.toDiffusionTriple.Lcls (a k) + T.toDiffusionTriple.Lcls (a' k)‖ ≤ Rv + Rv' :=
      (norm_add_le _ _).trans (by linarith [hRv k, hRv' k])
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have := pow_le_pow_left₀ (norm_nonneg _) h2 2
    linarith
  have hP : Tendsto (fun k => ‖T.toDiffusionTriple.cls (a k) - T.toDiffusionTriple.cls (a' k)‖ ^ 2 +
      ‖T.toDiffusionTriple.Lcls (a k) - T.toDiffusionTriple.Lcls (a' k)‖ ^ 2) atTop (𝓝 0) := by
    have h1 := ((hu.sub hu').norm).pow 2
    have h2 := ((hv.sub hv').norm).pow 2
    simpa using h1.add h2
  have hP0 : ∀ k, 0 ≤ ‖T.toDiffusionTriple.cls (a k) - T.toDiffusionTriple.cls (a' k)‖ ^ 2 +
      ‖T.toDiffusionTriple.Lcls (a k) - T.toDiffusionTriple.Lcls (a' k)‖ ^ 2 := fun k => by positivity
  constructor
  · refine tendsto_zero_of_amgm _ _ _ S (1 / 4) (by norm_num) hS0 hP hP0 hQ (fun k => dist_nonneg)
      (fun k l hl => ?_)
    have := dist_G1_le (a k) (a' k) hl
    simpa [mul_comm, div_eq_mul_inv, mul_assoc, mul_left_comm] using this
  · refine tendsto_zero_of_amgm _ _ _ S ((1 + |ρ|) / 2) (by positivity) hS0 hP hP0 hQ
      (fun k => dist_nonneg) (fun k l hl => ?_)
    have := dist_K1_le ρ hCD (a k) (a' k) hl
    refine this.trans (le_of_eq ?_)
    ring

lemma int_G2cls (a : T.A₀) : ∫ x, (G2cls T a : E → ℝ) x ∂T.μ = ‖T.toDiffusionTriple.Lcls a‖ ^ 2 := by
  have h1 : ∫ x, (G2cls T a : E → ℝ) x ∂T.μ = ∫ x, T.toDiffusionTriple.Γ₂ a.1 a.1 x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [Integrable.coeFn_toL1 (integrable_A₀ (Γ₂_memA₀ a.2))] with x hx
    unfold G2cls; rw [hx]
  rw [h1, integral_Γ₂ T a.2, Lcls_eq_cls, ← real_inner_self_eq_norm_sq, L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple ⟨T.L a.1, T.L_mem a.1 a.2⟩] with x hx
  rw [hx]

lemma int_G1 (a : T.A₀) : ∫ x, (G1 T a : E → ℝ) x ∂T.μ =
    -inner ℝ (T.toDiffusionTriple.cls a) (T.toDiffusionTriple.Lcls a) := by
  have h1 : ∫ x, (G1 T a : E → ℝ) x ∂T.μ = ∫ x, G T a.1 a.1 x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [Integrable.coeFn_toL1 (integrable_A₀ (T.ΓA_self_mem_A₀ a.2))] with x hx
    unfold G1; rw [hx]
  rw [h1, int_G_self a.2, L2_inner_eq]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple a,
    DiffusionTriple.coeFn_Lcls T.toDiffusionTriple a] with x h1 h2
  rw [h1, h2]

/-- **BGL Prop. 3.3.16 (i)–(iii) (operator level, `Γ` and `Γ₂`).**  Under `CD(ρ,n)` and ESA, `Γ` and `Γ₂`
extend to `𝒟(L)` as `L¹`-valued maps, as `L¹`-limits along any graph-convergent sequence of test
functions; `∫Γ₂(u) = ‖Lu‖²` (3.3.8), `∫Γ(u) = −⟪Lu,u⟫`, and `CD(ρ,n)` extends:
`Γ₂(u) ≥ ρΓ(u) + n⁻¹ (Lu)²` a.e. -/
theorem gamma_limits {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) :
    ∃ γ₁ γ₂ : Lp ℝ 1 T.μ,
      (∀ a : ℕ → T.A₀, Tendsto (fun k => T.toDiffusionTriple.cls (a k)) atTop (𝓝 u) →
        Tendsto (fun k => T.toDiffusionTriple.Lcls (a k)) atTop
          (𝓝 (T.toDiffusionTriple.generator ⟨u, hu⟩)) →
        Tendsto (fun k => G1 T (a k)) atTop (𝓝 γ₁) ∧
          Tendsto (fun k => G2cls T (a k)) atTop (𝓝 γ₂)) ∧
      (∃ a : ℕ → T.A₀, Tendsto (fun k => T.toDiffusionTriple.cls (a k)) atTop (𝓝 u) ∧
        Tendsto (fun k => T.toDiffusionTriple.Lcls (a k)) atTop
          (𝓝 (T.toDiffusionTriple.generator ⟨u, hu⟩))) ∧
      ∫ x, (γ₂ : E → ℝ) x ∂T.μ = ‖T.toDiffusionTriple.generator ⟨u, hu⟩‖ ^ 2 ∧
      ∫ x, (γ₁ : E → ℝ) x ∂T.μ = -inner ℝ (T.toDiffusionTriple.generator ⟨u, hu⟩) u ∧
      ρ • γ₁ + (n⁻¹).toReal • Sq (T.toDiffusionTriple.generator ⟨u, hu⟩) ≤ γ₂ := by
  set V := T.toDiffusionTriple.generator ⟨u, hu⟩ with hV
  obtain ⟨a0, h0u, h0v⟩ := T.esa u hu
  obtain ⟨c1, c2⟩ := cauchy_G1_K1 hCD a0 h0u h0v
  obtain ⟨γ₁, hγ₁⟩ := cauchySeq_tendsto_of_complete c1
  obtain ⟨κ, hκ⟩ := cauchySeq_tendsto_of_complete c2
  have hγ₂ : Tendsto (fun k => G2cls T (a0 k)) atTop (𝓝 (κ + ρ • γ₁)) := by
    have := hκ.add (hγ₁.const_smul ρ)
    refine this.congr (fun k => ?_)
    rw [G2cls_eq ρ]
  refine ⟨γ₁, κ + ρ • γ₁, ?_, ⟨a0, h0u, h0v⟩, ?_, ?_, ?_⟩
  · intro a hau hav
    obtain ⟨d1, d2⟩ := cross_G1_K1 hCD hau hav h0u h0v
    have e1 : Tendsto (fun k => G1 T (a k)) atTop (𝓝 γ₁) := by
      refine tendsto_iff_dist_tendsto_zero.2 ?_
      refine squeeze_zero (fun k => dist_nonneg) (fun k => dist_triangle _ (G1 T (a0 k)) _) ?_
      have := d1.add (tendsto_iff_dist_tendsto_zero.1 hγ₁)
      simpa using this
    have e2 : Tendsto (fun k => K1cls T ρ (a k)) atTop (𝓝 κ) := by
      refine tendsto_iff_dist_tendsto_zero.2 ?_
      refine squeeze_zero (fun k => dist_nonneg) (fun k => dist_triangle _ (K1cls T ρ (a0 k)) _) ?_
      have := d2.add (tendsto_iff_dist_tendsto_zero.1 hκ)
      simpa using this
    refine ⟨e1, ?_⟩
    have := e2.add (e1.const_smul ρ)
    exact this.congr (fun k => (G2cls_eq ρ (a k)).symm)
  · -- ∫ γ₂
    have h1 : Tendsto (fun k => ∫ x, (G2cls T (a0 k) : E → ℝ) x ∂T.μ) atTop
        (𝓝 (∫ x, ((κ + ρ • γ₁ : Lp ℝ 1 T.μ) : E → ℝ) x ∂T.μ)) :=
      ((MeasureTheory.continuous_integral (μ := T.μ) (G := ℝ)).tendsto _).comp hγ₂
    have h2 : Tendsto (fun k => ∫ x, (G2cls T (a0 k) : E → ℝ) x ∂T.μ) atTop (𝓝 (‖V‖ ^ 2)) := by
      simp only [int_G2cls]
      exact (h0v.norm).pow 2
    exact tendsto_nhds_unique h1 h2
  · have h1 : Tendsto (fun k => ∫ x, (G1 T (a0 k) : E → ℝ) x ∂T.μ) atTop
        (𝓝 (∫ x, (γ₁ : E → ℝ) x ∂T.μ)) :=
      ((MeasureTheory.continuous_integral (μ := T.μ) (G := ℝ)).tendsto _).comp hγ₁
    have h2 : Tendsto (fun k => ∫ x, (G1 T (a0 k) : E → ℝ) x ∂T.μ) atTop
        (𝓝 (-inner ℝ u V)) := by
      simp only [int_G1]
      exact (h0u.inner h0v).neg
    rw [real_inner_comm]
    exact tendsto_nhds_unique h1 h2
  · have hS := tendsto_Sq (T := T) h0v
    have hL := (hγ₁.const_smul ρ).add (hS.const_smul ((n⁻¹).toReal))
    refine le_of_tendsto_of_tendsto' hL hγ₂ (fun k => ?_)
    rw [← Lp.coeFn_le]
    have hk := hCD.2 (a0 k).1 (A₀_memA (a0 k).2)
    filter_upwards [Lp.coeFn_add (ρ • G1 T (a0 k)) ((n⁻¹).toReal • Sq (T.toDiffusionTriple.Lcls (a0 k))),
      Lp.coeFn_smul ρ (G1 T (a0 k)),
      Lp.coeFn_smul ((n⁻¹).toReal) (Sq (T.toDiffusionTriple.Lcls (a0 k))),
      Integrable.coeFn_toL1 (integrable_A₀ (T.ΓA_self_mem_A₀ (a0 k).2)),
      Integrable.coeFn_toL1 (Lp.memLp (T.toDiffusionTriple.Lcls (a0 k))).integrable_sq,
      Integrable.coeFn_toL1 (integrable_A₀ (Γ₂_memA₀ (a0 k).2)),
      DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (a0 k), hk] with x h1 h2 h3 h4 h5 h6 h7 h8
    rw [h1, Pi.add_apply, h2, h3, Pi.smul_apply, Pi.smul_apply]
    unfold G1 Sq G2cls
    rw [h4, h5, h6, h7]
    simp only [smul_eq_mul]
    exact h8

end FullTriple

end MarkovTriple.BGL

#print axioms MarkovTriple.BGL.FullTriple.gamma_limits
