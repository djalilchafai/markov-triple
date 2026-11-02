import Mathlib
import MarkovTriple.BGL.Theory.Extension.Estimates

/-!
# Extension of `Γ` and `Γ₂` to `𝒟(L)` as `L¹`-valued maps (BGL Prop. 3.3.16 (i)–(iii), operator level)

Under `CD(ρ,n)` and ESA (field F10 of `FullTriple`): for every `u ∈ 𝒟(L)` there are `γ₁ = Γ(u)`,
`γ₂ = Γ₂(u) ∈ L¹(μ)` such that `Γ(a_k) → γ₁` and `Γ₂(a_k) → γ₂` in `L¹` for **every** sequence
`a_k ∈ 𝒜₀` with `a_k → u`, `L a_k → L u` in `L²` (graph convergence), together with
`∫ γ₂ = ‖Lu‖²` (3.3.8 on `𝒟(L)`), `∫ γ₁ = −⟪Lu,u⟫`, and the extended curvature inequality
`γ₂ ≥ ρ γ₁ + n⁻¹ (Lu)²` a.e. (Prop. 3.3.16 (ii)).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace LinearPMap

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

lemma exists_small (ε S c : ℝ) (hε : 0 < ε) (hS : 0 ≤ S) (hc : 0 ≤ c) :
    ∃ l δ : ℝ, 0 < l ∧ 0 < δ ∧ ∀ P Q : ℝ, 0 ≤ P → P < δ → Q ≤ S → (l * P + Q / l) * c < ε := by
  set l : ℝ := 4 * c * S / ε + 1 with hl
  have hlpos : 0 < l := by positivity
  set δ : ℝ := ε / (4 * (l * c + 1)) with hδ
  have hlc : 0 ≤ l * c := by positivity
  have hδpos : 0 < δ := by positivity
  refine ⟨l, δ, hlpos, hδpos, fun P Q hP hPδ hQ => ?_⟩
  have h1 : l * P * c ≤ ε / 4 := by
    have : l * P * c ≤ l * c * δ := by nlinarith [mul_le_mul_of_nonneg_left hPδ.le hlc]
    refine this.trans ?_
    rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h2 : Q / l * c ≤ ε / 4 := by
    have hSl : S * c ≤ (ε / 4) * l := by
      have : 4 * c * S / ε ≤ l := by rw [hl]; linarith
      rw [div_le_iff₀ hε] at this
      nlinarith
    calc Q / l * c = Q * c / l := by ring
      _ ≤ S * c / l := by
          apply div_le_div_of_nonneg_right _ hlpos.le
          exact mul_le_mul_of_nonneg_right hQ hc
      _ ≤ ε / 4 := by rw [div_le_iff₀ hlpos]; linarith
  calc (l * P + Q / l) * c = l * P * c + Q / l * c := by ring
    _ < ε := by linarith

namespace FullTriple

variable {T : FullTriple E}

/-- the `L¹`-class of `Γ(a)`. -/
noncomputable def G1 (T : FullTriple E) (a : T.A₀) : Lp ℝ 1 T.μ :=
  (integrable_A₀ (T.ΓA_self_mem_A₀ a.2)).toL1 _

/-- the `L¹`-class of `K(a) = Γ₂(a) − ρΓ(a)`. -/
noncomputable def K1cls (T : FullTriple E) (ρ : ℝ) (a : T.A₀) : Lp ℝ 1 T.μ :=
  (integrable_A₀ (Kf_memA₀ ρ a.2)).toL1 _

lemma dist_toL1 {f g : E → ℝ} (hf : Integrable f T.μ) (hg : Integrable g T.μ) :
    dist (hf.toL1 f) (hg.toL1 g) = ∫ x, |f x - g x| ∂T.μ := by
  rw [dist_eq_norm, ← Integrable.toL1_sub f g hf hg, L1.norm_eq_integral_norm]
  refine integral_congr_ae ?_
  filter_upwards [Integrable.coeFn_toL1 (hf.sub hg)] with x hx
  rw [hx]; simp [Real.norm_eq_abs]

/-- `‖cls w‖² + ‖L w‖²` (graph norm squared) of a test function. -/
noncomputable def graphSq (T : FullTriple E) (w : T.A₀) : ℝ :=
  ‖T.toDiffusionTriple.cls w‖ ^ 2 + ‖T.toDiffusionTriple.Lcls w‖ ^ 2

lemma cls_sub (a b : T.A₀) :
    T.toDiffusionTriple.cls ⟨fun x => a.1 x + (-1) * b.1 x, sub_memA₀ a.2 b.2⟩ =
      T.toDiffusionTriple.cls a - T.toDiffusionTriple.cls b := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple
    ⟨fun x => a.1 x + (-1) * b.1 x, sub_memA₀ a.2 b.2⟩, DiffusionTriple.coeFn_cls T.toDiffusionTriple a,
    DiffusionTriple.coeFn_cls T.toDiffusionTriple b,
    Lp.coeFn_sub (T.toDiffusionTriple.cls a) (T.toDiffusionTriple.cls b)] with x h1 h2 h3 h4
  rw [h4, Pi.sub_apply, h2, h3]; rw [h1]; ring

lemma cls_add (a b : T.A₀) :
    T.toDiffusionTriple.cls ⟨fun x => a.1 x + 1 * b.1 x, add_memA₀ a.2 b.2⟩ =
      T.toDiffusionTriple.cls a + T.toDiffusionTriple.cls b := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple
    ⟨fun x => a.1 x + 1 * b.1 x, add_memA₀ a.2 b.2⟩, DiffusionTriple.coeFn_cls T.toDiffusionTriple a,
    DiffusionTriple.coeFn_cls T.toDiffusionTriple b,
    Lp.coeFn_add (T.toDiffusionTriple.cls a) (T.toDiffusionTriple.cls b)] with x h1 h2 h3 h4
  rw [h4, Pi.add_apply, h2, h3]; rw [h1]; ring

lemma Lcls_sub (a b : T.A₀) :
    T.toDiffusionTriple.Lcls ⟨fun x => a.1 x + (-1) * b.1 x, sub_memA₀ a.2 b.2⟩ =
      T.toDiffusionTriple.Lcls a - T.toDiffusionTriple.Lcls b := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple
    ⟨fun x => a.1 x + (-1) * b.1 x, sub_memA₀ a.2 b.2⟩, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple a,
    DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b,
    Lp.coeFn_sub (T.toDiffusionTriple.Lcls a) (T.toDiffusionTriple.Lcls b),
    L_lin (T := T) (A₀_memA a.2) (A₀_memA b.2) (-1)] with x h1 h2 h3 h4 h5
  rw [h4, Pi.sub_apply, h2, h3, h1]
  show T.L (fun x => a.1 x + (-1) * b.1 x) x = _
  linarith [h5]

lemma Lcls_add (a b : T.A₀) :
    T.toDiffusionTriple.Lcls ⟨fun x => a.1 x + 1 * b.1 x, add_memA₀ a.2 b.2⟩ =
      T.toDiffusionTriple.Lcls a + T.toDiffusionTriple.Lcls b := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple
    ⟨fun x => a.1 x + 1 * b.1 x, add_memA₀ a.2 b.2⟩, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple a,
    DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b,
    Lp.coeFn_add (T.toDiffusionTriple.Lcls a) (T.toDiffusionTriple.Lcls b),
    L_lin (T := T) (A₀_memA a.2) (A₀_memA b.2) 1] with x h1 h2 h3 h4 h5
  rw [h4, Pi.add_apply, h2, h3, h1]
  show T.L (fun x => a.1 x + 1 * b.1 x) x = _
  linarith [h5]

lemma Lcls_eq_cls (w : T.A₀) :
    T.toDiffusionTriple.Lcls w = T.toDiffusionTriple.cls ⟨T.L w.1, T.L_mem w.1 w.2⟩ := by
  refine Lp.ext ?_
  filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple w,
    DiffusionTriple.coeFn_cls T.toDiffusionTriple ⟨T.L w.1, T.L_mem w.1 w.2⟩] with x h1 h2
  rw [h1, h2]

lemma eG_le (w : T.A₀) : ∫ x, G T w.1 w.1 x ∂T.μ ≤ graphSq T w / 2 := by
  have h := int_G_self_le (T := T) w.2
  have e := Lcls_eq_cls w
  unfold graphSq
  rw [e]
  nlinarith [sq_nonneg (‖T.toDiffusionTriple.cls w‖ - ‖T.toDiffusionTriple.cls ⟨T.L w.1, T.L_mem w.1 w.2⟩‖)]

lemma eG_nonneg (w : T.A₀) : 0 ≤ ∫ x, G T w.1 w.1 x ∂T.μ :=
  integral_nonneg_of_ae (T.ΓA_nonneg w.1 (A₀_memA w.2))

lemma eK_le (ρ : ℝ) (w : T.A₀) :
    ∫ x, Kf T ρ w.1 w.1 x ∂T.μ ≤ (1 + |ρ|) * graphSq T w := by
  have h2 : ∫ x, T.toDiffusionTriple.Γ₂ w.1 w.1 x ∂T.μ = ‖T.toDiffusionTriple.Lcls w‖ ^ 2 := by
    rw [integral_Γ₂ T w.2, Lcls_eq_cls, ← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple ⟨T.L w.1, T.L_mem w.1 w.2⟩] with x hx
    rw [hx]
  have hK : ∫ x, Kf T ρ w.1 w.1 x ∂T.μ =
      ∫ x, T.toDiffusionTriple.Γ₂ w.1 w.1 x ∂T.μ - ρ * ∫ x, G T w.1 w.1 x ∂T.μ := by
    have i1 := integrable_A₀ (Γ₂_memA₀ w.2)
    have i2 := integrable_A₀ (T.ΓA_self_mem_A₀ w.2)
    simp only [Kf]
    rw [integral_sub i1 (i2.const_mul ρ), integral_const_mul]
  rw [hK, h2]
  have e0 := eG_nonneg w
  have e1 := eG_le w
  have n1 : 0 ≤ ‖T.toDiffusionTriple.cls w‖ ^ 2 := by positivity
  have n2 : 0 ≤ ‖T.toDiffusionTriple.Lcls w‖ ^ 2 := by positivity
  unfold graphSq at e1 ⊢
  have : -ρ * ∫ x, G T w.1 w.1 x ∂T.μ ≤ |ρ| * ∫ x, G T w.1 w.1 x ∂T.μ := by
    nlinarith [neg_abs_le ρ, le_abs_self ρ, mul_nonneg (abs_nonneg ρ) e0]
  have hb := mul_le_mul_of_nonneg_left e1 (abs_nonneg ρ)
  nlinarith [hb, this, mul_nonneg (abs_nonneg ρ) n1, mul_nonneg (abs_nonneg ρ) n2]

end FullTriple

end MarkovTriple.BGL
