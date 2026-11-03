import Mathlib
import MarkovTriple.BGL.Theory.Extension.HessL2
import MarkovTriple.BGL.Theory.Extension.Gamma2Ident

/-!
# The bilinear `Γ₂` on `𝒟(L) × 𝒟(L)` (BGL Prop. 3.3.16 (i)–(iii) and (vii), p. 160)

The book extends the bilinear `Γ₂` (Def. 3.3.12) to `𝒟(L)` by "the same procedure" as `Γ` on `𝒟(ℰ)`: continuity from the positive
form `K = Γ₂ − ρΓ` and `∫ Γ₂(f) = ∫(Lf)²`.  Here `GG2 a b = [Γ₂(a,b)] ∈ L¹` for `a, b ∈ 𝒜₀`, bounded for the graph norms
(`GG2_bound`, via `|K(a,b)|² ≤ K(a)K(b)` and `K = Γ₂ − ρΓ`), and `gamma2E u v` is the `L¹`-limit along graph-convergent sequences.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma Γ₂_bil_memA₀ {a b : E → ℝ} (ha : a ∈ T.A₀) (hb : b ∈ T.A₀) : T.toDiffusionTriple.Γ₂ a b ∈ T.A₀ := by
  have h1 := T.L_mem _ (G_memA₀ (A₀_memA ha) hb)
  have h2 := G_memA₀ (A₀_memA ha) (T.L_mem b hb)
  have h3 := G_memA₀ (A₀_memA (T.L_mem a ha)) hb
  have : T.toDiffusionTriple.Γ₂ a b = (1 / 2 : ℝ) • (T.L (G T a b) - G T a (T.L b) - G T (T.L a) b) := by
    funext x
    simp only [DiffusionTriple.Γ₂, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, G]
    ring
  rw [this]
  exact T.A₀.smul_mem _ (T.A₀.sub_mem (T.A₀.sub_mem h1 h2) h3)

/-- the `L¹`-class of `Γ₂(a,b)`. -/
noncomputable def GG2 (T : FullTriple E) (a b : T.A₀) : Lp ℝ 1 T.μ :=
  (integrable_A₀ (Γ₂_bil_memA₀ a.2 b.2)).toL1 (T.toDiffusionTriple.Γ₂ a.1 b.1)

lemma GG2_ae (a b : T.A₀) : (GG2 T a b : E → ℝ) =ᵐ[T.μ] T.toDiffusionTriple.Γ₂ a.1 b.1 :=
  Integrable.coeFn_toL1 _

lemma GG2_sub_left (a a' b : T.A₀) : GG2 T (a - a') b = GG2 T a b - GG2 T a' b := by
  refine Lp.ext ?_
  filter_upwards [GG2_ae (a - a') b, GG2_ae a b, GG2_ae a' b, Lp.coeFn_sub (GG2 T a b) (GG2 T a' b),
    Γ₂_lin_left (A₀_memA a.2) (A₀_memA a'.2) (A₀_memA b.2) (-1)] with x e1 e2 e3 e4 e5
  rw [e4, Pi.sub_apply, e1, e2, e3, coe_sub']
  rw [e5]; ring

lemma GG2_comm (a b : T.A₀) : GG2 T a b = GG2 T b a := by
  refine Lp.ext ?_
  filter_upwards [GG2_ae a b, GG2_ae b a] with x h1 h2
  rw [h1, h2, Γ₂_comm]

lemma GG2_sub_right (a b b' : T.A₀) : GG2 T a (b - b') = GG2 T a b - GG2 T a b' := by
  rw [GG2_comm, GG2_sub_left, GG2_comm b a, GG2_comm b' a]

lemma norm_GG2_le {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (a b : T.A₀) :
    ‖GG2 T a b‖ ≤ (2 * (1 + |ρ|) + 4 * |ρ|) * ‖jL T a‖ * ‖jL T b‖ := by
  have hK := Kf_nonneg hCD
  have cs := cs_of_psd (T := T) (Kf T ρ) (Kf_comm ρ) (fun hf hg hk s => Kf_lin_left ρ hf hg hk s) hK
    (A₀_memA a.2) (A₀_memA b.2)
  have iKa := integrable_A₀ (Kf_memA₀ (T := T) ρ a.2)
  have iKb := integrable_A₀ (Kf_memA₀ (T := T) ρ b.2)
  have iKab : Integrable (Kf T ρ a.1 b.1) T.μ := by
    have : Kf T ρ a.1 b.1 = T.toDiffusionTriple.Γ₂ a.1 b.1 - fun x => ρ * G T a.1 b.1 x := by
      funext x; simp [Kf]
    rw [this]
    exact (integrable_A₀ (Γ₂_bil_memA₀ a.2 b.2)).sub ((integrable_G a b).const_mul ρ)
  have key := int_abs_le_sqrt iKa iKb iKab.1 (hK a.1 (A₀_memA a.2)) (hK b.1 (A₀_memA b.2)) cs
  have eK : ∀ w : T.A₀, √(∫ x, Kf T ρ w.1 w.1 x ∂T.μ) ≤ √(2 * (1 + |ρ|)) * ‖jL T w‖ := by
    intro w
    have e1 : ∫ x, Kf T ρ w.1 w.1 x ∂T.μ ≤ 2 * (1 + |ρ|) * ‖jL T w‖ ^ 2 := by
      refine (eK_le ρ w).trans ?_
      have := graphSq_le w
      nlinarith [abs_nonneg ρ]
    calc √(∫ x, Kf T ρ w.1 w.1 x ∂T.μ) ≤ √(2 * (1 + |ρ|) * ‖jL T w‖ ^ 2) := Real.sqrt_le_sqrt e1
      _ = √(2 * (1 + |ρ|)) * ‖jL T w‖ := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hs : √(2 * (1 + |ρ|)) * √(2 * (1 + |ρ|)) = 2 * (1 + |ρ|) := Real.mul_self_sqrt (by positivity)
  have k1 : ∫ x, |Kf T ρ a.1 b.1 x| ∂T.μ ≤ 2 * (1 + |ρ|) * ‖jL T a‖ * ‖jL T b‖ := by
    refine key.2.trans ?_
    calc √(∫ x, Kf T ρ a.1 a.1 x ∂T.μ) * √(∫ x, Kf T ρ b.1 b.1 x ∂T.μ)
        ≤ (√(2 * (1 + |ρ|)) * ‖jL T a‖) * (√(2 * (1 + |ρ|)) * ‖jL T b‖) :=
          mul_le_mul (eK a) (eK b) (Real.sqrt_nonneg _) (by positivity)
      _ = (√(2 * (1 + |ρ|)) * √(2 * (1 + |ρ|))) * ‖jL T a‖ * ‖jL T b‖ := by ring
      _ = 2 * (1 + |ρ|) * ‖jL T a‖ * ‖jL T b‖ := by rw [hs]
  have g1 : ∫ x, |G T a.1 b.1 x| ∂T.μ ≤ ‖jE T a‖ * ‖jE T b‖ := by
    have := norm_GG_le a b
    rw [norm_GG] at this; linarith
  have g2 : ‖jE T a‖ * ‖jE T b‖ ≤ 4 * ‖jL T a‖ * ‖jL T b‖ := by
    have := norm_jE_le a
    have := norm_jE_le b
    nlinarith [norm_nonneg (jE T a), norm_nonneg (jE T b), norm_nonneg (jL T a), norm_nonneg (jL T b)]
  have iG := integrable_G a b
  have hpt : ∀ x, |T.toDiffusionTriple.Γ₂ a.1 b.1 x| ≤ |Kf T ρ a.1 b.1 x| + |ρ| * |G T a.1 b.1 x| := by
    intro x
    have : T.toDiffusionTriple.Γ₂ a.1 b.1 x = Kf T ρ a.1 b.1 x + ρ * G T a.1 b.1 x := by simp [Kf]
    rw [this]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul]
  have iΓ := integrable_A₀ (Γ₂_bil_memA₀ a.2 b.2)
  have n1 : ‖GG2 T a b‖ = ∫ x, |T.toDiffusionTriple.Γ₂ a.1 b.1 x| ∂T.μ := by
    rw [L1.norm_eq_integral_norm]
    refine integral_congr_ae ?_
    filter_upwards [GG2_ae a b] with x hx
    rw [hx]; rfl
  rw [n1]
  calc ∫ x, |T.toDiffusionTriple.Γ₂ a.1 b.1 x| ∂T.μ
      ≤ ∫ x, (|Kf T ρ a.1 b.1 x| + |ρ| * |G T a.1 b.1 x|) ∂T.μ :=
        integral_mono iΓ.abs (iKab.abs.add (iG.abs.const_mul _)) hpt
    _ = ∫ x, |Kf T ρ a.1 b.1 x| ∂T.μ + |ρ| * ∫ x, |G T a.1 b.1 x| ∂T.μ := by
        rw [integral_add iKab.abs (iG.abs.const_mul _), integral_const_mul]
    _ ≤ (2 * (1 + |ρ|) + 4 * |ρ|) * ‖jL T a‖ * ‖jL T b‖ := by
        have := mul_le_mul_of_nonneg_left (g1.trans g2) (abs_nonneg ρ)
        nlinarith [norm_nonneg (jL T a), norm_nonneg (jL T b), mul_nonneg (norm_nonneg (jL T a)) (norm_nonneg (jL T b))]

/-- **Bilinear `Γ₂` on `𝒟(L)`**: existence of the `L¹`-limit of `Γ₂(a_k,b_k)`, independent of the sequences. -/
theorem gamma2E_exists {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u v : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (hv : v ∈ T.toDiffusionTriple.generator.domain) :
    ∃ γ : Lp ℝ 1 T.μ, ∀ (a b : ℕ → T.A₀), GraphConv T a u hu → GraphConv T b v hv →
      Tendsto (fun k => GG2 T (a k) (b k)) atTop (𝓝 γ) := by
  obtain ⟨a0, ha0⟩ := exists_graphConv u hu
  obtain ⟨b0, hb0⟩ := exists_graphConv v hv
  exact bil_spec (jL T) (jL T) (GG2 T) (by positivity) (fun x x' y => GG2_sub_left x x' y)
    (fun x y y' => GG2_sub_right x y y') (norm_GG2_le hCD) ⟨a0, b0, ha0, hb0⟩

/-- the bilinear extended `Γ₂(u,v)`, `u, v ∈ 𝒟(L)` (BGL Prop. 3.3.16 (i)). -/
noncomputable def gamma2E {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (u v : Lp ℝ 2 T.μ)
    (hu : u ∈ T.toDiffusionTriple.generator.domain) (hv : v ∈ T.toDiffusionTriple.generator.domain) :
    Lp ℝ 1 T.μ :=
  Classical.choose (gamma2E_exists hCD u v hu hv)

theorem gamma2E_tendsto {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {u v : Lp ℝ 2 T.μ}
    {hu : u ∈ T.toDiffusionTriple.generator.domain} {hv : v ∈ T.toDiffusionTriple.generator.domain}
    {a b : ℕ → T.A₀} (ha : GraphConv T a u hu) (hb : GraphConv T b v hv) :
    Tendsto (fun k => GG2 T (a k) (b k)) atTop (𝓝 (gamma2E hCD u v hu hv)) :=
  Classical.choose_spec (gamma2E_exists hCD u v hu hv) a b ha hb

end FullTriple

end MarkovTriple.BGL
