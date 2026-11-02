import Mathlib
import MarkovTriple.BGL.Theory.Strong.Reinforced
import MarkovTriple.BGL.Theory.Strong.Energy
import MarkovTriple.BGL.Theory.Gamma2Integral

/-!
# `L¹` estimates for `Γ` and `Γ₂` on test functions (BGL Props 3.3.5/3.3.16, the continuity part)

For `a, b ∈ 𝒜₀`, `p = a − b`, `q = a + b` and every `λ > 0`:
`∫|Γ(a) − Γ(b)| ≤ ½ (λ ℰ(p) + ℰ(q)/λ)` and the same for `Γ₂` with `ℰ` replaced by
`k(w) = ∫ (Γ₂(w) − ρΓ(w)) = ‖Lw‖² − ρ ℰ(w)` (plus the `ρ`-correction), under `CD(ρ,n)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- `B(a−b, a+b) = B(a,a) − B(b,b)` for a symmetric a.e.-bilinear form on `𝒜`. -/
lemma bil_diff (B : (E → ℝ) → (E → ℝ) → E → ℝ) (hsymm : ∀ f g, B f g = B g f)
    (hlin : ∀ {f g k : E → ℝ}, f ∈ T.A → g ∈ T.A → k ∈ T.A → ∀ s : ℝ,
      B (fun x => f x + s * g x) k =ᵐ[T.μ] fun x => B f k x + s * B g k x)
    {a b : E → ℝ} (ha : a ∈ T.A) (hb : b ∈ T.A) :
    B (fun x => a x + (-1) * b x) (fun x => a x + 1 * b x) =ᵐ[T.μ]
      fun x => B a a x - B b b x := by
  have hq : (fun x => a x + 1 * b x) ∈ T.A := by
    have : (fun x => a x + 1 * b x) = a + (1 : ℝ) • b := by funext x; simp
    rw [this]; exact T.A.add_mem ha (T.A.smul_mem hb _)
  have h1 := hlin ha hb hq (-1)
  have h2 := hlin ha hb ha 1
  have h3 := hlin ha hb hb 1
  filter_upwards [h1, h2, h3] with x e1 e2 e3
  have s1 : B a (fun x => a x + 1 * b x) x = B (fun x => a x + 1 * b x) a x := congrFun (hsymm _ _) x
  have s2 : B b (fun x => a x + 1 * b x) x = B (fun x => a x + 1 * b x) b x := congrFun (hsymm _ _) x
  have s3 : B b a x = B a b x := congrFun (hsymm _ _) x
  rw [e1, s1, s2, e2, e3]
  rw [s3]; ring

/-- elementary: `c² ≤ xy`, `x,y ≥ 0`, `λ > 0` ⇒ `2|c| ≤ λx + y/λ`. -/
lemma two_abs_le {c x y l : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hl : 0 < l) (h : c ^ 2 ≤ x * y) :
    2 * |c| ≤ l * x + y / l := by
  have h1 : (l * x + y / l) ^ 2 ≥ 4 * (x * y) := by
    have : (l * x + y / l) ^ 2 - 4 * (x * y) = (l * x - y / l) ^ 2 := by field_simp; ring
    nlinarith [sq_nonneg (l * x - y / l)]
  have h2 : (2 * |c|) ^ 2 ≤ (l * x + y / l) ^ 2 := by
    have : (2 * |c|) ^ 2 = 4 * c ^ 2 := by rw [mul_pow, sq_abs]; ring
    nlinarith
  have h3 : 0 ≤ l * x + y / l := by positivity
  exact abs_le_of_sq_le_sq' h2 h3 |>.2

lemma G_amgm {p q : E → ℝ} (hp : p ∈ T.A) (hq : q ∈ T.A) {l : ℝ} (hl : 0 < l) :
    ∀ᵐ x ∂T.μ, 2 * |G T p q x| ≤ l * G T p p x + G T q q x / l := by
  filter_upwards [ExtendedAlgebra.ΓA_cs T.extendedAlgebra hp hq, T.ΓA_nonneg p hp, T.ΓA_nonneg q hq]
    with x h1 h2 h3
  exact two_abs_le h2 h3 hl h1

lemma Kf_amgm {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {p q : E → ℝ} (hp : p ∈ T.A) (hq : q ∈ T.A)
    {l : ℝ} (hl : 0 < l) :
    ∀ᵐ x ∂T.μ, 2 * |Kf T ρ p q x| ≤ l * Kf T ρ p p x + Kf T ρ q q x / l := by
  have hK := Kf_nonneg hCD
  have cs := cs_of_psd (T := T) (Kf T ρ) (Kf_comm ρ) (fun hf hg hk s => Kf_lin_left ρ hf hg hk s)
    hK hp hq
  filter_upwards [cs, hK p hp, hK q hq] with x h1 h2 h3
  exact two_abs_le h2 h3 hl h1

lemma sub_memA₀ {a b : E → ℝ} (ha : a ∈ T.A₀) (hb : b ∈ T.A₀) :
    (fun x => a x + (-1) * b x) ∈ T.A₀ := by
  have : (fun x => a x + (-1) * b x) = a + (-1 : ℝ) • b := by funext x; simp
  rw [this]; exact T.A₀.add_mem ha (T.A₀.smul_mem _ hb)

lemma add_memA₀ {a b : E → ℝ} (ha : a ∈ T.A₀) (hb : b ∈ T.A₀) :
    (fun x => a x + 1 * b x) ∈ T.A₀ := by
  have : (fun x => a x + 1 * b x) = a + (1 : ℝ) • b := by funext x; simp
  rw [this]; exact T.A₀.add_mem ha (T.A₀.smul_mem _ hb)

lemma Γ₂_memA₀ {a : E → ℝ} (ha : a ∈ T.A₀) : T.toDiffusionTriple.Γ₂ a a ∈ T.A₀ := by
  have h1 := T.L_mem _ (T.ΓA_self_mem_A₀ ha)
  have h2 := ΓA_mem_A₀ T (T.A₀_le a ha) (T.L_mem a ha)
  have : T.toDiffusionTriple.Γ₂ a a = (1 / 2 : ℝ) • (T.L (G T a a) - (2 : ℝ) • G T a (T.L a)) := by
    funext x
    simp only [DiffusionTriple.Γ₂, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [show T.toDiffusionTriple.ΓA (T.L a) a x = T.toDiffusionTriple.ΓA a (T.L a) x from
      congrFun (DiffusionTriple.ΓA_comm T.toDiffusionTriple (T.L a) a) x]
    ring
  rw [this]
  exact T.A₀.smul_mem _ (T.A₀.sub_mem h1 (T.A₀.smul_mem _ h2))

lemma Kf_memA₀ (ρ : ℝ) {a : E → ℝ} (ha : a ∈ T.A₀) : Kf T ρ a a ∈ T.A₀ := by
  have : Kf T ρ a a = T.toDiffusionTriple.Γ₂ a a - ρ • G T a a := by
    funext x; simp [Kf]
  rw [this]
  exact T.A₀.sub_mem (Γ₂_memA₀ ha) (T.A₀.smul_mem _ (T.ΓA_self_mem_A₀ ha))

lemma integrable_A₀ {f : E → ℝ} (hf : f ∈ T.A₀) : Integrable f T.μ :=
  DiffusionTriple.integrable_of_mem T.toDiffusionTriple hf

/-- **`L¹` difference estimate for `Γ`.** -/
theorem int_G_diff_le {a b : E → ℝ} (ha : a ∈ T.A₀) (hb : b ∈ T.A₀) {l : ℝ} (hl : 0 < l) :
    ∫ x, |G T a a x - G T b b x| ∂T.μ ≤
      (l * ∫ x, G T (fun x => a x + (-1) * b x) (fun x => a x + (-1) * b x) x ∂T.μ +
        (∫ x, G T (fun x => a x + 1 * b x) (fun x => a x + 1 * b x) x ∂T.μ) / l) / 2 := by
  have hp := sub_memA₀ ha hb
  have hq := add_memA₀ ha hb
  have hpA := A₀_memA hp
  have hqA := A₀_memA hq
  have hbil := bil_diff (T := T) (G T) G_comm (fun hf hg hk s => G_lin_left hf hg s hk)
    (A₀_memA ha) (A₀_memA hb)
  have ip := integrable_A₀ (T.ΓA_self_mem_A₀ hp)
  have iq := integrable_A₀ (T.ΓA_self_mem_A₀ hq)
  have iab : Integrable (fun x => |G T a a x - G T b b x|) T.μ := by
    have h1 := integrable_A₀ (T.ΓA_self_mem_A₀ ha)
    have h2 := integrable_A₀ (T.ΓA_self_mem_A₀ hb)
    exact (h1.sub h2).abs
  have iR : Integrable (fun x => (l * G T (fun x => a x + (-1) * b x) (fun x => a x + (-1) * b x) x +
      G T (fun x => a x + 1 * b x) (fun x => a x + 1 * b x) x / l) / 2) T.μ :=
    ((ip.const_mul l).add (iq.div_const l)).div_const 2
  have hle : ∀ᵐ x ∂T.μ, |G T a a x - G T b b x| ≤
      (l * G T (fun x => a x + (-1) * b x) (fun x => a x + (-1) * b x) x +
        G T (fun x => a x + 1 * b x) (fun x => a x + 1 * b x) x / l) / 2 := by
    filter_upwards [hbil, G_amgm hpA hqA hl] with x h1 h2
    rw [← h1]; linarith
  refine (integral_mono_ae iab iR hle).trans (le_of_eq ?_)
  rw [integral_div, integral_add (ip.const_mul l) (iq.div_const l), integral_const_mul, integral_div]

/-- **`L¹` difference estimate for `K = Γ₂ − ρΓ`.** -/
theorem int_Kf_diff_le {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {a b : E → ℝ} (ha : a ∈ T.A₀)
    (hb : b ∈ T.A₀) {l : ℝ} (hl : 0 < l) :
    ∫ x, |Kf T ρ a a x - Kf T ρ b b x| ∂T.μ ≤
      (l * ∫ x, Kf T ρ (fun x => a x + (-1) * b x) (fun x => a x + (-1) * b x) x ∂T.μ +
        (∫ x, Kf T ρ (fun x => a x + 1 * b x) (fun x => a x + 1 * b x) x ∂T.μ) / l) / 2 := by
  have hp := sub_memA₀ ha hb
  have hq := add_memA₀ ha hb
  have hpA := A₀_memA hp
  have hqA := A₀_memA hq
  have hbil := bil_diff (T := T) (Kf T ρ) (Kf_comm ρ) (fun hf hg hk s => Kf_lin_left ρ hf hg hk s)
    (A₀_memA ha) (A₀_memA hb)
  have ip := integrable_A₀ (Kf_memA₀ ρ hp)
  have iq := integrable_A₀ (Kf_memA₀ ρ hq)
  have iab : Integrable (fun x => |Kf T ρ a a x - Kf T ρ b b x|) T.μ := by
    have h1 := integrable_A₀ (Kf_memA₀ ρ ha)
    have h2 := integrable_A₀ (Kf_memA₀ ρ hb)
    exact (h1.sub h2).abs
  have iR : Integrable (fun x => (l * Kf T ρ (fun x => a x + (-1) * b x) (fun x => a x + (-1) * b x) x +
      Kf T ρ (fun x => a x + 1 * b x) (fun x => a x + 1 * b x) x / l) / 2) T.μ :=
    ((ip.const_mul l).add (iq.div_const l)).div_const 2
  have hle : ∀ᵐ x ∂T.μ, |Kf T ρ a a x - Kf T ρ b b x| ≤
      (l * Kf T ρ (fun x => a x + (-1) * b x) (fun x => a x + (-1) * b x) x +
        Kf T ρ (fun x => a x + 1 * b x) (fun x => a x + 1 * b x) x / l) / 2 := by
    filter_upwards [hbil, Kf_amgm hCD hpA hqA hl] with x h1 h2
    rw [← h1]; linarith
  refine (integral_mono_ae iab iR hle).trans (le_of_eq ?_)
  rw [integral_div, integral_add (ip.const_mul l) (iq.div_const l), integral_const_mul, integral_div]

end FullTriple

end MarkovTriple.BGL
