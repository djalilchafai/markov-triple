import Mathlib
import MarkovTriple.BGL.Theory.Extension.Gamma2Mul
import MarkovTriple.BGL.Theory.Extension.IdentIBP
import MarkovTriple.BGL.Theory.Strong.Hessian

/-!
# Converse of BGL Prop. 3.3.17 (book p. 162): analytic part

Statements: `Extension/STATEMENTS_R15_Converse.md`.  This file contains step (2) of the book's proof: the pairing
`ℓ_f(h) = ∫ K(f,h)`, `K(f,h) = Γ₂(f,h) − ρ Γ(f,h)`, `f ∈ 𝒜`, `h ∈ 𝒜₀`, and its integrated Cauchy–Schwarz inequality
`ℓ_f(h)² ≤ ∫K(f) · ∫K(h)` (the book's `K(f,h)² ≤ K(f,f)K(h,h)`, integrated).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- `∫ L g = 0` for `g ∈ 𝒜₀` (F7 with the test function `1`). -/
lemma int_L_A₀ {g : E → ℝ} (hg : g ∈ T.A₀) : ∫ x, T.L g x ∂T.μ = 0 := by
  have h1 : (fun _ : E => (1 : ℝ)) ∈ T.A := T.A.algebraMap_mem 1
  have e := (T.ibp_A (fun _ => 1) h1 g hg).2
  have e0 : ∫ x, G T (fun _ => (1 : ℝ)) g x ∂T.μ = 0 := by
    rw [integral_congr_ae (G_const_left (T := T) 1 (A₀_memA hg))]; simp
  rw [e0] at e
  simpa using e.symm

/-- `∫ Γ₂(f,h) = ∫ (L f)(L h)` for `f ∈ 𝒜`, `h ∈ 𝒜₀` (book, proof of 3.3.17, p. 162). -/
lemma int_Γ₂_mul {f h : E → ℝ} (hf : f ∈ T.A) (hh : h ∈ T.A₀) :
    ∫ x, T.toDiffusionTriple.Γ₂ f h x ∂T.μ = ∫ x, T.L f x * T.L h x ∂T.μ := by
  have i1 := intA₀ (L_memA₀ (G_memA₀ hf hh))
  have i2 := intA₀ (G_memA₀ hf (L_memA₀ hh))
  have i3 := intA₀ (G_memA₀ (L_memA hf) hh)
  have e1 := int_L_A₀ (G_memA₀ hf hh)
  have e2 := (T.ibp_A f hf (T.L h) (L_memA₀ hh)).1
  have e3 := (T.ibp_A (T.L f) (L_memA hf) h hh).2
  have s1 := integral_sub i1 i2
  have s2 := integral_sub (i1.sub i2) i3
  simp only [Pi.sub_apply] at s2
  have e4 : ∫ x, T.toDiffusionTriple.Γ₂ f h x ∂T.μ =
      (∫ x, T.L (G T f h) x ∂T.μ - ∫ x, G T f (T.L h) x ∂T.μ - ∫ x, G T (T.L f) h x ∂T.μ) / 2 := by
    rw [← s1, ← s2, ← integral_div]
    rfl
  have e5 : ∫ x, T.L h x * T.L f x ∂T.μ = ∫ x, T.L f x * T.L h x ∂T.μ :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [e4, e1, e2, e3, e5]; ring

/-- quadratic expansion of `G`. -/
lemma G_quad {f h : E → ℝ} (hf : f ∈ T.A) (hh : h ∈ T.A) (s : ℝ) :
    G T (fun x => f x + s * h x) (fun x => f x + s * h x) =ᵐ[T.μ]
      fun x => G T f f x + 2 * s * G T f h x + s ^ 2 * G T h h x := by
  have hu : (fun x => f x + s * h x) ∈ T.A := by
    have : (fun x => f x + s * h x) = f + s • h := by funext x; simp
    rw [this]; exact T.A.add_mem hf (T.A.smul_mem hh s)
  have a1 := G_lin_left hf hh s hu
  have a2 := G_lin_left hf hh s hf
  have a3 := G_lin_left hf hh s hh
  filter_upwards [a1, a2, a3] with x b1 b2 b3
  rw [b1, G_comm f _, G_comm h _, b2, b3, G_comm h f]
  ring

/-- quadratic expansion of `Γ₂`. -/
lemma Γ₂_quad {f h : E → ℝ} (hf : f ∈ T.A) (hh : h ∈ T.A) (s : ℝ) :
    T.toDiffusionTriple.Γ₂ (fun x => f x + s * h x) (fun x => f x + s * h x) =ᵐ[T.μ]
      fun x => T.toDiffusionTriple.Γ₂ f f x + 2 * s * T.toDiffusionTriple.Γ₂ f h x +
        s ^ 2 * T.toDiffusionTriple.Γ₂ h h x := by
  have hu : (fun x => f x + s * h x) ∈ T.A := by
    have : (fun x => f x + s * h x) = f + s • h := by funext x; simp
    rw [this]; exact T.A.add_mem hf (T.A.smul_mem hh s)
  have a1 := Γ₂_lin_left hf hh hu s
  have a2 := Γ₂_lin_left hf hh hf s
  have a3 := Γ₂_lin_left hf hh hh s
  filter_upwards [a1, a2, a3] with x b1 b2 b3
  rw [b1, Γ₂_comm f _, Γ₂_comm h _, b2, b3, Γ₂_comm h f]
  ring

/-- `Γ₂(a,b) ∈ 𝒜₀` for `a ∈ 𝒜`, `b ∈ 𝒜₀`. -/
lemma Γ₂_pairA₀ {a b : E → ℝ} (ha : a ∈ T.A) (hb : b ∈ T.A₀) : T.toDiffusionTriple.Γ₂ a b ∈ T.A₀ := by
  have e : T.toDiffusionTriple.Γ₂ a b = (1 / 2 : ℝ) • (T.L (G T a b) - G T a (T.L b) - G T (T.L a) b) := by
    funext x; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Γ₂_eq]; ring
  rw [e]
  exact T.A₀.smul_mem _ (T.A₀.sub_mem (T.A₀.sub_mem (L_memA₀ (G_memA₀ ha hb)) (G_memA₀ ha (L_memA₀ hb)))
    (G_memA₀ (L_memA ha) hb))

/-- `K(g) ≥ 0` a.e. for `g ∈ 𝒜` under `CD(ρ,n)`. -/
lemma K_nonneg {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {g : E → ℝ} (hg : g ∈ T.A) :
    ∀ᵐ x ∂T.μ, 0 ≤ T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x := by
  filter_upwards [hCD.2 g hg] with x hx
  have : 0 ≤ (n⁻¹).toReal * (T.L g x) ^ 2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  show 0 ≤ _
  have h2 : ρ * G T g g x + (n⁻¹).toReal * (T.L g x) ^ 2 ≤ T.toDiffusionTriple.Γ₂ g g x := hx
  linarith

/-- **Integrated Cauchy–Schwarz for `K`** (book p. 162: `K(f,h)² ≤ K(f,f)K(h,h)`, integrated).
For `f ∈ 𝒜` with `Γ(f), Γ₂(f) ∈ L¹`, `h ∈ 𝒜₀`:
`(∫ (Γ₂(f,h) − ρΓ(f,h)))² ≤ (∫ K(f)) (∫ K(h))`. -/
theorem ell_sq_le {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f h : E → ℝ} (hf : f ∈ T.A) (hh : h ∈ T.A₀)
    (hG : Integrable (G T f f) T.μ) (hG2 : Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ) :
    (∫ x, (T.toDiffusionTriple.Γ₂ f h x - ρ * G T f h x) ∂T.μ) ^ 2 ≤
      (∫ x, (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) ∂T.μ) *
        (∫ x, (T.toDiffusionTriple.Γ₂ h h x - ρ * G T h h x) ∂T.μ) := by
  have hhA := A₀_memA hh
  -- integrability
  have iA : Integrable (fun x => T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) T.μ :=
    hG2.sub (hG.const_mul ρ)
  have iB : Integrable (fun x => T.toDiffusionTriple.Γ₂ f h x - ρ * G T f h x) T.μ :=
    (intA₀ (Γ₂_pairA₀ hf hh)).sub ((intA₀ (G_memA₀ hf hh)).const_mul ρ)
  have iC : Integrable (fun x => T.toDiffusionTriple.Γ₂ h h x - ρ * G T h h x) T.μ :=
    (intA₀ (Γ₂_pairA₀ hhA hh)).sub ((intA₀ (G_memA₀ hhA hh)).const_mul ρ)
  set A := ∫ x, (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) ∂T.μ
  set B := ∫ x, (T.toDiffusionTriple.Γ₂ f h x - ρ * G T f h x) ∂T.μ
  set C := ∫ x, (T.toDiffusionTriple.Γ₂ h h x - ρ * G T h h x) ∂T.μ
  have key : ∀ s : ℝ, 0 ≤ C * s * s + 2 * B * s + A := by
    intro s
    have hu : (fun x => f x + s * h x) ∈ T.A := by
      have : (fun x => f x + s * h x) = f + s • h := by funext x; simp
      rw [this]; exact T.A.add_mem hf (T.A.smul_mem hhA s)
    have hnn := K_nonneg hCD hu
    have hexp : ∀ᵐ x ∂T.μ, T.toDiffusionTriple.Γ₂ (fun x => f x + s * h x) (fun x => f x + s * h x) x -
        ρ * G T (fun x => f x + s * h x) (fun x => f x + s * h x) x =
        (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) + 2 * s * (T.toDiffusionTriple.Γ₂ f h x - ρ * G T f h x) +
          s ^ 2 * (T.toDiffusionTriple.Γ₂ h h x - ρ * G T h h x) := by
      filter_upwards [Γ₂_quad hf hhA s, G_quad hf hhA s] with x e1 e2
      rw [e1, e2]; ring
    have h0 : 0 ≤ ∫ x, ((T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) +
        2 * s * (T.toDiffusionTriple.Γ₂ f h x - ρ * G T f h x) +
          s ^ 2 * (T.toDiffusionTriple.Γ₂ h h x - ρ * G T h h x)) ∂T.μ := by
      refine integral_nonneg_of_ae ?_
      filter_upwards [hnn, hexp] with x h1 h2
      rw [← h2]; exact h1
    have j1 := integral_add (iA.add (iB.const_mul (2 * s))) (iC.const_mul (s ^ 2))
    have j2 := integral_add iA (iB.const_mul (2 * s))
    simp only [Pi.add_apply] at j1 j2
    rw [j1, j2, integral_const_mul, integral_const_mul] at h0
    nlinarith [h0]
  have := discrim_le_zero (a := C) (b := 2 * B) (c := A) (fun s => by nlinarith [key s])
  unfold discrim at this
  nlinarith [this]

end FullTriple

/-! ### Abstract Hilbert-space step (Hahn–Banach + Riesz) -/

section Rep

variable {V H : Type*} [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]

/-- If `|Λ b| ≤ M ‖Φ b‖` for linear `Φ : V → H`, `Λ : V → ℝ`, then `Λ = ⟪w, Φ ·⟫` for some `w ∈ H`
(Hahn–Banach for the functional on `ran Φ`, then Riesz).  No density of `ran Φ` is needed. -/
lemma exists_rep (Φ : V →ₗ[ℝ] H) (Λ : V →ₗ[ℝ] ℝ) (M : ℝ) (hM : ∀ b, |Λ b| ≤ M * ‖Φ b‖) :
    ∃ w : H, ∀ b, Λ b = inner ℝ w (Φ b) := by
  have hker : LinearMap.ker Φ ≤ LinearMap.ker Λ := by
    intro b hb
    have h0 : Φ b = 0 := hb
    have := hM b
    rw [h0] at this
    simp only [norm_zero, mul_zero] at this
    exact abs_nonpos_iff.1 this
  let Ψ : LinearMap.range Φ →ₗ[ℝ] ℝ :=
    ((LinearMap.ker Φ).liftQ Λ hker).comp (Φ.quotKerEquivRange).symm.toLinearMap
  have hΨ : ∀ b, Ψ ⟨Φ b, LinearMap.mem_range_self Φ b⟩ = Λ b := by
    intro b
    have h1 := LinearMap.quotKerEquivRange_symm_apply_image Φ b (LinearMap.mem_range_self Φ b)
    simp only [Ψ, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1]
    rfl
  have hb : ∀ y : LinearMap.range Φ, ‖Ψ y‖ ≤ M * ‖y‖ := by
    intro y
    obtain ⟨b, hb⟩ := y.2
    have hy : y = ⟨Φ b, LinearMap.mem_range_self Φ b⟩ := Subtype.ext hb.symm
    rw [hy, hΨ b]
    exact hM b
  let Ψc : LinearMap.range Φ →L[ℝ] ℝ := Ψ.mkContinuousOfExistsBound ⟨M, hb⟩
  obtain ⟨g, hg, -⟩ := exists_extension_norm_eq (LinearMap.range Φ) Ψc
  refine ⟨(InnerProductSpace.toDual ℝ H).symm g, fun b => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply, hg ⟨Φ b, LinearMap.mem_range_self Φ b⟩]
  exact (hΨ b).symm

end Rep

namespace FullTriple

variable {T : FullTriple E}

/-- `b ↦ [L L b]`, `𝒜₀ → L²`, linear (a.e. linearity of `L` on `𝒜₀` and well-definedness on `𝒜`). -/
noncomputable def LLₗ (T : FullTriple E) : T.A₀ →ₗ[ℝ] Lp ℝ 2 T.μ where
  toFun b := T.toDiffusionTriple.Lcls ⟨T.L b.1, T.L_mem b.1 b.2⟩
  map_add' b c := by
    refine Lp.ext ?_
    have hbc : T.L (b.1 + c.1) =ᵐ[T.μ] T.L b.1 + T.L c.1 :=
      DiffusionTriple.L_add_ae T.toDiffusionTriple b.2 c.2
    have h1 : T.L (T.L (b.1 + c.1)) =ᵐ[T.μ] T.L (T.L b.1 + T.L c.1) :=
      L_congr_A T (T.L_mem_A _ (T.A₀_le _ (T.A₀.add_mem b.2 c.2)))
        (T.A.add_mem (T.L_mem_A _ (T.A₀_le _ b.2)) (T.L_mem_A _ (T.A₀_le _ c.2))) hbc
    have h2 : T.L (T.L b.1 + T.L c.1) =ᵐ[T.μ] T.L (T.L b.1) + T.L (T.L c.1) :=
      DiffusionTriple.L_add_ae T.toDiffusionTriple (T.L_mem _ b.2) (T.L_mem _ c.2)
    filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple
        (⟨T.L (b + c).1, T.L_mem _ (b + c).2⟩ : T.A₀),
      DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀),
      DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (⟨T.L c.1, T.L_mem c.1 c.2⟩ : T.A₀),
      Lp.coeFn_add (T.toDiffusionTriple.Lcls (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀))
        (T.toDiffusionTriple.Lcls (⟨T.L c.1, T.L_mem c.1 c.2⟩ : T.A₀)), h1, h2] with x e1 e2 e3 e4 e5 e6
    rw [e4, Pi.add_apply, e2, e3]
    refine e1.trans ?_
    have := e5.trans e6
    simpa using this
  map_smul' c b := by
    refine Lp.ext ?_
    have hb : T.L (c • b.1) =ᵐ[T.μ] c • T.L b.1 := DiffusionTriple.L_smul_ae T.toDiffusionTriple c b.2
    have h1 : T.L (T.L (c • b.1)) =ᵐ[T.μ] T.L (c • T.L b.1) :=
      L_congr_A T (T.L_mem_A _ (T.A₀_le _ (T.A₀.smul_mem c b.2)))
        (T.A.smul_mem (T.L_mem_A _ (T.A₀_le _ b.2)) c) hb
    have h2 : T.L (c • T.L b.1) =ᵐ[T.μ] c • T.L (T.L b.1) :=
      DiffusionTriple.L_smul_ae T.toDiffusionTriple c (T.L_mem _ b.2)
    filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple
        (⟨T.L (c • b).1, T.L_mem _ (c • b).2⟩ : T.A₀),
      DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀),
      Lp.coeFn_smul c (T.toDiffusionTriple.Lcls (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀)), h1, h2]
      with x e1 e2 e3 e4 e5
    rw [RingHom.id_apply, e3, Pi.smul_apply, e2]
    refine e1.trans ?_
    have := e4.trans e5
    simpa using this

/-- **`Core2`** (implicit in the book's proof of the converse in Prop. 3.3.17, p. 162): `(1 − L)𝒜₀` is a core for `L`,
i.e. `𝒜₀` is a core for `L²`.  Concretely, for each `a ∈ 𝒜₀` there are `b_n ∈ 𝒜₀` with `(1−L)b_n → a` and
`L(1−L)b_n → L a` in `L²`.  Not derived from ESA of `L` alone by abstract operator theory (we know of no derivation and of no counter-model satisfying F1–F10; audit R15 asks for a reference or this softer wording); see
`Extension/STATEMENTS_R15_Converse.md`. -/
def Core2 (T : FullTriple E) : Prop :=
  ∀ a : T.A₀, ∃ b : ℕ → T.A₀,
    Tendsto (fun n => T.toDiffusionTriple.cls (b n) - T.toDiffusionTriple.Lcls (b n)) atTop
      (𝓝 (T.toDiffusionTriple.cls a)) ∧
    Tendsto (fun n => T.toDiffusionTriple.Lcls (b n) - LLₗ T (b n)) atTop
      (𝓝 (T.toDiffusionTriple.Lcls a))

lemma inner_cls_Lcls (b c : T.A₀) :
    inner ℝ (T.toDiffusionTriple.cls b) (T.toDiffusionTriple.Lcls c) = ∫ x, b.1 x * T.L c.1 x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple b,
    DiffusionTriple.coeFn_Lcls T.toDiffusionTriple c] with x h1 h2
  rw [h1, h2]

lemma inner_cls_cls (b c : T.A₀) :
    inner ℝ (T.toDiffusionTriple.cls b) (T.toDiffusionTriple.cls c) = ∫ x, b.1 x * c.1 x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple b,
    DiffusionTriple.coeFn_cls T.toDiffusionTriple c] with x h1 h2
  rw [h1, h2]

lemma inner_Lcls_Lcls (b c : T.A₀) :
    inner ℝ (T.toDiffusionTriple.Lcls b) (T.toDiffusionTriple.Lcls c) =
      ∫ x, T.L b.1 x * T.L c.1 x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b,
    DiffusionTriple.coeFn_Lcls T.toDiffusionTriple c] with x h1 h2
  rw [h1, h2]

lemma inner_f_Lcls {f : E → ℝ} (hf2 : MemLp f 2 T.μ) (b : T.A₀) :
    inner ℝ (hf2.toLp f) (T.toDiffusionTriple.Lcls b) = ∫ x, f x * T.L b.1 x ∂T.μ := by
  rw [L2_inner_eq]
  refine integral_congr_ae ?_
  filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b] with x h1 h2
  rw [h1, h2]

lemma inner_f_LL {f : E → ℝ} (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ) (b : T.A₀) :
    inner ℝ (hf2.toLp f) (LLₗ T b) = ∫ x, T.L f x * T.L b.1 x ∂T.μ := by
  rw [L2_inner_eq]
  have e := (T.ibp_A f hf (T.L b.1) (T.L_mem b.1 b.2)).1
  have e2 := (T.ibp_A f hf (T.L b.1) (T.L_mem b.1 b.2)).2
  have : ∫ x, f x * T.L (T.L b.1) x ∂T.μ = ∫ x, T.L b.1 x * T.L f x ∂T.μ := by linarith
  have hc : ∫ x, T.L b.1 x * T.L f x ∂T.μ = ∫ x, T.L f x * T.L b.1 x ∂T.μ :=
    integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
  rw [← hc, ← this]
  refine integral_congr_ae ?_
  filter_upwards [hf2.coeFn_toLp, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple
    (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀)] with x h1 h2
  show _ * (T.toDiffusionTriple.Lcls (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀) : E → ℝ) x = _
  rw [h1, h2]

/-- `b ↦ [b] − [L b]`, `𝒜₀ → L²`. -/
noncomputable def Φₗ (T : FullTriple E) : T.A₀ →ₗ[ℝ] Lp ℝ 2 T.μ :=
  DiffusionTriple.clsₗ T.toDiffusionTriple - DiffusionTriple.Lclsₗ T.toDiffusionTriple

/-- `b ↦ ∫ f L(b − L b) = ⟪[f], [L b] − [L L b]⟫`. -/
noncomputable def Λₗ (T : FullTriple E) {f : E → ℝ} (hf2 : MemLp f 2 T.μ) : T.A₀ →ₗ[ℝ] ℝ :=
  (innerₗ (Lp ℝ 2 T.μ) (hf2.toLp f)).comp (DiffusionTriple.Lclsₗ T.toDiffusionTriple - LLₗ T)

lemma Φₗ_apply (b : T.A₀) : Φₗ T b = T.toDiffusionTriple.cls b - T.toDiffusionTriple.Lcls b := rfl

lemma Λₗ_apply {f : E → ℝ} (hf2 : MemLp f 2 T.μ) (b : T.A₀) :
    Λₗ T hf2 b = inner ℝ (hf2.toLp f) (T.toDiffusionTriple.Lcls b - LLₗ T b) := rfl

/-- **Step (2)–(3) of the book's proof** (p. 162), in the form `|∫ f L v| ≤ M ‖v‖₂` for `v = b − L b ∈ (1−L)𝒜₀`:
`∫ f L(b − L b) = (1+ρ)∫ f L b − ℓ_f(b)`, `|ℓ_f(b)| ≤ √(∫K(f)) √(∫K(b))`, `∫K(b) ≤ (1+|ρ|)‖b − L b‖²`. -/
theorem bound_fLv {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {f : E → ℝ} (hf : f ∈ T.A)
    (hf2 : MemLp f 2 T.μ) (hG : Integrable (G T f f) T.μ)
    (hG2 : Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ) :
    ∃ M : ℝ, ∀ b : T.A₀, |Λₗ T hf2 b| ≤ M * ‖Φₗ T b‖ := by
  set A : ℝ := ∫ x, (T.toDiffusionTriple.Γ₂ f f x - ρ * G T f f x) ∂T.μ with hAdef
  have hA0 : 0 ≤ A := integral_nonneg_of_ae (K_nonneg hCD hf)
  set F0 : Lp ℝ 2 T.μ := hf2.toLp f with hF0
  set m : ℝ := √(A * (1 + |ρ|)) with hm
  have hm0 : 0 ≤ m := Real.sqrt_nonneg _
  have hmsq : m ^ 2 = A * (1 + |ρ|) := Real.sq_sqrt (by positivity)
  refine ⟨|1 + ρ| * ‖F0‖ + m, fun b => ?_⟩
  have hb := b.2
  have hbA := T.A₀_le _ hb
  set x : Lp ℝ 2 T.μ := T.toDiffusionTriple.cls b with hx
  set y : Lp ℝ 2 T.μ := T.toDiffusionTriple.Lcls b with hy
  set N : ℝ := ‖Φₗ T b‖ with hN
  have hN0 : 0 ≤ N := norm_nonneg _
  have hΦ : Φₗ T b = x - y := rfl
  set α : ℝ := ∫ t, f t * T.L b.1 t ∂T.μ with hα
  set β : ℝ := ∫ t, T.L f t * T.L b.1 t ∂T.μ with hβ
  have hΛ : Λₗ T hf2 b = α - β := by
    rw [Λₗ_apply, inner_sub_right, inner_f_Lcls hf2 b, inner_f_LL hf hf2 b]
  have hxy : inner ℝ x y = ∫ t, b.1 t * T.L b.1 t ∂T.μ := inner_cls_Lcls b b
  have hGbb : ∫ t, G T b.1 b.1 t ∂T.μ = -∫ t, b.1 t * T.L b.1 t ∂T.μ := (T.ibp_A b.1 hbA b.1 hb).2
  have hGnn : 0 ≤ ∫ t, G T b.1 b.1 t ∂T.μ := integral_nonneg_of_ae (T.ΓA_nonneg b.1 hbA)
  have hxy0 : inner ℝ x y ≤ 0 := by rw [hxy]; linarith
  have hN2 : N ^ 2 = ‖x‖ ^ 2 - 2 * inner ℝ x y + ‖y‖ ^ 2 := by
    rw [hN, hΦ]; exact norm_sub_sq_real x y
  have hyN : ‖y‖ ≤ N := by
    by_contra hc; replace hc := not_le.mp hc
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hxN : ‖x‖ ≤ N := by
    by_contra hc; replace hc := not_le.mp hc
    nlinarith [norm_nonneg x, norm_nonneg y]
  have hxyN : -inner ℝ x y ≤ N * N := by
    have h1 := abs_real_inner_le_norm x y
    have h2 : ‖x‖ * ‖y‖ ≤ N * N := mul_le_mul hxN hyN (norm_nonneg _) hN0
    have h3 := neg_le_abs (inner ℝ x y)
    linarith
  -- ℓ
  have iΓ₂f := intA₀ (Γ₂_pairA₀ hf hb)
  have iGf := intA₀ (G_memA₀ hf hb)
  have iΓ₂b := intA₀ (Γ₂_pairA₀ hbA hb)
  have iGb := intA₀ (G_memA₀ hbA hb)
  have hℓ : ∫ t, (T.toDiffusionTriple.Γ₂ f b.1 t - ρ * G T f b.1 t) ∂T.μ = β + ρ * α := by
    rw [integral_sub iΓ₂f (iGf.const_mul ρ), integral_const_mul, int_Γ₂_mul hf hb,
      (T.ibp_A f hf b.1 hb).2]
    ring
  have hC : ∫ t, (T.toDiffusionTriple.Γ₂ b.1 b.1 t - ρ * G T b.1 b.1 t) ∂T.μ =
      ‖y‖ ^ 2 + ρ * inner ℝ x y := by
    rw [integral_sub iΓ₂b (iGb.const_mul ρ), integral_const_mul, int_Γ₂_mul hbA hb, hGbb, hxy,
      ← real_inner_self_eq_norm_sq, inner_Lcls_Lcls]
    ring
  have hell := ell_sq_le hCD hf hb hG hG2
  rw [hℓ, hC] at hell
  have hCle : ‖y‖ ^ 2 + ρ * inner ℝ x y ≤ (1 + |ρ|) * N ^ 2 := by
    have h1 : ρ * inner ℝ x y ≤ |ρ| * (N * N) := by
      calc ρ * inner ℝ x y ≤ |ρ * inner ℝ x y| := le_abs_self _
        _ = |ρ| * |inner ℝ x y| := abs_mul _ _
        _ ≤ |ρ| * (N * N) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          rw [abs_of_nonpos hxy0]; exact hxyN
    nlinarith [sq_nonneg (‖y‖ - N), mul_self_nonneg N, hyN, norm_nonneg y]
  have hℓbd : |β + ρ * α| ≤ m * N := by
    by_contra hc; replace hc := not_le.mp hc
    have h1 : (m * N) ^ 2 < (β + ρ * α) ^ 2 := by
      have := abs_nonneg (β + ρ * α)
      nlinarith [sq_abs (β + ρ * α), mul_nonneg hm0 hN0]
    have h2 : (β + ρ * α) ^ 2 ≤ A * ((1 + |ρ|) * N ^ 2) :=
      hell.trans (mul_le_mul_of_nonneg_left hCle hA0)
    have h3 : (m * N) ^ 2 = A * ((1 + |ρ|) * N ^ 2) := by rw [mul_pow, hmsq]; ring
    linarith
  have hα' : |α| ≤ ‖F0‖ * N := by
    have : α = inner ℝ F0 y := (inner_f_Lcls hf2 b).symm
    rw [this]
    exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hyN (norm_nonneg _))
  rw [hΛ]
  have e : α - β = (1 + ρ) * α - (β + ρ * α) := by ring
  rw [e]
  calc |(1 + ρ) * α - (β + ρ * α)| ≤ |(1 + ρ) * α| + |β + ρ * α| := abs_sub _ _
    _ = |1 + ρ| * |α| + |β + ρ * α| := by rw [abs_mul]
    _ ≤ |1 + ρ| * (‖F0‖ * N) + m * N :=
        add_le_add (mul_le_mul_of_nonneg_left hα' (abs_nonneg _)) hℓbd
    _ = (|1 + ρ| * ‖F0‖ + m) * N := by ring

/-- Sanity check for `Core2` (non-vacuity): it holds whenever `(1 − L)` maps `𝒜₀` onto `𝒜₀` (a.e.), e.g. for
operators with a finite-dimensional or eigenfunction-closed test algebra. -/
theorem core2_of_surjective
    (h : ∀ a : T.A₀, ∃ b : T.A₀, (fun x => b.1 x - T.L b.1 x) =ᵐ[T.μ] a.1) : T.Core2 := by
  intro a
  obtain ⟨b, hb⟩ := h a
  refine ⟨fun _ => b, ?_, ?_⟩
  · have : T.toDiffusionTriple.cls b - T.toDiffusionTriple.Lcls b = T.toDiffusionTriple.cls a := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (T.toDiffusionTriple.cls b) (T.toDiffusionTriple.Lcls b),
        DiffusionTriple.coeFn_cls T.toDiffusionTriple b, DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b,
        DiffusionTriple.coeFn_cls T.toDiffusionTriple a, hb] with x e1 e2 e3 e4 e5
      rw [e1, Pi.sub_apply, e2, e3, e4]; exact e5
    simp only [this]; exact tendsto_const_nhds
  · have hbA := T.A₀_le _ b.2
    have hLb := T.L_mem_A _ hbA
    have hsub : (fun x => b.1 x + (-1 : ℝ) * T.L b.1 x) =ᵐ[T.μ] a.1 := by
      filter_upwards [hb] with x hx; rw [← hx]; ring
    have h1 : T.L a.1 =ᵐ[T.μ] T.L (fun x => b.1 x + (-1 : ℝ) * T.L b.1 x) :=
      (L_congr_A T (by
        have : (fun x => b.1 x + (-1 : ℝ) * T.L b.1 x) = b.1 + (-1 : ℝ) • T.L b.1 := by
          funext x; simp
        rw [this]; exact T.A.add_mem hbA (T.A.smul_mem hLb _)) (T.A₀_le _ a.2) hsub).symm
    have h2 := L_lin hbA hLb (-1 : ℝ)
    have : T.toDiffusionTriple.Lcls b - LLₗ T b = T.toDiffusionTriple.Lcls a := by
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (T.toDiffusionTriple.Lcls b) (LLₗ T b),
        DiffusionTriple.coeFn_Lcls T.toDiffusionTriple b,
        DiffusionTriple.coeFn_Lcls T.toDiffusionTriple (⟨T.L b.1, T.L_mem b.1 b.2⟩ : T.A₀),
        DiffusionTriple.coeFn_Lcls T.toDiffusionTriple a, h1, h2] with x e1 e2 e3 e4 e5 e6
      rw [e1, Pi.sub_apply, e2]
      have e3' : ((LLₗ T b : Lp ℝ 2 T.μ) : E → ℝ) x = T.L (T.L b.1) x := e3
      rw [e3', e4, e5, e6]; ring
    simp only [this]; exact tendsto_const_nhds

/-- **Converse of BGL Prop. 3.3.17 (p. 162), conditional on `Core2`** (see `STATEMENTS_R15_Converse.md`).
`f ∈ 𝒜 ∩ L²` with `Γ(f), Γ₂(f) ∈ L¹` ⇒ `[f] ∈ 𝒟(L)` and `L[f] = [L f]`.  Hypotheses: `CD(ρ,n)`, ESA (field), and
`Core2` (implicit in the book).  Ergodicity (S10) is not used. -/
theorem mem_domain_of_Γ₂ {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hCore : T.Core2) {f : E → ℝ} (hf : f ∈ T.A)
    (hf2 : MemLp f 2 T.μ) (hG : Integrable (G T f f) T.μ)
    (hG2 : Integrable (T.toDiffusionTriple.Γ₂ f f) T.μ) :
    ∃ hF : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain,
      ((T.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] T.L f := by
  obtain ⟨M, hM⟩ := bound_fLv hCD hf hf2 hG hG2
  obtain ⟨w, hw⟩ := exists_rep (Φₗ T) (Λₗ T hf2) M hM
  have hadj : ∀ a : T.A₀, inner ℝ (hf2.toLp f) (T.toDiffusionTriple.Lcls a) =
      inner ℝ w (T.toDiffusionTriple.cls a) := by
    intro a
    obtain ⟨b, h1, h2⟩ := hCore a
    have l1 : Tendsto (fun k => Λₗ T hf2 (b k)) atTop (𝓝 (inner ℝ w (T.toDiffusionTriple.cls a))) := by
      have : ∀ k, Λₗ T hf2 (b k) = inner ℝ w (T.toDiffusionTriple.cls (b k) - T.toDiffusionTriple.Lcls (b k)) :=
        fun k => hw (b k)
      simp only [this]
      exact tendsto_const_nhds.inner h1
    have l2 : Tendsto (fun k => Λₗ T hf2 (b k)) atTop
        (𝓝 (inner ℝ (hf2.toLp f) (T.toDiffusionTriple.Lcls a))) := by
      have : ∀ k, Λₗ T hf2 (b k) =
          inner ℝ (hf2.toLp f) (T.toDiffusionTriple.Lcls (b k) - LLₗ T (b k)) := fun k => rfl
      simp only [this]
      exact tendsto_const_nhds.inner h2
    exact tendsto_nhds_unique l2 l1
  obtain ⟨hF, hFw⟩ := mem_domain_of_adjoint (T := T) (hf2.toLp f) w hadj
  exact ⟨hF, generator_ae_L hf hf2 hF⟩

end FullTriple

end MarkovTriple.BGL
