import Mathlib
import MarkovTriple.BGL.Basic
import MarkovTriple.Hilbert.Friedrichs

/-!
# The form data of a Diffusion Markov Triple (D7)

For a `DiffusionTriple T` we build, on `H = L²(μ)`, the `FormData` (densely defined, symmetric,
nonnegative operator): `D = {classes of 𝒜₀}`, `A [f] = -[L f]`.  This is the new analogue (with
a.e. fields) of `Hilbert/TripleForm.lean`.

The only non-formal point is that `A` is well defined on classes: if `f = 0` a.e. (`f ∈ 𝒜₀`) then
`L f = 0` a.e.  This follows from integration by parts, `Γ ≥ 0`, bilinearity and symmetry of `Γ`
(Cauchy–Schwarz for the semi-inner product `q(f,g) = ∫ Γ(f,g)`).
-/

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

/-- `f ↦ [f]`, `𝒜₀ → L²(μ)`, linear. -/
noncomputable def clsₗ : T.A₀ →ₗ[ℝ] Lp ℝ 2 T.μ where
  toFun := T.cls
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_cls T (f + g), coeFn_cls T f, coeFn_cls T g,
      Lp.coeFn_add (T.cls f) (T.cls g)] with x h1 h2 h3 h4
    rw [h4, Pi.add_apply, h2, h3]; exact h1
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_cls T (c • f), coeFn_cls T f, Lp.coeFn_smul c (T.cls f)] with x h1 h2 h3
    rw [RingHom.id_apply, h3, Pi.smul_apply, h2]; exact h1

/-- `f ↦ [L f]`, `𝒜₀ → L²(μ)`, linear (by `L_add_ae`, `L_smul_ae`). -/
noncomputable def Lclsₗ : T.A₀ →ₗ[ℝ] Lp ℝ 2 T.μ where
  toFun := T.Lcls
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [coeFn_Lcls T (f + g), coeFn_Lcls T f, coeFn_Lcls T g,
      Lp.coeFn_add (T.Lcls f) (T.Lcls g), L_add_ae T f.2 g.2] with x h1 h2 h3 h4 h5
    rw [h4, Pi.add_apply, h2, h3]; rw [h1]; exact h5
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [coeFn_Lcls T (c • f), coeFn_Lcls T f, Lp.coeFn_smul c (T.Lcls f),
      L_smul_ae T c f.2] with x h1 h2 h3 h4
    rw [RingHom.id_apply, h3, Pi.smul_apply, h2]; rw [h1]; exact h4

/-- The semi-inner product `q(f,g) = ∫ Γ(f,g)`. -/
noncomputable def qf (f g : T.A₀) : ℝ := ∫ x, T.Γ f.1 g.1 x ∂T.μ

lemma Γ_integrable (f g : T.A₀) : Integrable (T.Γ f.1 g.1) T.μ :=
  integrable_of_mem T (T.Γ_mem f.1 f.2 g.1 g.2)

lemma qf_symm (f g : T.A₀) : qf T f g = qf T g f := by
  unfold qf; exact integral_congr_ae (T.Γ_symm f.1 f.2 g.1 g.2)

lemma qf_nonneg (f : T.A₀) : 0 ≤ qf T f f :=
  integral_nonneg_of_ae (T.Γ_nonneg f.1 f.2)

/-- Expansion `Γ(f + s g, f + s g) = Γ(f,f) + 2 s Γ(f,g) + s² Γ(g,g)`, a.e. -/
lemma Γ_expand (f g : T.A₀) (s : ℝ) :
    T.Γ (f.1 + s • g.1) (f.1 + s • g.1) =ᵐ[T.μ]
      T.Γ f.1 f.1 + (2 * s) • T.Γ f.1 g.1 + (s ^ 2) • T.Γ g.1 g.1 := by
  have hsg : s • g.1 ∈ T.A₀ := T.A₀.smul_mem s g.2
  have hfs : f.1 + s • g.1 ∈ T.A₀ := T.A₀.add_mem f.2 hsg
  filter_upwards [T.Γ_add f.1 f.2 (s • g.1) hsg _ hfs, T.Γ_smul s g.1 g.2 _ hfs,
    T.Γ_symm f.1 f.2 _ hfs, T.Γ_add f.1 f.2 (s • g.1) hsg _ f.2, T.Γ_smul s g.1 g.2 _ f.2,
    T.Γ_symm g.1 g.2 _ hfs, T.Γ_add f.1 f.2 (s • g.1) hsg _ g.2, T.Γ_smul s g.1 g.2 _ g.2,
    T.Γ_symm g.1 g.2 f.1 f.2] with x a1 a2 a3 a4 a5 a6 a7 a8 a9
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at *
  rw [a1, a2, a3, a4, a5, a6, a7, a8, a9]; ring

lemma qf_expand (f g : T.A₀) (s : ℝ) :
    qf T (f + s • g) (f + s • g) = qf T f f + 2 * s * qf T f g + s ^ 2 * qf T g g := by
  unfold qf
  have := Γ_expand T f g s
  simp only [NonUnitalSubalgebra.coe_add, NonUnitalSubalgebra.coe_smul]
  rw [integral_congr_ae this]
  have i1 := Γ_integrable T f f
  have i2 := Γ_integrable T f g
  have i3 := Γ_integrable T g g
  have := integral_add (i1.add (i2.smul (2 * s))) (i3.smul (s ^ 2))
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
  rw [this, integral_add i1 (i2.const_mul _), integral_const_mul, integral_const_mul]

/-- A real lemma: if `0 ≤ 2 s a + s² b` for all `s` then `a = 0`. -/
lemma eq_zero_of_forall (a b : ℝ) (hb : 0 ≤ b) (h : ∀ s : ℝ, 0 ≤ 2 * s * a + s ^ 2 * b) :
    a = 0 := by
  have h1 := h (-a / (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b =
      -a ^ 2 * (2 * (b + 1) - b) / (b + 1) ^ 2 := by
    field_simp; ring
  rw [this] at h1
  have h2 : 0 < (2 * (b + 1) - b) / (b + 1) ^ 2 := by
    apply div_pos <;> nlinarith
  have h3 : -a ^ 2 * (2 * (b + 1) - b) / (b + 1) ^ 2 =
      -(a ^ 2 * ((2 * (b + 1) - b) / (b + 1) ^ 2)) := by
    ring
  rw [h3] at h1
  have : a ^ 2 * ((2 * (b + 1) - b) / (b + 1) ^ 2) ≤ 0 := by linarith
  have : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hc h2]
  nlinarith [sq_nonneg a]

/-- density of the test functions in `L²`. -/
lemma dense_range_cls : Dense (LinearMap.range (clsₗ T) : Set (Lp ℝ 2 T.μ)) := by
  have hd := T.dense 2 fact_one_le_two_ennreal (by simp)
  refine hd.mono ?_
  rintro u ⟨f, hf, huf⟩
  refine ⟨⟨f, hf⟩, ?_⟩
  refine Lp.ext ?_
  exact ((coeFn_cls T ⟨f, hf⟩).trans huf.symm)

/-- if `v ∈ L²` is orthogonal to all test functions then `v = 0`. -/
lemma eq_zero_of_orth (v : Lp ℝ 2 T.μ) (h : ∀ g : T.A₀, inner ℝ v (T.cls g) = 0) : v = 0 := by
  have hc : IsClosed {w : Lp ℝ 2 T.μ | inner ℝ v w = 0} :=
    isClosed_eq (by fun_prop) continuous_const
  have hall : ∀ w : Lp ℝ 2 T.μ, inner ℝ v w = 0 := by
    intro w
    have : w ∈ closure (LinearMap.range (clsₗ T) : Set (Lp ℝ 2 T.μ)) := by
      rw [(dense_range_cls T).closure_eq]; trivial
    refine (closure_minimal (fun z hz => ?_) hc) this
    obtain ⟨g, rfl⟩ := hz
    exact h g
  exact inner_self_eq_zero.mp (hall v)

/-- **Well-definedness of `L` on classes.** -/
lemma Lcls_eq_zero_of_cls_eq_zero (f : T.A₀) (hf : T.cls f = 0) : T.Lcls f = 0 := by
  have hae : f.1 =ᵐ[T.μ] 0 := by
    have h1 := coeFn_cls T f
    rw [hf] at h1
    exact h1.symm.trans (Lp.coeFn_zero ℝ 2 T.μ)
  have hqff : qf T f f = 0 := by
    have hibp := T.ibp f.1 f.2 f.1 f.2
    have h0 : ∫ x, f.1 x * T.L f.1 x ∂T.μ = 0 := by
      have : (fun x => f.1 x * T.L f.1 x) =ᵐ[T.μ] 0 := by
        filter_upwards [hae] with x hx
        simp [hx]
      rw [integral_congr_ae this]; simp
    unfold qf
    linarith
  apply eq_zero_of_orth
  intro g
  rw [inner_Lcls_cls]
  have : qf T f g = 0 := by
    apply eq_zero_of_forall (qf T f g) (qf T g g) (qf_nonneg T g)
    intro s
    have h := qf_nonneg T (f + s • g)
    rw [qf_expand, hqff] at h
    linarith
  unfold qf at this
  rw [this]; simp

/-- The densely defined operator `A [f] = -[L f]` on the classes of test functions. -/
noncomputable def formA : LinearMap.range (clsₗ T) →ₗ[ℝ] Lp ℝ 2 T.μ :=
  ((LinearMap.ker (clsₗ T)).liftQ (-(Lclsₗ T)) (by
      intro f hf
      simp only [LinearMap.mem_ker] at hf ⊢
      simpa [Lclsₗ] using Lcls_eq_zero_of_cls_eq_zero T f hf)) ∘ₗ
    (LinearMap.quotKerEquivRange (clsₗ T)).symm.toLinearMap

lemma formA_apply (f : T.A₀) :
    formA T ⟨clsₗ T f, ⟨f, rfl⟩⟩ = -T.Lcls f := by
  unfold formA
  have h := LinearMap.quotKerEquivRange_symm_apply_image (clsₗ T) f
    (⟨f, rfl⟩ : clsₗ T f ∈ LinearMap.range (clsₗ T))
  simp [h, Lclsₗ]

lemma inner_formA (f g : T.A₀) :
    inner ℝ (formA T ⟨clsₗ T f, ⟨f, rfl⟩⟩) (clsₗ T g) = qf T f g := by
  rw [formA_apply, inner_neg_left]
  show -inner ℝ (T.Lcls f) (T.cls g) = _
  rw [inner_Lcls_cls]; simp [qf]

/-- **The form data of a Diffusion Markov Triple.** -/
noncomputable def formData : MarkovTriple.Hilbert.FormData (Lp ℝ 2 T.μ) where
  D := LinearMap.range (clsₗ T)
  dense := dense_range_cls T
  A := formA T
  symm := by
    rintro ⟨_, f, rfl⟩ ⟨_, g, rfl⟩
    show inner ℝ (formA T ⟨clsₗ T f, ⟨f, rfl⟩⟩) (clsₗ T g) =
      inner ℝ (clsₗ T f) (formA T ⟨clsₗ T g, ⟨g, rfl⟩⟩)
    rw [inner_formA, real_inner_comm, inner_formA, qf_symm]
  nonneg := by
    rintro ⟨_, f, rfl⟩
    show 0 ≤ inner ℝ (formA T ⟨clsₗ T f, ⟨f, rfl⟩⟩) (clsₗ T f)
    rw [inner_formA]; exact qf_nonneg T f

end DiffusionTriple

end MarkovTriple.BGL
