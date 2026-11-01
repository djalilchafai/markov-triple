import Mathlib
import MarkovTriple.Frozen.MarkovTriple
import MarkovTriple.Hilbert.Friedrichs

/-!
# The form data of a Markov triple

For a Markov triple `T` (`Frozen/MarkovTriple.lean`) we build, on `H = L²(μ)`, the
`FormData` (densely defined, symmetric, nonnegative operator)
`D = {classes of 𝒜₀}`, `A [f] = -[L f]`.

The only non-formal point is that `A` is well defined on classes: if `f = 0` a.e. (`f ∈ 𝒜₀`) then
`L f = 0` a.e.  This is proved from integration by parts, `Γ ≥ 0`, the (first-variable) bilinearity
of `Γ`, its symmetry, and density of `𝒜₀` (Cauchy–Schwarz for the semi-inner product
`q(f,g) = ∫ Γ(f,g)`).  `⟪A f, g⟫ = ∫ Γ(f,g)` (`inner_A_toLp0`).
-/

open MeasureTheory
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E] (T : _root_.MarkovTriple E)

section Basic

lemma memLp2 {f : E → ℝ} (hf : f ∈ T.A₀) : MemLp f 2 T.μ := T.memLp f hf 2 (by simp)

lemma integrable_of_mem {f : E → ℝ} (hf : f ∈ T.A₀) : Integrable f T.μ :=
  memLp_one_iff_integrable.1 (T.memLp f hf 1 (by simp))

/-- Test functions as elements of `L²(μ)`. -/
noncomputable def toLp0 : T.A₀ →ₗ[ℝ] Lp ℝ 2 T.μ where
  toFun f := (memLp2 T f.2).toLp f.1
  map_add' f g := by
    have := MemLp.toLp_add (memLp2 T f.2) (memLp2 T g.2)
    exact this
  map_smul' c f := by
    have := MemLp.toLp_const_smul (𝕜 := ℝ) c (memLp2 T f.2)
    exact this

/-- `L` on test functions, with values in `L²(μ)`. -/
noncomputable def Lt0 : T.A₀ →ₗ[ℝ] Lp ℝ 2 T.μ where
  toFun f := (memLp2 T (T.L_mem f.1 f.2)).toLp (T.L f.1)
  map_add' f g := by
    have h := MemLp.toLp_add (memLp2 T (T.L_mem f.1 f.2)) (memLp2 T (T.L_mem g.1 g.2))
    have e : T.L (f.1 + g.1) = T.L f.1 + T.L g.1 := T.L_add f.1 f.2 g.1 g.2
    simp only [Subalgebra.coe_add, e]
    exact h
  map_smul' c f := by
    have h := MemLp.toLp_const_smul (𝕜 := ℝ) c (memLp2 T (T.L_mem f.1 f.2))
    have e : T.L (c • f.1) = c • T.L f.1 := T.L_smul c f.1 f.2
    simp only [Subalgebra.coe_smul, RingHom.id_apply, e]
    exact h

lemma toLp0_apply (f : T.A₀) : toLp0 T f = (memLp2 T f.2).toLp f.1 := rfl
lemma Lt0_apply (f : T.A₀) : Lt0 T f = (memLp2 T (T.L_mem f.1 f.2)).toLp (T.L f.1) := rfl

lemma coeFn_toLp0 (f : T.A₀) : (toLp0 T f : E → ℝ) =ᵐ[T.μ] f.1 :=
  MemLp.coeFn_toLp (memLp2 T f.2)
lemma coeFn_Lt0 (f : T.A₀) : (Lt0 T f : E → ℝ) =ᵐ[T.μ] T.L f.1 :=
  MemLp.coeFn_toLp (memLp2 T (T.L_mem f.1 f.2))

/-- `⟪L f, g⟫ = ∫ g L f = -∫ Γ(f,g)` (integration by parts). -/
lemma inner_Lt0_toLp0 (f g : T.A₀) :
    inner ℝ (Lt0 T f) (toLp0 T g) = -∫ x, T.Γ f.1 g.1 x ∂T.μ := by
  rw [MeasureTheory.L2.inner_def, ← T.ibp f.1 f.2 g.1 g.2]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_Lt0 T f, coeFn_toLp0 T g] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- The semi-inner product `q(f,g) = ∫ Γ(f,g)`. -/
noncomputable def qf (f g : T.A₀) : ℝ := ∫ x, T.Γ f.1 g.1 x ∂T.μ

lemma Γ_integrable (f g : T.A₀) : Integrable (T.Γ f.1 g.1) T.μ :=
  integrable_of_mem T (T.Γ_mem f.1 f.2 g.1 g.2)

lemma qf_symm (f g : T.A₀) : qf T f g = qf T g f := by
  unfold qf; rw [T.Γ_symm f.1 f.2 g.1 g.2]

lemma qf_nonneg (f : T.A₀) : 0 ≤ qf T f f :=
  integral_nonneg (fun x => T.Γ_nonneg f.1 f.2 x)

/-- Expansion `Γ(f + s g, f + s g) = Γ(f,f) + 2 s Γ(f,g) + s² Γ(g,g)`. -/
lemma Γ_expand (f g : T.A₀) (s : ℝ) :
    T.Γ (f.1 + s • g.1) (f.1 + s • g.1) =
      T.Γ f.1 f.1 + (2 * s) • T.Γ f.1 g.1 + (s ^ 2) • T.Γ g.1 g.1 := by
  have hsg : s • g.1 ∈ T.A₀ := T.A₀.smul_mem g.2 s
  have hfs : f.1 + s • g.1 ∈ T.A₀ := T.A₀.add_mem f.2 hsg
  have e1 : T.Γ (f.1 + s • g.1) (f.1 + s • g.1) =
      T.Γ f.1 (f.1 + s • g.1) + s • T.Γ g.1 (f.1 + s • g.1) := by
    rw [T.Γ_add f.1 f.2 (s • g.1) hsg _ hfs, T.Γ_smul s g.1 g.2 _ hfs]
  have e2 : T.Γ f.1 (f.1 + s • g.1) = T.Γ f.1 f.1 + s • T.Γ g.1 f.1 := by
    rw [T.Γ_symm f.1 f.2 _ hfs, T.Γ_add f.1 f.2 (s • g.1) hsg _ f.2, T.Γ_smul s g.1 g.2 _ f.2]
  have e3 : T.Γ g.1 (f.1 + s • g.1) = T.Γ f.1 g.1 + s • T.Γ g.1 g.1 := by
    rw [T.Γ_symm g.1 g.2 _ hfs, T.Γ_add f.1 f.2 (s • g.1) hsg _ g.2, T.Γ_smul s g.1 g.2 _ g.2]
  rw [e1, e2, e3, T.Γ_symm g.1 g.2 f.1 f.2]
  funext x
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma qf_expand (f g : T.A₀) (s : ℝ) :
    qf T (f + s • g) (f + s • g) = qf T f f + 2 * s * qf T f g + s ^ 2 * qf T g g := by
  unfold qf
  have := Γ_expand T f g s
  simp only [Subalgebra.coe_add, Subalgebra.coe_smul]
  rw [this]
  have i1 := Γ_integrable T f f
  have i2 := Γ_integrable T f g
  have i3 := Γ_integrable T g g
  have h1 : ∫ x, (T.Γ f.1 f.1 + (2 * s) • T.Γ f.1 g.1 + (s ^ 2) • T.Γ g.1 g.1) x ∂T.μ =
      ∫ x, T.Γ f.1 f.1 x ∂T.μ + (2 * s) * ∫ x, T.Γ f.1 g.1 x ∂T.μ +
        s ^ 2 * ∫ x, T.Γ g.1 g.1 x ∂T.μ := by
    have := integral_add (i1.add (i2.smul (2 * s))) (i3.smul (s ^ 2))
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    rw [this, integral_add i1 (i2.const_mul _), integral_const_mul, integral_const_mul]
  exact h1

/-- A real lemma: if `0 ≤ 2 s a + s² b` for all `s` then `a = 0`. -/
lemma eq_zero_of_forall (a b : ℝ) (hb : 0 ≤ b) (h : ∀ s : ℝ, 0 ≤ 2 * s * a + s ^ 2 * b) : a = 0 := by
  have h1 := h (-a / (b + 1))
  have hb1 : 0 < b + 1 := by linarith
  have : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b = -a ^ 2 * (2 * (b + 1) - b) / (b + 1) ^ 2 := by
    field_simp; ring
  rw [this] at h1
  have h2 : 0 < (2 * (b + 1) - b) / (b + 1) ^ 2 := by
    apply div_pos <;> nlinarith
  have h3 : -a ^ 2 * (2 * (b + 1) - b) / (b + 1) ^ 2 = -(a ^ 2 * ((2 * (b + 1) - b) / (b + 1) ^ 2)) := by
    ring
  rw [h3] at h1
  have : a ^ 2 * ((2 * (b + 1) - b) / (b + 1) ^ 2) ≤ 0 := by linarith
  have : a ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    nlinarith [mul_pos hc h2]
  nlinarith [sq_nonneg a]

/-- density of the test functions in `L²`. -/
lemma dense_range_toLp0 : Dense (LinearMap.range (toLp0 T) : Set (Lp ℝ 2 T.μ)) := by
  have hd := T.dense 2 fact_one_le_two_ennreal (by simp)
  refine hd.mono ?_
  rintro u ⟨f, hf, huf⟩
  refine ⟨⟨f, hf⟩, ?_⟩
  refine Lp.ext ?_
  exact ((coeFn_toLp0 T ⟨f, hf⟩).trans huf.symm)

/-- if `v ∈ L²` is orthogonal to all test functions then `v = 0`. -/
lemma eq_zero_of_orth (v : Lp ℝ 2 T.μ) (h : ∀ g : T.A₀, inner ℝ v (toLp0 T g) = 0) : v = 0 := by
  have hc : IsClosed {w : Lp ℝ 2 T.μ | inner ℝ v w = 0} := isClosed_eq (by fun_prop) continuous_const
  have hall : ∀ w : Lp ℝ 2 T.μ, inner ℝ v w = 0 := by
    intro w
    have : w ∈ closure (LinearMap.range (toLp0 T) : Set (Lp ℝ 2 T.μ)) := by
      rw [(dense_range_toLp0 T).closure_eq]; trivial
    refine (closure_minimal (fun z hz => ?_) hc) this
    obtain ⟨g, rfl⟩ := hz
    exact h g
  exact inner_self_eq_zero.mp (hall v)

/-- **Well-definedness of `L` on classes.** -/
lemma Lt0_eq_zero_of_toLp0_eq_zero (f : T.A₀) (hf : toLp0 T f = 0) : Lt0 T f = 0 := by
  have hae : f.1 =ᵐ[T.μ] 0 := by
    have h1 := coeFn_toLp0 T f
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
  rw [inner_Lt0_toLp0]
  have : qf T f g = 0 := by
    apply eq_zero_of_forall (qf T f g) (qf T g g) (qf_nonneg T g)
    intro s
    have h := qf_nonneg T (f + s • g)
    rw [qf_expand, hqff] at h
    linarith
  unfold qf at this
  rw [this]; simp

/-- The densely defined operator `A [f] = -[L f]` on the classes of test functions. -/
noncomputable def formA : LinearMap.range (toLp0 T) →ₗ[ℝ] Lp ℝ 2 T.μ :=
  ((LinearMap.ker (toLp0 T)).liftQ (-(Lt0 T)) (by
      intro f hf
      simp only [LinearMap.mem_ker] at hf ⊢
      simp [Lt0_eq_zero_of_toLp0_eq_zero T f hf])) ∘ₗ
    (LinearMap.quotKerEquivRange (toLp0 T)).symm.toLinearMap

lemma formA_apply (f : T.A₀) :
    formA T ⟨toLp0 T f, ⟨f, rfl⟩⟩ = -Lt0 T f := by
  unfold formA
  have h := LinearMap.quotKerEquivRange_symm_apply_image (toLp0 T) f (⟨f, rfl⟩ : toLp0 T f ∈ LinearMap.range (toLp0 T))
  simp [h]

lemma inner_formA (f g : T.A₀) :
    inner ℝ (formA T ⟨toLp0 T f, ⟨f, rfl⟩⟩) (toLp0 T g) = qf T f g := by
  rw [formA_apply, inner_neg_left, inner_Lt0_toLp0]; simp [qf]

/-- **The form data of a Markov triple.** -/
noncomputable def formData : Hilbert.FormData (Lp ℝ 2 T.μ) where
  D := LinearMap.range (toLp0 T)
  dense := dense_range_toLp0 T
  A := formA T
  symm := by
    rintro ⟨_, f, rfl⟩ ⟨_, g, rfl⟩
    show inner ℝ (formA T ⟨toLp0 T f, ⟨f, rfl⟩⟩) (toLp0 T g) =
      inner ℝ (toLp0 T f) (formA T ⟨toLp0 T g, ⟨g, rfl⟩⟩)
    rw [inner_formA, real_inner_comm, inner_formA, qf_symm]
  nonneg := by
    rintro ⟨_, f, rfl⟩
    show 0 ≤ inner ℝ (formA T ⟨toLp0 T f, ⟨f, rfl⟩⟩) (toLp0 T f)
    rw [inner_formA]; exact qf_nonneg T f

end Basic

end MarkovTriple.Hilbert
