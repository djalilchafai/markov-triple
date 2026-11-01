import Mathlib
import MarkovTriple.BGL.Frozen.StandardTriple
import MarkovTriple.BGL.Frozen.FormDomain
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Semigroup.Markov

/-!
# Characterisation of the generator by the closed form; second form of ergodicity (S10)

(Not frozen; these are the theorems that pin down the meaning of the *definitions*
`DiffusionTriple.generator`, `.formDomain`, `.closedForm` (audit item M1) independently of how they
are constructed.)

* `Hilbert.FormData.generator_iff_form` (abstract, any `FormData`): `u ∈ 𝒟(G)` and `G u = y` iff
  `u ∈ Q` and `E(u, v) = −⟪y, v⟫` for all `v ∈ Q`.
* `DiffusionTriple.generator_iff_form`: the same for a diffusion triple.  This is the book's
  characterisation of `𝒟(L)` in D7 (`𝒟(L) = {u ∈ 𝒟(ℰ) : ∃ y ∈ L², ℰ(u,v) = −⟪y,v⟫ ∀ v ∈ 𝒟(ℰ)}`);
  together with `𝒜₀ ⊂ 𝒟(L)`, `L = L|𝒜₀` on `𝒜₀` (`generator_cls`), and the fact that `ℰ` is the closure
  of `ℰ(f,g) = ∫Γ(f,g)` (`closedForm_cls`), it determines `generator` as the Friedrichs generator.
* `DiffusionTriple.ergodic_iff_energy`: S10 (`u ∈ 𝒟(L)`, `Lu = 0` ⇒ const) is equivalent to the
  second form of the book (`u ∈ 𝒟(ℰ)`, `ℰ(u) = 0` ⇒ const; for `u ∈ 𝒜₀`, `ℰ(u) = ∫Γ(u)` and
  `Γ(u) ≥ 0`, so `ℰ(u) = 0 ⇔ Γ(u) = 0` a.e.: `energy_zero_iff`).
-/

open MeasureTheory
open scoped NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.Hilbert.FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- The domain of the generator lies in the form domain, and `E(u,v) = −⟪G u, v⟫`. -/
theorem generator_mem_Q_and_form {u : H} (hu : u ∈ S.generator.domain) :
    ∃ hQ : u ∈ S.Q, ∀ φ : S.Q, S.E ⟨u, hQ⟩ φ = -inner ℝ (S.generator ⟨u, hu⟩) (φ : H) := by
  have hR : S.R (u - S.generator ⟨u, hu⟩) = u := (S.generator_apply_eq_iff hu _).1 rfl
  have hQ : u ∈ S.Q := by rw [← hR]; exact S.R_mem_Q _
  refine ⟨hQ, fun φ => ?_⟩
  have h := S.E_R (u - S.generator ⟨u, hu⟩) φ
  have e : (⟨S.R (u - S.generator ⟨u, hu⟩), S.R_mem_Q _⟩ : S.Q) = ⟨u, hQ⟩ := Subtype.ext hR
  rw [e, hR, inner_sub_left] at h
  linarith

/-- Converse: if `u ∈ Q` and `E(u, v) = −⟪y, v⟫` for all `v ∈ Q`, then `u ∈ 𝒟(G)` and `G u = y`. -/
theorem generator_of_form {u y : H} (hQ : u ∈ S.Q)
    (h : ∀ φ : S.Q, S.E ⟨u, hQ⟩ φ = -inner ℝ y (φ : H)) :
    ∃ hu : u ∈ S.generator.domain, S.generator ⟨u, hu⟩ = y := by
  have hR : u = S.R (u - y) := by
    refine S.eq_R_of_weak hQ (u - y) (fun φ => ?_)
    have := h φ
    unfold E at this
    simp only at this
    rw [inner_sub_left]
    linarith
  have hu : u ∈ S.generator.domain := (S.mem_domain_generator_iff u).2 ⟨y, hR.symm⟩
  exact ⟨hu, (S.generator_apply_eq_iff hu y).2 hR.symm⟩

/-- **Generator ⇔ form.** -/
theorem generator_iff_form (u y : H) :
    (∃ hu : u ∈ S.generator.domain, S.generator ⟨u, hu⟩ = y) ↔
      ∃ hQ : u ∈ S.Q, ∀ φ : S.Q, S.E ⟨u, hQ⟩ φ = -inner ℝ y (φ : H) := by
  constructor
  · rintro ⟨hu, rfl⟩
    exact S.generator_mem_Q_and_form hu
  · rintro ⟨hQ, h⟩
    exact S.generator_of_form hQ h

/-- Cauchy–Schwarz consequence: `E(u,u) = 0` forces `E(u,φ) = 0`. -/
theorem E_eq_zero_of_self_eq_zero (u : S.Q) (h : S.E u u = 0) (φ : S.Q) : S.E u φ = 0 := by
  have key : ∀ c : ℝ, 0 ≤ 2 * c * (-S.E u φ) + c ^ 2 * S.E φ φ := by
    intro c
    have h1 := S.E_nonneg (u - c • φ)
    rw [S.E_sub_smul_self, h] at h1
    linarith
  have a : -S.E u φ = 0 := by
    by_contra hne
    set a := -S.E u φ
    set b := S.E φ φ
    have hb := S.E_nonneg φ
    have h1 := key (-a / (b + 1))
    have hb1 : 0 < b + 1 := by linarith
    have : 2 * (-a / (b + 1)) * a + (-a / (b + 1)) ^ 2 * b =
        -a ^ 2 * (2 * (b + 1) - b) / (b + 1) ^ 2 := by field_simp; ring
    rw [this] at h1
    have h2 : 0 < a ^ 2 := by positivity
    have h3 : 0 < (2 * (b + 1) - b) / (b + 1) ^ 2 := by apply div_pos <;> nlinarith
    have : -a ^ 2 * (2 * (b + 1) - b) / (b + 1) ^ 2 = -(a ^ 2 * ((2 * (b + 1) - b) / (b + 1) ^ 2)) := by
      ring
    rw [this] at h1
    nlinarith [mul_pos h2 h3]
  linarith

end MarkovTriple.Hilbert.FormData

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

/-- **Characterisation of the generator** (BGL D7): `u ∈ 𝒟(L)` with `L u = y` iff `u ∈ 𝒟(ℰ)` and
`ℰ(u, v) = −⟪y, v⟫` for every `v ∈ 𝒟(ℰ)`. -/
theorem generator_iff_form (u y : Lp ℝ 2 T.μ) :
    (∃ hu : u ∈ T.generator.domain, T.generator ⟨u, hu⟩ = y) ↔
      ∃ hQ : u ∈ T.formDomain, ∀ v : T.formDomain,
        T.closedForm ⟨u, hQ⟩ v = -inner ℝ y (v : Lp ℝ 2 T.μ) :=
  (formData T).generator_iff_form u y

/-- `ℰ` extends `ℰ(f,g) = ∫ Γ(f,g)` on test functions. -/
theorem closedForm_cls (f g : T.A₀) :
    T.closedForm ⟨T.cls f, (formData T).emb_mem_Q ⟨clsₗ T f, ⟨f, rfl⟩⟩⟩
      ⟨T.cls g, (formData T).emb_mem_Q ⟨clsₗ T g, ⟨g, rfl⟩⟩⟩ = ∫ x, T.Γ f.1 g.1 x ∂T.μ :=
  (formData T).E_emb ⟨clsₗ T f, ⟨f, rfl⟩⟩ ⟨clsₗ T g, ⟨g, rfl⟩⟩ |>.trans (inner_formA T f g)

/-- For a test function, `ℰ(f) = 0 ⇔ Γ(f) = 0` a.e. -/
theorem energy_zero_iff (f : T.A₀) : ∫ x, T.Γ f.1 f.1 x ∂T.μ = 0 ↔ T.Γ f.1 f.1 =ᵐ[T.μ] 0 := by
  constructor
  · intro h
    exact (integral_eq_zero_iff_of_nonneg_ae (T.Γ_nonneg f.1 f.2) (Γ_integrable T f f)).1 h
  · intro h
    rw [integral_congr_ae h]; simp

/-- **S10, second form.**  Ergodicity in the sense of Def. 3.1.11 (`u ∈ 𝒟(L)`, `L u = 0` ⇒ const) is
equivalent to the form version (`u ∈ 𝒟(ℰ)`, `ℰ(u) = 0` ⇒ const). -/
theorem ergodic_iff_energy :
    (∀ (u : Lp ℝ 2 T.μ) (hu : u ∈ T.generator.domain), T.generator ⟨u, hu⟩ = 0 →
        ∃ c : ℝ, (u : E → ℝ) =ᵐ[T.μ] fun _ => c) ↔
      (∀ u : T.formDomain, T.closedForm u u = 0 → ∃ c : ℝ, ((u : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] fun _ => c) := by
  constructor
  · intro h u hE
    have hzero : ∀ v : T.formDomain, T.closedForm u v = -inner ℝ (0 : Lp ℝ 2 T.μ) (v : Lp ℝ 2 T.μ) := by
      intro v
      rw [inner_zero_left, neg_zero]
      exact (formData T).E_eq_zero_of_self_eq_zero u hE v
    obtain ⟨hu, hG⟩ := (T.generator_iff_form u 0).2 ⟨u.2, hzero⟩
    exact h u hu hG
  · intro h u hu hG
    obtain ⟨hQ, hform⟩ := (T.generator_iff_form u 0).1 ⟨hu, hG⟩
    refine h ⟨u, hQ⟩ ?_
    have := hform ⟨u, hQ⟩
    rw [inner_zero_left, neg_zero] at this
    exact this

end DiffusionTriple

/-- S10 in the form version, for a standard triple. -/
theorem StandardTriple.energy_zero_const (S : StandardTriple E) (u : S.formDomain)
    (h : S.toDiffusionTriple.closedForm u u = 0) :
    ∃ c : ℝ, ((u : Lp ℝ 2 S.μ) : E → ℝ) =ᵐ[S.μ] fun _ => c :=
  (S.toDiffusionTriple.ergodic_iff_energy.1 S.ergodic) u h

end MarkovTriple.BGL
