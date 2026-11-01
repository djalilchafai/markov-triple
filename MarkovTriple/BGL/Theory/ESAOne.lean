import Mathlib
import MarkovTriple.BGL.Frozen.FullTriple
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Semigroup.ESA

/-!
# ESA gives `P_t 1 = 1` for a finite measure (mass conservation, finite case)

`DiffusionTriple.ESAProp T` is the statement of F10 (`𝒜₀` is a core for the Friedrichs generator),
for a bare diffusion triple.  For finite `μ` we prove, **without any curvature hypothesis and without
S11**: `1 ∈ 𝒟(L)`, `L 1 = 0`, `P_t 1 = 1`, and the S11 statement itself (`conservative_of_esa`).
The only inputs are D8 (`∫ L f = 0`), ESA and the self-adjointness of the Friedrichs generator.
(For infinite `μ` this fails in general; the book's Thm 3.3.23 needs completeness + CD(ρ,∞),
see `Theory/Conservative.lean`.)
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace LinearPMap

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- F10 (ESA, core form) for a bare diffusion triple. -/
def DiffusionTriple.ESAProp (T : DiffusionTriple E) : Prop :=
  ∀ (u : Lp ℝ 2 T.μ) (hu : u ∈ T.generator.domain),
    ∃ a : ℕ → T.A₀, Tendsto (fun n => T.cls (a n)) atTop (𝓝 u) ∧
      Tendsto (fun n => T.Lcls (a n)) atTop (𝓝 (T.generator ⟨u, hu⟩))

theorem FullTriple.esaProp {E : Type*} [MeasurableSpace E] (T : FullTriple E) :
    T.toDiffusionTriple.ESAProp := T.esa

namespace DiffusionTriple

variable (T : DiffusionTriple E) [IsFiniteMeasure T.μ]

/-- `⟪L a, 1⟫ = ∫ L a = 0` (D8). -/
lemma inner_Lcls_one2 (a : T.A₀) : inner ℝ (T.Lcls a) T.one2 = 0 := by
  rw [L2_inner_eq]
  have : ∫ x, (T.Lcls a : E → ℝ) x * (T.one2 : E → ℝ) x ∂T.μ = ∫ x, T.L a.1 x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_Lcls T a, T.coeFn_one2] with x h1 h2
    rw [h1, h2, mul_one]
  rw [this]; exact T.integral_L a.1 a.2

/-- Under ESA, `⟪G v, 1⟫ = 0` for all `v ∈ 𝒟(G)`. -/
lemma inner_generator_one2 (hesa : T.ESAProp) (v : Lp ℝ 2 T.μ) (hv : v ∈ T.generator.domain) :
    inner ℝ (T.generator ⟨v, hv⟩) T.one2 = 0 := by
  obtain ⟨a, -, ha2⟩ := hesa v hv
  have h1 : Tendsto (fun k => inner ℝ (T.Lcls (a k)) T.one2) atTop
      (𝓝 (inner ℝ (T.generator ⟨v, hv⟩) T.one2)) := ha2.inner tendsto_const_nhds
  simp only [inner_Lcls_one2] at h1
  exact (tendsto_nhds_unique h1 tendsto_const_nhds).symm ▸ rfl

/-- **ESA ⇒ `R 1 = 1`** (finite measure). -/
theorem R_one2 (hesa : T.ESAProp) : (formData T).R T.one2 = T.one2 := by
  set S := formData T
  have key : ∀ w : Lp ℝ 2 T.μ, inner ℝ w (S.R T.one2 - T.one2) = 0 := by
    intro w
    obtain ⟨h, hG⟩ := S.generator_R w
    have h0 := T.inner_generator_one2 hesa (S.R w) h
    have hG' : (T.generator ⟨S.R w, h⟩ : Lp ℝ 2 T.μ) = S.R w - w := hG
    rw [hG', inner_sub_left] at h0
    have hsa := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp S.R_isSelfAdjoint w T.one2
    rw [inner_sub_right]
    have : inner ℝ (S.R w) T.one2 = inner ℝ w (S.R T.one2) := hsa
    linarith
  have := key (S.R T.one2 - T.one2)
  exact sub_eq_zero.mp (inner_self_eq_zero.mp this)

/-- **`1 ∈ 𝒟(L)`, `L 1 = 0`** (finite measure, ESA). -/
theorem one2_mem_domain (hesa : T.ESAProp) :
    ∃ h : T.one2 ∈ T.generator.domain, T.generator ⟨T.one2, h⟩ = 0 := by
  have hR := R_one2 T hesa
  have h : T.one2 ∈ T.generator.domain :=
    ((formData T).mem_domain_generator_iff _).2 ⟨0, by rw [sub_zero]; exact hR⟩
  exact ⟨h, ((formData T).generator_apply_eq_iff h 0).2 (by rw [sub_zero]; exact hR)⟩

/-- **`P_t 1 = 1`** for a finite measure under ESA (no S11, no curvature). -/
theorem semigroup_one2 (hesa : T.ESAProp) (t : ℝ≥0) : T.semigroup t T.one2 = T.one2 := by
  have hR : (formData T).R T.one2 = ((1 + (0 : ℝ))⁻¹) • T.one2 := by
    rw [R_one2 T hesa]; simp
  have := (formData T).semigroup_eigen (le_refl (0 : ℝ)) hR t
  simpa [semigroup] using this

/-- **Mass conservation, finite case (S11 derived).**  For a diffusion triple with finite `μ` and
ESA, S11 holds for every exhaustion sequence: `P_t u_n → 1` a.e. -/
theorem conservative_of_esa (hesa : T.ESAProp) {u : ℕ → E → ℝ} (hu : IsExhaustion T.μ T.A₀ u)
    (t : ℝ≥0) :
    ∀ᵐ x ∂T.μ, Tendsto (fun n => (T.semigroup t (T.cls ⟨u n, hu.1 n⟩) : E → ℝ) x) atTop (𝓝 1) :=
  (T.conservative_iff_semigroup_one hu t).2 (T.semigroup_one2 hesa t)

end DiffusionTriple

end MarkovTriple.BGL
