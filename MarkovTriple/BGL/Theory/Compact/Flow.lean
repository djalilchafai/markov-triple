import Mathlib
import MarkovTriple.BGL.Theory.Compact.Product
import MarkovTriple.BGL.Theory.GradientBound
import MarkovTriple.BGL.Theory.LogSobolev
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.SemigroupLemmas

/-!
# The heat flow of a test function on a compact triple, in `L²`

For a `CompactTriple` (`𝒜 = 𝒜₀`, so `P_t f ∈ 𝒜₀`, F8) and `ψ ∈ 𝒜₀`, the orbit
`orb ψ s = P_s [ψ]` is an `L²`-differentiable curve (`hasDerivAt_orb`: `d/ds P_s[ψ] = P_s[Lψ]`, `s > 0`),
continuous on `ℝ`, essentially bounded by `‖ψ‖_∞`, and its `𝒜₀`-representative `Pt s ψ` satisfies
`L (Pt s ψ) = P_s [Lψ]` a.e. (`L_Pt`).  These are the inputs to the differentiation of the interpolation
functions of `Theory/GradientBound.lean` and `Theory/LogSobolev.lean`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace CompactTriple

variable (C : CompactTriple E)

lemma mem_A₀ {f : E → ℝ} (hf : f ∈ C.A) : f ∈ C.A₀ := (C.A_eq f).1 hf

/-- `L ψ` as a test function. -/
def Lt (ψ : C.A₀) : C.A₀ := ⟨C.L ψ.1, C.toDiffusionTriple.L_mem ψ.1 ψ.2⟩

/-- the orbit `s ↦ P_s [ψ]` of a test function (constant `[ψ]` for `s ≤ 0`). -/
noncomputable def orb (ψ : C.A₀) (s : ℝ) : Lp ℝ 2 C.μ :=
  C.toDiffusionTriple.semigroup s.toNNReal (C.toDiffusionTriple.cls ψ)

lemma cls_Lt (ψ : C.A₀) : C.toDiffusionTriple.cls (C.Lt ψ) = C.toDiffusionTriple.Lcls ψ := by
  refine Lp.ext ?_
  exact (DiffusionTriple.coeFn_cls C.toDiffusionTriple (C.Lt ψ)).trans
    (DiffusionTriple.coeFn_Lcls C.toDiffusionTriple ψ).symm

lemma continuous_orb (ψ : C.A₀) : Continuous (C.orb ψ) :=
  (C.toDiffusionTriple.continuous_semigroup_apply _).comp continuous_real_toNNReal

lemma orb_zero (ψ : C.A₀) : C.orb ψ 0 = C.toDiffusionTriple.cls ψ := by
  simp [orb, DiffusionTriple.semigroup_zero]

/-- `d/ds P_s [ψ] = P_s [Lψ]` for `s > 0`. -/
theorem hasDerivAt_orb (ψ : C.A₀) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (C.orb ψ) (C.orb (C.Lt ψ) s) s := by
  have h := (DiffusionTriple.formData C.toDiffusionTriple).hasDerivAt_semigroup hs
    (C.toDiffusionTriple.cls ψ - C.toDiffusionTriple.Lcls ψ)
  rw [DiffusionTriple.R_cls_sub C.toDiffusionTriple ψ] at h
  have e : C.toDiffusionTriple.cls ψ - C.toDiffusionTriple.Lcls ψ - C.toDiffusionTriple.cls ψ =
      -C.toDiffusionTriple.Lcls ψ := by abel
  rw [e, map_neg, neg_neg] at h
  unfold orb
  rw [cls_Lt]
  exact h

/-- `|u| ≤ c` a.e. ⇒ `|P_t u| ≤ c` a.e. (sub-Markov + positivity). -/
lemma ae_abs_semigroup_le {c : ℝ} (hc : 0 < c) {u : Lp ℝ 2 C.μ}
    (hu : ∀ᵐ x ∂C.μ, |(u : E → ℝ) x| ≤ c) (t : ℝ≥0) :
    ∀ᵐ x ∂C.μ, |(C.toDiffusionTriple.semigroup t u : E → ℝ) x| ≤ c := by
  have key : ∀ v : Lp ℝ 2 C.μ, (∀ᵐ x ∂C.μ, (v : E → ℝ) x ≤ c) →
      ∀ᵐ x ∂C.μ, (C.toDiffusionTriple.semigroup t v : E → ℝ) x ≤ c := by
    intro v hv
    have h1 : ((c⁻¹ • v : Lp ℝ 2 C.μ) : E → ℝ) ≤ᵐ[C.μ] (1 : E → ℝ) := by
      filter_upwards [Lp.coeFn_smul c⁻¹ v, hv] with x h1 h2
      rw [h1]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      rw [inv_mul_le_iff₀ hc]; simpa using h2
    have h2 := C.toDiffusionTriple.semigroup_le_one t _ h1
    rw [map_smul] at h2
    filter_upwards [h2, Lp.coeFn_smul c⁻¹ (C.toDiffusionTriple.semigroup t v)] with x h3 h4
    rw [h4] at h3
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h3
    rw [inv_mul_le_iff₀ hc] at h3; simpa using h3
  have h1 := key u (hu.mono fun x hx => (le_abs_self _).trans hx)
  have h2 := key (-u) (by
    filter_upwards [hu, Lp.coeFn_neg u] with x hx h
    rw [h]; simpa using (neg_le_abs _).trans hx)
  filter_upwards [h1, h2, Lp.coeFn_neg (C.toDiffusionTriple.semigroup t u),
    (by rw [map_neg]; exact Lp.coeFn_neg (C.toDiffusionTriple.semigroup t u) :
      (C.toDiffusionTriple.semigroup t (-u) : E → ℝ) =ᵐ[C.μ]
        -(C.toDiffusionTriple.semigroup t u : E → ℝ))] with x a b _ d
  rw [d] at b
  simp only [Pi.neg_apply] at b
  rw [abs_le]; constructor <;> linarith

/-- a bound for the test function `ψ`, positive. -/
lemma exists_bound (ψ : C.A₀) : ∃ c : ℝ, 0 < c ∧ ∀ x, |ψ.1 x| ≤ c := by
  obtain ⟨c, hc⟩ := C.bounded ψ.1 ψ.2
  exact ⟨|c| + 1, by positivity, fun x => (hc x).trans (by linarith [le_abs_self c])⟩

lemma orb_bdd {ψ : C.A₀} {c : ℝ} (hc : 0 < c) (hψ : ∀ x, |ψ.1 x| ≤ c) (s : ℝ) :
    Compact.Bdd c (C.orb ψ s) := by
  refine C.ae_abs_semigroup_le hc ?_ _
  filter_upwards [DiffusionTriple.coeFn_cls C.toDiffusionTriple ψ] with x hx
  rw [hx]; exact hψ x

/-- the `𝒜₀`-representative of the orbit. -/
lemma orb_ae (ψ : C.A₀) (s : ℝ) : (C.orb ψ s : E → ℝ) =ᵐ[C.μ] C.Pt s.toNNReal ψ :=
  C.Pt_ae s.toNNReal ψ

lemma Pt_mem (t : ℝ≥0) (ψ : C.A₀) : C.Pt t ψ ∈ C.A₀ := C.mem_A₀ (C.Pt_mem_A t ψ)

/-- `L (P_s ψ) = P_s (Lψ)` for the representative. -/
theorem L_Pt (ψ : C.A₀) (s : ℝ) :
    C.L (C.Pt s.toNNReal ψ) =ᵐ[C.μ] (C.orb (C.Lt ψ) s : E → ℝ) := by
  have hp0 : C.Pt s.toNNReal ψ ∈ C.A₀ := C.Pt_mem _ ψ
  have hcls : C.toDiffusionTriple.cls ⟨C.Pt s.toNNReal ψ, hp0⟩ = C.orb ψ s :=
    Lp.ext ((DiffusionTriple.coeFn_cls C.toDiffusionTriple ⟨C.Pt s.toNNReal ψ, hp0⟩).trans
      (C.orb_ae ψ s).symm)
  obtain ⟨hdom, hG⟩ := (DiffusionTriple.formData C.toDiffusionTriple).semigroup_generator_comm
    (C.toDiffusionTriple.cls_mem_generator_domain ψ) s.toNNReal
  have hGa : C.toDiffusionTriple.generator ⟨C.toDiffusionTriple.cls ψ,
      C.toDiffusionTriple.cls_mem_generator_domain ψ⟩ = C.toDiffusionTriple.Lcls ψ :=
    C.toDiffusionTriple.generator_cls ψ _
  have hG' : C.toDiffusionTriple.generator ⟨C.orb ψ s, hdom⟩ =
      C.orb (C.Lt ψ) s := by
    have : C.toDiffusionTriple.generator ⟨C.orb ψ s, hdom⟩ =
        C.toDiffusionTriple.semigroup s.toNNReal (C.toDiffusionTriple.generator
          ⟨C.toDiffusionTriple.cls ψ, C.toDiffusionTriple.cls_mem_generator_domain ψ⟩) := hG
    rw [this, hGa, orb, cls_Lt]
  have h1 : C.toDiffusionTriple.generator ⟨C.toDiffusionTriple.cls ⟨C.Pt s.toNNReal ψ, hp0⟩,
      C.toDiffusionTriple.cls_mem_generator_domain ⟨C.Pt s.toNNReal ψ, hp0⟩⟩ =
      C.toDiffusionTriple.Lcls ⟨C.Pt s.toNNReal ψ, hp0⟩ := C.toDiffusionTriple.generator_cls _ _
  have h2 : (⟨C.toDiffusionTriple.cls ⟨C.Pt s.toNNReal ψ, hp0⟩,
      C.toDiffusionTriple.cls_mem_generator_domain ⟨C.Pt s.toNNReal ψ, hp0⟩⟩ :
        C.toDiffusionTriple.generator.domain) = ⟨C.orb ψ s, hdom⟩ := Subtype.ext hcls
  rw [h2, hG'] at h1
  rw [h1]
  exact (DiffusionTriple.coeFn_Lcls C.toDiffusionTriple ⟨C.Pt s.toNNReal ψ, hp0⟩).symm

end CompactTriple

end MarkovTriple.BGL
