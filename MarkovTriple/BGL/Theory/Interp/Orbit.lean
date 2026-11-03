import Mathlib
import MarkovTriple.BGL.Theory.Extension.Gamma2Ident
import MarkovTriple.BGL.Theory.Extension.GammaELin
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Theory.GradientBound
import MarkovTriple.BGL.SemigroupLemmas

/-!
# The heat orbit of a test function in `𝒟(L)` and in the form space `K` (inputs of BGL Lemmas 3.3.20-3.3.21)

For a general `FullTriple` (no compactness): `orb ψ s = P_s[ψ]`, `ψ ∈ 𝒜₀`.  `hasDerivAt_orb` (`L²`), membership in `𝒟(L)` with
`L P_s ψ = P_s L ψ`, and the key estimate `‖v‖_K² ≤ ‖v‖₂² + ‖Lv‖₂‖v‖₂` for `v ∈ 𝒟(L)` which yields
`hasDerivAt_orbK`: `s ↦ P_s ψ` is differentiable in the form norm of `𝒟(ℰ)` (`s > 0`) and continuous for all `s`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- `L ψ` as a test function. -/
def Lt (ψ : T.A₀) : T.A₀ := ⟨T.L ψ.1, T.toDiffusionTriple.L_mem ψ.1 ψ.2⟩

/-- the orbit `s ↦ P_s [ψ]` of a test function (constant `[ψ]` for `s ≤ 0`). -/
noncomputable def orb (ψ : T.A₀) (s : ℝ) : Lp ℝ 2 T.μ :=
  T.toDiffusionTriple.semigroup s.toNNReal (T.toDiffusionTriple.cls ψ)

lemma cls_Lt (ψ : T.A₀) : T.toDiffusionTriple.cls (T.Lt ψ) = T.toDiffusionTriple.Lcls ψ := by
  refine Lp.ext ?_
  exact (DiffusionTriple.coeFn_cls T.toDiffusionTriple (T.Lt ψ)).trans
    (DiffusionTriple.coeFn_Lcls T.toDiffusionTriple ψ).symm

lemma continuous_orb (ψ : T.A₀) : Continuous (T.orb ψ) :=
  (T.toDiffusionTriple.continuous_semigroup_apply _).comp continuous_real_toNNReal

lemma orb_zero (ψ : T.A₀) : T.orb ψ 0 = T.toDiffusionTriple.cls ψ := by
  simp [orb, DiffusionTriple.semigroup_zero]

/-- `d/ds P_s [ψ] = P_s [Lψ]` for `s > 0`. -/
theorem hasDerivAt_orb (ψ : T.A₀) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (T.orb ψ) (T.orb (T.Lt ψ) s) s := by
  have h := (DiffusionTriple.formData T.toDiffusionTriple).hasDerivAt_semigroup hs
    (T.toDiffusionTriple.cls ψ - T.toDiffusionTriple.Lcls ψ)
  rw [DiffusionTriple.R_cls_sub T.toDiffusionTriple ψ] at h
  have e : T.toDiffusionTriple.cls ψ - T.toDiffusionTriple.Lcls ψ - T.toDiffusionTriple.cls ψ =
      -T.toDiffusionTriple.Lcls ψ := by abel
  rw [e, map_neg, neg_neg] at h
  unfold orb
  rw [cls_Lt]
  exact h

/-- `P_s[ψ] ∈ 𝒟(L)` and `L P_s[ψ] = P_s[Lψ]`. -/
theorem orb_mem_dom (ψ : T.A₀) (s : ℝ) :
    ∃ hdom : T.orb ψ s ∈ T.toDiffusionTriple.generator.domain,
      T.toDiffusionTriple.generator ⟨T.orb ψ s, hdom⟩ = T.orb (T.Lt ψ) s := by
  obtain ⟨hdom, hG⟩ := (DiffusionTriple.formData T.toDiffusionTriple).semigroup_generator_comm
    (T.toDiffusionTriple.cls_mem_generator_domain ψ) s.toNNReal
  refine ⟨hdom, ?_⟩
  have hGa : T.toDiffusionTriple.generator ⟨T.toDiffusionTriple.cls ψ,
      T.toDiffusionTriple.cls_mem_generator_domain ψ⟩ = T.toDiffusionTriple.Lcls ψ :=
    T.toDiffusionTriple.generator_cls ψ _
  have : T.toDiffusionTriple.generator ⟨T.orb ψ s, hdom⟩ =
      T.toDiffusionTriple.semigroup s.toNNReal (T.toDiffusionTriple.generator
        ⟨T.toDiffusionTriple.cls ψ, T.toDiffusionTriple.cls_mem_generator_domain ψ⟩) := hG
  rw [this, hGa, orb, cls_Lt]

lemma orb_mem_Q (ψ : T.A₀) (s : ℝ) : T.orb ψ s ∈ T.formDomain :=
  ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form
    (T.orb_mem_dom ψ s).1).1

/-- the orbit as an element of `𝒟(ℰ)`. -/
noncomputable def orbQ (ψ : T.A₀) (s : ℝ) : T.formDomain := ⟨T.orb ψ s, T.orb_mem_Q ψ s⟩

/-- the Hilbert norm of `𝒟(ℰ)`. -/
noncomputable def kn (u : T.formDomain) : ℝ :=
  ‖(DiffusionTriple.formData T.toDiffusionTriple).qEquiv.symm u‖

lemma kn_sq (u : T.formDomain) :
    T.kn u ^ 2 = T.toDiffusionTriple.closedForm u u + ‖(u : Lp ℝ 2 T.μ)‖ ^ 2 := by
  unfold kn
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  show (DiffusionTriple.formData T.toDiffusionTriple).E1 u u =
    (DiffusionTriple.formData T.toDiffusionTriple).E u u + _
  unfold Hilbert.FormData.E
  ring

/-- `‖v‖_K² ≤ ‖v‖₂² + ‖Lv‖₂ ‖v‖₂` for `v ∈ 𝒟(L)`. -/
lemma kn_sq_le {v : Lp ℝ 2 T.μ} (hv : v ∈ T.toDiffusionTriple.generator.domain) :
    T.kn ⟨v, ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form hv).1⟩ ^ 2 ≤
      ‖v‖ ^ 2 + ‖T.toDiffusionTriple.generator ⟨v, hv⟩‖ * ‖v‖ := by
  obtain ⟨hQ, hform⟩ := (DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form hv
  rw [kn_sq]
  have := hform ⟨v, hQ⟩
  have h2 : T.toDiffusionTriple.closedForm ⟨v, hQ⟩ ⟨v, hQ⟩ =
      -inner ℝ (T.toDiffusionTriple.generator ⟨v, hv⟩) v := this
  rw [h2]
  have := real_inner_le_norm (-(T.toDiffusionTriple.generator ⟨v, hv⟩)) v
  rw [inner_neg_left, norm_neg] at this
  simp only
  nlinarith

end FullTriple

end MarkovTriple.BGL
