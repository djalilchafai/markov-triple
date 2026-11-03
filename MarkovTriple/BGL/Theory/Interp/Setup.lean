import Mathlib
import MarkovTriple.BGL.Theory.Interp.Curve
import MarkovTriple.BGL.Theory.Interp.Pairing
import MarkovTriple.BGL.Theory.Interp.PsiBounds
import MarkovTriple.BGL.Theory.Interp.Lemma3320
import MarkovTriple.BGL.Theory.Interp.IbpBdd
import MarkovTriple.BGL.Theory.Strong.Main

/-!
# Representatives of the orbits and the curves of the interpolation (BGL proof of Thm 3.3.18, p. 164)

* `ae_abs_semigroup_le`: sub-Markov bound `|u| ≤ c ⇒ |P_t u| ≤ c` (a general `DiffusionTriple`);
* `ucurve f t r = Γ(P_{t-r} f)` as an `L¹` class (`GB (cK f (t-r)) (cK f (t-r))`) and its identification with the
  `𝒜`-representative `ΓA (Pt (t-r) f)` (Props 3.3.5 (ii)); `L_Pt_ae`: `L(P_s ψ) = P_s Lψ`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

lemma ae_abs_semigroup_le (D : DiffusionTriple E) {c : ℝ} (hc : 0 < c) {u : Lp ℝ 2 D.μ}
    (hu : ∀ᵐ x ∂D.μ, |(u : E → ℝ) x| ≤ c) (t : ℝ≥0) :
    ∀ᵐ x ∂D.μ, |(D.semigroup t u : E → ℝ) x| ≤ c := by
  have key : ∀ v : Lp ℝ 2 D.μ, (∀ᵐ x ∂D.μ, (v : E → ℝ) x ≤ c) →
      ∀ᵐ x ∂D.μ, (D.semigroup t v : E → ℝ) x ≤ c := by
    intro v hv
    have h1 : ((c⁻¹ • v : Lp ℝ 2 D.μ) : E → ℝ) ≤ᵐ[D.μ] (1 : E → ℝ) := by
      filter_upwards [Lp.coeFn_smul c⁻¹ v, hv] with x h1 h2
      rw [h1]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      rw [inv_mul_le_iff₀ hc]; simpa using h2
    have h2 := D.semigroup_le_one t _ h1
    rw [map_smul] at h2
    filter_upwards [h2, Lp.coeFn_smul c⁻¹ (D.semigroup t v)] with x h3 h4
    rw [h4] at h3
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h3
    rw [inv_mul_le_iff₀ hc] at h3; simpa using h3
  have h1 := key u (hu.mono fun x hx => (le_abs_self _).trans hx)
  have h2 := key (-u) (by
    filter_upwards [hu, Lp.coeFn_neg u] with x hx h
    rw [h]; simpa using (neg_le_abs _).trans hx)
  filter_upwards [h1, h2, Lp.coeFn_neg (D.semigroup t u),
    (by rw [map_neg]; exact Lp.coeFn_neg (D.semigroup t u) :
      (D.semigroup t (-u) : E → ℝ) =ᵐ[D.μ] -(D.semigroup t u : E → ℝ))] with x a b _ d
  rw [d] at b
  simp only [Pi.neg_apply] at b
  rw [abs_le]; constructor <;> linarith

namespace FullTriple

variable {T : FullTriple E}

/-- the curve `r ↦ Γ(P_{t-r} f)` in `L¹`. -/
noncomputable def ucurve (T : FullTriple E) (f : T.A₀) (t : ℝ≥0) (r : ℝ) : Lp ℝ 1 T.μ :=
  GB T (T.cK f ((t : ℝ) - r)) (T.cK f ((t : ℝ) - r))

lemma ucurve_eq_gammaE (f : T.A₀) (t : ℝ≥0) (r : ℝ) :
    T.ucurve f t r = gammaE T (T.orbQ f ((t : ℝ) - r)) (T.orbQ f ((t : ℝ) - r)) :=
  GB_apply T _ _

lemma ucurve_nonneg (f : T.A₀) (t : ℝ≥0) (r : ℝ) : 0 ≤ᵐ[T.μ] (T.ucurve f t r : E → ℝ) := by
  rw [ucurve_eq_gammaE]; exact gammaE_self_nonneg _

lemma continuous_ucurve (f : T.A₀) (t : ℝ≥0) : Continuous (T.ucurve f t) := by
  have h : Continuous fun r : ℝ => (t : ℝ) - r := continuous_const.sub continuous_id
  exact (T.continuous_uK f).comp h

lemma Pt_toLp_eq_orb (ψ : T.A₀) (σ : ℝ) :
    (T.Pt_memLp σ.toNNReal ψ).toLp (T.Pt σ.toNNReal ψ) = T.orb ψ σ := by
  refine Lp.ext ?_
  filter_upwards [(T.Pt_memLp σ.toNNReal ψ).coeFn_toLp, T.Pt_ae σ.toNNReal ψ] with x h1 h2
  rw [h1]; exact h2.symm

lemma Pt_mem_dom (ψ : T.A₀) (σ : ℝ) :
    (T.Pt_memLp σ.toNNReal ψ).toLp (T.Pt σ.toNNReal ψ) ∈ T.toDiffusionTriple.generator.domain := by
  rw [Pt_toLp_eq_orb]; exact (T.orb_mem_dom ψ σ).1

lemma Pt_mem_Q (ψ : T.A₀) (σ : ℝ) :
    (T.Pt_memLp σ.toNNReal ψ).toLp (T.Pt σ.toNNReal ψ) ∈ T.formDomain := by
  rw [Pt_toLp_eq_orb]; exact T.orb_mem_Q ψ σ

/-- `L (P_σ ψ) = P_σ (Lψ)` (a.e., for the `𝒜`-representative). -/
lemma L_Pt_ae (ψ : T.A₀) (σ : ℝ) :
    T.L (T.Pt σ.toNNReal ψ) =ᵐ[T.μ] (T.orb (T.Lt ψ) σ : E → ℝ) := by
  have h := generator_ae_L (T.Pt_mem_A σ.toNNReal ψ) (T.Pt_memLp σ.toNNReal ψ) (Pt_mem_dom ψ σ)
  have e : (⟨(T.Pt_memLp σ.toNNReal ψ).toLp (T.Pt σ.toNNReal ψ), Pt_mem_dom ψ σ⟩ :
      T.toDiffusionTriple.generator.domain) = T.orbD ψ σ := Subtype.ext (Pt_toLp_eq_orb ψ σ)
  rw [e, generator_orbD] at h
  exact h.symm

lemma memLp_L_Pt (ψ : T.A₀) (σ : ℝ) : MemLp (T.L (T.Pt σ.toNNReal ψ)) 2 T.μ :=
  (Lp.memLp (T.orb (T.Lt ψ) σ)).ae_eq (T.L_Pt_ae ψ σ).symm

lemma toLp_L_Pt (ψ : T.A₀) (σ : ℝ) :
    (T.memLp_L_Pt ψ σ).toLp (T.L (T.Pt σ.toNNReal ψ)) = T.orb (T.Lt ψ) σ := by
  refine Lp.ext ?_
  filter_upwards [(T.memLp_L_Pt ψ σ).coeFn_toLp, T.L_Pt_ae ψ σ] with x h1 h2
  rw [h1]; exact h2

lemma ucurve_ae (f : T.A₀) (t : ℝ≥0) (r : ℝ) :
    (T.ucurve f t r : E → ℝ) =ᵐ[T.μ]
      G T (T.Pt ((t : ℝ) - r).toNNReal f) (T.Pt ((t : ℝ) - r).toNNReal f) := by
  rw [ucurve_eq_gammaE]
  have e : (⟨(T.Pt_memLp ((t : ℝ) - r).toNNReal f).toLp (T.Pt ((t : ℝ) - r).toNNReal f),
      Pt_mem_Q f ((t : ℝ) - r)⟩ : T.formDomain) = T.orbQ f ((t : ℝ) - r) :=
    Subtype.ext (Pt_toLp_eq_orb f _)
  rw [← e]
  exact gammaE_self_eq_ΓA (T.Pt_mem_A _ f) (T.Pt_memLp _ f) (Pt_mem_Q f _)

end FullTriple

end MarkovTriple.BGL
