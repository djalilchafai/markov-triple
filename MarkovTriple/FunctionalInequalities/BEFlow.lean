import Mathlib
import MarkovTriple.Hilbert.FullBridge
import MarkovTriple.FunctionalInequalities.FormDomain

/-! # Bakry–Émery (Phase 4b): the heat flow of a test function in `L²`

For `φ ∈ 𝒜₀` of a full Markov triple (`P = tripleSemigroup`, `[φ] = toLp0 φ`):

* `hasDerivAt_orbit`: `d/ds P_s[φ] = P_s[Lφ]` in `L²`, `s > 0`;
* `ae_abs_le_semigroup`: `|u| ≤ c` a.e. ⟹ `|P_t u| ≤ c` a.e. (sub-Markov + positivity);
* `integral_semigroup`: `∫ P_t u = ∫ u` (finite `μ`);
* `L_rep_eq`: if `f ∈ 𝒜`, `f, Lf ∈ L²`, `[f] = P_s[φ]`, then `[Lf] = P_s[Lφ]`
  (`resolvent_eq` and the commutation of `P_s` with the resolvent). -/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
open MarkovTriple.Hilbert

namespace MarkovTriple.BE

variable {E : Type*} [MeasurableSpace E] (F : FullMarkovTriple E)

/-- the class of a test function -/
noncomputable def cl {φ : E → ℝ} (hφ : φ ∈ F.A₀) : Lp ℝ 2 F.μ := toLp0 F.toMarkovTriple ⟨φ, hφ⟩

lemma coeFn_cl {φ : E → ℝ} (hφ : φ ∈ F.A₀) : (cl F hφ : E → ℝ) =ᵐ[F.μ] φ :=
  coeFn_toLp0 F.toMarkovTriple ⟨φ, hφ⟩

/-- `R([φ] - [Lφ]) = [φ]` -/
lemma R_cl {φ : E → ℝ} (hφ : φ ∈ F.A₀) :
    (formData F.toMarkovTriple).R (cl F hφ - cl F (F.L_mem φ hφ)) = cl F hφ := by
  set T := F.toMarkovTriple
  have := (formData T).R_resolvent ⟨toLp0 T ⟨φ, hφ⟩, ⟨⟨φ, hφ⟩, rfl⟩⟩
  have e : (formData T).opA ⟨toLp0 T ⟨φ, hφ⟩, ⟨⟨φ, hφ⟩, rfl⟩⟩ = -Lt0 T ⟨φ, hφ⟩ :=
    formA_apply T ⟨φ, hφ⟩
  rw [e] at this
  have e2 : Lt0 T ⟨φ, hφ⟩ = cl F (F.L_mem φ hφ) := rfl
  rw [e2] at this
  rw [sub_eq_add_neg]
  exact this

/-- `d/ds P_s [φ] = P_s [Lφ]` for `s > 0` -/
theorem hasDerivAt_orbit {φ : E → ℝ} (hφ : φ ∈ F.A₀) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r : ℝ => tripleSemigroup F.toMarkovTriple r.toNNReal (cl F hφ))
      (tripleSemigroup F.toMarkovTriple s.toNNReal (cl F (F.L_mem φ hφ))) s := by
  set S := formData F.toMarkovTriple
  have h := S.hasDerivAt_semigroup hs (cl F hφ - cl F (F.L_mem φ hφ))
  rw [R_cl F hφ] at h
  have e : cl F hφ - cl F (F.L_mem φ hφ) - cl F hφ = -cl F (F.L_mem φ hφ) := by abel
  rw [e, map_neg, neg_neg] at h
  exact h

lemma continuous_orbit (u : Lp ℝ 2 F.μ) :
    Continuous fun r : ℝ => tripleSemigroup F.toMarkovTriple r.toNNReal u :=
  ((formData F.toMarkovTriple).continuous_semigroup_apply u).comp continuous_real_toNNReal

section Markov

variable {F}

/-- `|u| ≤ c` a.e. ⟹ `|P_t u| ≤ c` a.e. (`c > 0`). -/
lemma ae_abs_le_semigroup {c : ℝ} (hc : 0 < c) {u : Lp ℝ 2 F.μ}
    (hu : ∀ᵐ x ∂F.μ, |(u : E → ℝ) x| ≤ c) (t : ℝ≥0) :
    ∀ᵐ x ∂F.μ, |(tripleSemigroup F.toMarkovTriple t u : E → ℝ) x| ≤ c := by
  have hP := isSemigroupOf_full F
  obtain ⟨-, -, -, -, -, hsub, -, -⟩ := hP
  have key : ∀ v : Lp ℝ 2 F.μ, (∀ᵐ x ∂F.μ, (v : E → ℝ) x ≤ c) →
      ∀ᵐ x ∂F.μ, (tripleSemigroup F.toMarkovTriple t v : E → ℝ) x ≤ c := by
    intro v hv
    have h1 : ((c⁻¹ • v : Lp ℝ 2 F.μ) : E → ℝ) ≤ᵐ[F.μ] (1 : E → ℝ) := by
      filter_upwards [Lp.coeFn_smul c⁻¹ v, hv] with x h1 h2
      rw [h1]
      simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      rw [inv_mul_le_iff₀ hc]; simpa using h2
    have h2 := hsub t _ h1
    rw [map_smul] at h2
    filter_upwards [h2, Lp.coeFn_smul c⁻¹ (tripleSemigroup F.toMarkovTriple t v)] with x h3 h4
    rw [h4] at h3
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply] at h3
    rw [inv_mul_le_iff₀ hc] at h3; simpa using h3
  have h1 := key u (hu.mono fun x hx => (le_abs_self _).trans hx)
  have h2 := key (-u) (by
    filter_upwards [hu, Lp.coeFn_neg u] with x hx h
    rw [h]; simpa using (neg_le_abs _).trans hx)
  filter_upwards [h1, h2, Lp.coeFn_neg (tripleSemigroup F.toMarkovTriple t u),
    (by rw [map_neg]; exact Lp.coeFn_neg (tripleSemigroup F.toMarkovTriple t u) :
      (tripleSemigroup F.toMarkovTriple t (-u) : E → ℝ) =ᵐ[F.μ]
        -(tripleSemigroup F.toMarkovTriple t u : E → ℝ))] with x a b _ d
  rw [d] at b
  simp only [Pi.neg_apply] at b
  rw [abs_le]; constructor <;> linarith

/-- `0 ≤ u` a.e. ⟹ `0 ≤ P_t u` a.e. -/
lemma ae_nonneg_semigroup {u : Lp ℝ 2 F.μ} (hu : 0 ≤ᵐ[F.μ] u) (t : ℝ≥0) :
    0 ≤ᵐ[F.μ] tripleSemigroup F.toMarkovTriple t u := by
  obtain ⟨-, -, -, -, hpos, -, -, -⟩ := isSemigroupOf_full F
  exact hpos t u hu

variable (F)

lemma inner_oneL2 [IsFiniteMeasure F.μ] (v : Lp ℝ 2 F.μ) :
    inner ℝ v (oneL2 F.μ) = ∫ x, (v : E → ℝ) x ∂F.μ := by
  have h0 : ((oneL2 F.μ : Lp ℝ 2 F.μ) : E → ℝ) =ᵐ[F.μ] fun _ => (1 : ℝ) :=
    MemLp.coeFn_toLp (memLp_const (1 : ℝ))
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [h0] with x hx
  rw [hx]; simp

/-- `∫ P_t u = ∫ u`. -/
lemma integral_semigroup [IsFiniteMeasure F.μ] (t : ℝ≥0) (u : Lp ℝ 2 F.μ) :
    ∫ x, (tripleSemigroup F.toMarkovTriple t u : E → ℝ) x ∂F.μ = ∫ x, (u : E → ℝ) x ∂F.μ := by
  obtain ⟨-, -, -, hsymm, -, -, hone, -⟩ := isSemigroupOf_full F
  have h1 : tripleSemigroup F.toMarkovTriple t (oneL2 F.μ) = oneL2 F.μ := by
    refine Lp.ext ?_
    have h0 : ((oneL2 F.μ : Lp ℝ 2 F.μ) : E → ℝ) =ᵐ[F.μ] fun _ => (1 : ℝ) :=
      MemLp.coeFn_toLp (memLp_const (1 : ℝ))
    exact (hone t (oneL2 F.μ) h0).trans h0.symm
  rw [← inner_oneL2, ← inner_oneL2, hsymm, h1]

/-- **Identification of `L` on a representative of the flow.** -/
theorem L_rep_eq {φ : E → ℝ} (hφ : φ ∈ F.A₀) {s : ℝ≥0} {f : E → ℝ} (hfA : f ∈ F.A)
    (hf : MemLp f 2 F.μ) (hLf : MemLp (F.L f) 2 F.μ)
    (hfs : hf.toLp f = tripleSemigroup F.toMarkovTriple s (cl F hφ)) :
    hLf.toLp (F.L f) = tripleSemigroup F.toMarkovTriple s (cl F (F.L_mem φ hφ)) := by
  have h1 := F.resolvent_eq hfA hf hLf
  have h2 : (formData F.toMarkovTriple).R (tripleSemigroup F.toMarkovTriple s (cl F hφ) -
      tripleSemigroup F.toMarkovTriple s (cl F (F.L_mem φ hφ))) =
      tripleSemigroup F.toMarkovTriple s (cl F hφ) := by
    rw [← map_sub]
    have := (formData F.toMarkovTriple).semigroup_comm_R s (cl F hφ - cl F (F.L_mem φ hφ))
    rw [R_cl F hφ] at this
    exact this.symm
  rw [hfs] at h1
  have h3 : (formData F.toMarkovTriple).R (tripleSemigroup F.toMarkovTriple s
      (cl F (F.L_mem φ hφ)) - hLf.toLp (F.L f)) = 0 := by
    have e : tripleSemigroup F.toMarkovTriple s (cl F (F.L_mem φ hφ)) - hLf.toLp (F.L f) =
        (tripleSemigroup F.toMarkovTriple s (cl F hφ) - hLf.toLp (F.L f)) -
        (tripleSemigroup F.toMarkovTriple s (cl F hφ) -
          tripleSemigroup F.toMarkovTriple s (cl F (F.L_mem φ hφ))) := by abel
    rw [e, map_sub, h1, h2, sub_self]
  have := (formData F.toMarkovTriple).R_injective (h3.trans (map_zero _).symm)
  exact (sub_eq_zero.mp this).symm

end Markov

end MarkovTriple.BE
