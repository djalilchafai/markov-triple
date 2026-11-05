import Mathlib
import MarkovTriple.BGL.SemigroupLemmas
import MarkovTriple.BGL.Semigroup.Characterization
import MarkovTriple.BGL.Semigroup.ESA
import MarkovTriple.BGL.Semigroup.Markov

/-!
# Round 30 (S), part 6: abstract Duhamel uniqueness for the Friedrichs semigroup

Let `T` be a Diffusion Markov Triple and `Q : ℝ → L²(μ)` a continuous curve, strongly differentiable on `(0, ∞)` with derivative `DQ`,
satisfying the Green identity `⟨L̄ v, Q s⟩ = ⟨v, DQ s⟩` for all `v ∈ 𝒟(L̄)` and `s > 0`.  Then `P_t (Q 0) = Q t`.
(BGL Sect. 2.7.1, 3.1: `s ↦ ⟨P_{t-s} Φ, Q s⟩` is constant, `Φ ∈ 𝒜₀`.)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.Stochastic.R30

open MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

theorem duhamel_unique (T : DiffusionTriple E) (Q DQ : ℝ → Lp ℝ 2 T.μ) (hcont : Continuous Q)
    (hder : ∀ s, 0 < s → HasDerivAt Q (DQ s) s)
    (hgreen : ∀ s, 0 < s → ∀ (v : Lp ℝ 2 T.μ) (hv : v ∈ T.generator.domain),
      inner ℝ (T.generator ⟨v, hv⟩) (Q s) = inner ℝ v (DQ s)) (t : ℝ≥0) :
    T.semigroup t (Q 0) = Q t := by
  set S := DiffusionTriple.formData T with hS
  rcases (zero_le : (0 : ℝ≥0) ≤ t).eq_or_lt with h0 | hpos
  · subst h0
    have e : T.semigroup 0 = 1 := S.semigroup_zero
    rw [e]
    simp
  · have ht : (0 : ℝ) < (t : ℝ) := by exact_mod_cast hpos
    rw [← sub_eq_zero]
    refine T.eq_zero_of_orth _ (fun g => ?_)
    rw [inner_sub_left, sub_eq_zero]
    set F : Lp ℝ 2 T.μ := T.cls g with hF
    have hFd : F ∈ T.generator.domain := T.cls_mem_generator_domain g
    set g0 : Lp ℝ 2 T.μ := F - T.generator ⟨F, hFd⟩ with hg0
    have hRg0 : S.R g0 = F := (S.generator_apply_eq_iff hFd _).1 rfl
    set u : ℝ → Lp ℝ 2 T.μ := fun s => S.semigroup ((t : ℝ) - s).toNNReal F with hu
    set gg : ℝ → ℝ := fun s => inner ℝ (u s) (Q s) with hgg
    have hucont : Continuous u :=
      (S.continuous_semigroup_apply F).comp (continuous_real_toNNReal.comp (by fun_prop))
    have hgcont : Continuous gg := hucont.inner hcont
    have hderiv : ∀ s, 0 < s → s < (t : ℝ) → HasDerivAt gg 0 s := by
      intro s hs0 hst
      have hu' : HasDerivAt u (-(S.semigroup ((t : ℝ) - s).toNNReal (T.generator ⟨F, hFd⟩))) s := by
        have h1 := S.hasDerivAt_semigroup (t := (t : ℝ) - s) (by linarith) g0
        rw [hRg0] at h1
        have hσ : HasDerivAt (fun s : ℝ => (t : ℝ) - s) (-1) s := by
          simpa using (hasDerivAt_id s).const_sub (t : ℝ)
        have h2 := h1.scomp s hσ
        refine h2.congr_deriv ?_
        have : g0 - F = -T.generator ⟨F, hFd⟩ := by rw [hg0]; abel
        rw [this, map_neg, neg_neg, neg_smul, one_smul]
      have hg' := (hu'.inner ℝ (hder s hs0))
      refine hg'.congr_deriv ?_
      obtain ⟨hPd, hPG⟩ := S.semigroup_generator_comm hFd ((t : ℝ) - s).toNNReal
      have hG := hgreen s hs0 _ hPd
      have e1 : S.semigroup ((t : ℝ) - s).toNNReal (T.generator ⟨F, hFd⟩) =
          T.generator ⟨S.semigroup ((t : ℝ) - s).toNNReal F, hPd⟩ := hPG.symm
      rw [e1, inner_neg_left, hG]
      show inner ℝ (u s) (DQ s) + -inner ℝ (S.semigroup ((t : ℝ) - s).toNNReal F) (DQ s) = 0
      simp [hu]
    have hconst : ∀ ε, 0 < ε → ε < (t : ℝ) → gg ε = gg t := by
      intro ε hε hεt
      have := constant_of_has_deriv_right_zero (f := gg) (a := ε) (b := (t : ℝ))
        hgcont.continuousOn
        (fun x hx => (hderiv x (lt_of_lt_of_le hε hx.1) hx.2).hasDerivWithinAt) (t : ℝ)
        ⟨hεt.le, le_rfl⟩
      exact this.symm
    have hg0 : gg 0 = gg t := by
      have h1 : Tendsto gg (𝓝[>] (0 : ℝ)) (𝓝 (gg 0)) :=
        hgcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Tendsto gg (𝓝[>] (0 : ℝ)) (𝓝 (gg t)) :=
        tendsto_const_nhds.congr' (by
          filter_upwards [Ioo_mem_nhdsGT ht] with s hs
          exact (hconst s hs.1 hs.2).symm)
      exact tendsto_nhds_unique h1 h2
    have hgt : gg t = inner ℝ F (Q t) := by
      simp only [hgg, hu, sub_self, Real.toNNReal_zero, S.semigroup_zero]
      rfl
    have hg0' : gg 0 = inner ℝ (T.semigroup t (Q 0)) F := by
      simp only [hgg, hu, sub_zero, Real.toNNReal_coe]
      have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (S.semigroup_isSelfAdjoint t)
        F (Q 0)
      exact hs.trans (real_inner_comm _ _).symm
    have := hg0'.symm.trans (hg0.trans hgt)
    rw [this, real_inner_comm]

end MarkovTriple.Stochastic.R30
