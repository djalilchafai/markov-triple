import Mathlib
import MarkovTriple.BGL.Frozen.Poincare
import MarkovTriple.BGL.Frozen.LSI
import MarkovTriple.BGL.Frozen.FormDomain
import MarkovTriple.BGL.Semigroup.Mass
import MarkovTriple.BGL.Semigroup.Characterization

/-!
# `𝒜₀` is dense in `𝒟(ℰ)`; the Poincaré inequality extends from `𝒜₀` to `𝒟(ℰ)` (audit M2)

* `DiffusionTriple.formDomain_approx` (D7: "`𝒟(ℰ)` is the completion of `𝒜₀` for
  `(‖f‖² + ℰ(f))^{1/2}`"): every `u ∈ 𝒟(ℰ)` is the limit of classes `a_n ∈ 𝒜₀` in `L²`, with
  `ℰ(u − a_n) → 0` and `ℰ(a_n) → ℰ(u)`.  `formDomain = range ι` for the canonical map `ι` of the
  completion `K` of `𝒜₀`, and `𝒜₀` is dense in `K` by construction.
* `DiffusionTriple.PI.extend`: `P(C)` on `𝒜₀` implies `Var(u) ≤ C ℰ(u)` for all `u ∈ 𝒟(ℰ)`.
* `DiffusionTriple.integrable_sq_mul_log_sq`: for `f ∈ 𝒜₀` (bounded), `f² log f²` is integrable
  (finite `μ`), so `Ent(f²)` in `LS` is a genuine entropy.
* `DiffusionTriple.ℰ_eq`: the triple-bound `ℰ` on `𝒜₀` is `∫ Γ`, and `closedForm` extends it.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E] (T : DiffusionTriple E)

namespace DiffusionTriple

lemma ℰ_eq (f g : T.A₀) : T.ℰ f g = ∫ x, T.Γ f.1 g.1 x ∂T.μ := rfl

lemma ℰ_eq_qf (f g : T.A₀) : T.ℰ f g = qf T f g := rfl

/-- The class of a test function as an element of the Dirichlet domain. -/
noncomputable def clsQ (a : T.A₀) : T.formDomain :=
  ⟨T.cls a, (formData T).emb_mem_Q ⟨clsₗ T a, ⟨a, rfl⟩⟩⟩

lemma coe_clsQ (a : T.A₀) : ((T.clsQ a : T.formDomain) : Lp ℝ 2 T.μ) = T.cls a := rfl

lemma closedForm_clsQ (a b : T.A₀) : T.closedForm (T.clsQ a) (T.clsQ b) = T.ℰ a b :=
  T.closedForm_cls a b

/-- **Density of `𝒜₀` in `𝒟(ℰ)`.**  Every `u ∈ 𝒟(ℰ)` is the limit in `L²` of classes `a_n ∈ 𝒜₀`,
with `ℰ(u − a_n) → 0` (convergence in the form norm) and `ℰ(a_n) → ℰ(u)`. -/
theorem formDomain_approx (u : T.formDomain) :
    ∃ a : ℕ → T.A₀,
      Tendsto (fun n => T.cls (a n)) atTop (𝓝 (u : Lp ℝ 2 T.μ)) ∧
      Tendsto (fun n => T.closedForm (u - T.clsQ (a n)) (u - T.clsQ (a n))) atTop (𝓝 0) ∧
      Tendsto (fun n => T.ℰ (a n) (a n)) atTop (𝓝 (T.closedForm u u)) := by
  set S := formData T with hS
  obtain ⟨x, hx⟩ := S.qEquiv.surjective u
  have hxc : x ∈ closure (Set.range ((↑) : S.Dom → S.K)) :=
    UniformSpace.Completion.denseRange_coe x
  obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.1 hxc
  have hs' : ∀ n, ∃ a : T.A₀, ((show S.Dom from ⟨clsₗ T a, ⟨a, rfl⟩⟩ : S.Dom) : S.K) = s n := by
    intro n
    obtain ⟨d, hd⟩ := hs n
    obtain ⟨_, a, rfl⟩ := d
    exact ⟨a, hd⟩
  choose a ha using hs'
  set d : ℕ → S.K := fun n => ((show S.Dom from ⟨clsₗ T (a n), ⟨a n, rfl⟩⟩ : S.Dom) : S.K) with hd
  have hdx : Tendsto d atTop (𝓝 x) := by
    have : d = s := funext ha
    rw [this]; exact hslim
  have hιd : ∀ n, S.ι (d n) = T.cls (a n) := fun n => S.ι_coe _
  have hqd : ∀ n, S.qEquiv (d n) = (T.clsQ (a n)) := fun n =>
    Subtype.ext (by rw [Hilbert.FormData.qEquiv_apply, hιd]; rfl)
  have hux : S.ι x = (u : Lp ℝ 2 T.μ) := by
    rw [← hx]; rfl
  refine ⟨a, ?_, ?_, ?_⟩
  · have := (S.ι.continuous.tendsto x).comp hdx
    rw [hux] at this
    exact this.congr (fun n => hιd n)
  · have hsub : ∀ n, u - T.clsQ (a n) = S.qEquiv (x - d n) := by
      intro n
      rw [map_sub, hx, hqd]; rfl
    have hE : ∀ n, T.closedForm (u - T.clsQ (a n)) (u - T.clsQ (a n)) =
        ‖x - d n‖ ^ 2 - ‖S.ι (x - d n)‖ ^ 2 := by
      intro n
      rw [hsub n]
      show S.E _ _ = _
      rw [Hilbert.FormData.E_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have hn : Tendsto (fun n => ‖x - d n‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero.1 hdx)
      simpa [norm_sub_rev] using this
    refine squeeze_zero (fun n => ?_) (fun n => ?_) (by simpa using hn.pow 2)
    · rw [hsub n]; exact S.E_nonneg _
    · rw [hE n]; nlinarith [sq_nonneg ‖S.ι (x - d n)‖]
  · have hE : ∀ n, T.ℰ (a n) (a n) = ‖d n‖ ^ 2 - ‖T.cls (a n)‖ ^ 2 := by
      intro n
      rw [← closedForm_clsQ, ← hqd n]
      show S.E _ _ = _
      rw [Hilbert.FormData.E_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hιd]
    have hE' : T.closedForm u u = ‖x‖ ^ 2 - ‖S.ι x‖ ^ 2 := by
      rw [← hx]
      show S.E _ _ = _
      rw [Hilbert.FormData.E_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    rw [hE']
    have h1 : Tendsto (fun n => ‖d n‖ ^ 2) atTop (𝓝 (‖x‖ ^ 2)) := (hdx.norm).pow 2
    have h2 : Tendsto (fun n => ‖S.ι (d n)‖ ^ 2) atTop (𝓝 (‖S.ι x‖ ^ 2)) :=
      (((S.ι.continuous.tendsto x).comp hdx).norm).pow 2
    refine (h1.sub h2).congr (fun n => ?_)
    rw [hE n, hιd]

/-- Variance of an `L²` class on a probability space: `‖v‖² − ⟪v, 1⟫²`. -/
theorem variance_Lp [IsProbabilityMeasure T.μ] (v : Lp ℝ 2 T.μ) :
    ProbabilityTheory.variance (v : E → ℝ) T.μ = ‖v‖ ^ 2 - (inner ℝ v T.one2) ^ 2 := by
  rw [ProbabilityTheory.variance_eq_sub (Lp.memLp v)]
  have h1 : ∫ x, ((v : E → ℝ) ^ 2) x ∂T.μ = ‖v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])
  have h2 : ∫ x, (v : E → ℝ) x ∂T.μ = inner ℝ v T.one2 := by
    rw [L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [T.coeFn_one2] with x hx
    rw [hx]; simp
  rw [h1, h2]

/-- **The Poincaré inequality extends from `𝒜₀` to `𝒟(ℰ)`** (book form of Def. 4.2.1). -/
theorem PI.extend {C : ℝ} (h : T.PI C) (u : T.formDomain) :
    ProbabilityTheory.variance ((u : Lp ℝ 2 T.μ) : E → ℝ) T.μ ≤ C * T.closedForm u u := by
  unfold DiffusionTriple.PI PoincareIneq at h
  obtain ⟨hprob, hC, hineq⟩ := h
  have := hprob
  obtain ⟨a, h1, -, h3⟩ := T.formDomain_approx u
  have hV : ∀ n, ProbabilityTheory.variance ((T.cls (a n) : Lp ℝ 2 T.μ) : E → ℝ) T.μ ≤
      C * T.ℰ (a n) (a n) := by
    intro n
    rw [ProbabilityTheory.variance_congr (coeFn_cls T (a n))]
    exact hineq (a n).1 (a n).2
  have hlim1 : Tendsto (fun n => ProbabilityTheory.variance ((T.cls (a n) : Lp ℝ 2 T.μ) : E → ℝ) T.μ)
      atTop (𝓝 (ProbabilityTheory.variance ((u : Lp ℝ 2 T.μ) : E → ℝ) T.μ)) := by
    simp only [variance_Lp]
    exact (h1.norm.pow 2).sub ((h1.inner tendsto_const_nhds).pow 2)
  exact le_of_tendsto_of_tendsto hlim1 (h3.const_mul C) (Filter.Eventually.of_forall hV)

/-- For `f ∈ 𝒜₀` (bounded, measurable) and a finite measure, `f² log f²` is integrable: the entropy
`Ent(f²)` appearing in `LS(C,D)` is a genuine entropy, not a Bochner junk value. -/
theorem integrable_sq_mul_log_sq [IsFiniteMeasure T.μ] {f : E → ℝ} (hf : f ∈ T.A₀) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) T.μ := by
  obtain ⟨M, hM⟩ := T.bounded f hf
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := M ^ 2)).exists_bound_of_continuousOn
    (Real.continuous_mul_log.continuousOn (s := Set.Icc 0 (M ^ 2)))
  have hmeas : Measurable fun x => f x ^ 2 * Real.log (f x ^ 2) :=
    Real.continuous_mul_log.measurable.comp ((T.measurable f hf).pow_const 2)
  refine Integrable.of_bound hmeas.aestronglyMeasurable K (Filter.Eventually.of_forall fun x => ?_)
  refine hK _ ⟨sq_nonneg _, ?_⟩
  have := hM x
  have h2 : f x ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
  exact h2

end DiffusionTriple

end MarkovTriple.BGL
