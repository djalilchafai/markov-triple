import Mathlib
import MarkovTriple.BGL.Analysis.Hilbert.SpectralGap

/-!
# Existence of the self-adjoint contraction semigroup of a form

**Main theorem** `FormData.exists_semigroup`: for a densely defined symmetric nonnegative operator
`A : D → H` on a real Hilbert space (a `FormData`), there are a strongly continuous
semigroup `P : ℝ≥0 → H →L H` of self-adjoint positive contractions and a closed densely defined
self-adjoint nonpositive operator `G` such that

* `G` is exactly the generator of `P`: `x ∈ dom G ∧ G x = v ↔ t⁻¹(P_t x - x) → v` as `t ↓ 0`;
* `G` extends `-A`: `f ∈ dom G` and `G f = -A f` for every `f ∈ D`.

(`G = -A_F`, `A_F` the Friedrichs extension; `P_t = e^{tG}` through the continuous functional
calculus of the Friedrichs resolvent.)
-/

open Filter Topology Set
open scoped NNReal LinearPMap InnerProductSpace

namespace MarkovTriple.Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A strongly continuous semigroup of self-adjoint positive contractions on `H`. -/
def IsSelfAdjointContractionSemigroup (P : ℝ≥0 → H →L[ℝ] H) : Prop :=
  P 0 = 1 ∧ (∀ s t, P (s + t) = P s * P t) ∧ (∀ u, Continuous fun t => P t u) ∧
  (∀ t, IsSelfAdjoint (P t)) ∧ (∀ t, ‖P t‖ ≤ 1) ∧ (∀ t u, 0 ≤ inner ℝ (P t u) u)

/-- `G` is the generator of the semigroup `P`: `x ∈ dom G ∧ G x = v` iff the right derivative of
`t ↦ P_t x` at `0` exists and equals `v`. -/
def IsGeneratorOf (G : H →ₗ.[ℝ] H) (P : ℝ≥0 → H →L[ℝ] H) : Prop :=
  ∀ x v : H, (∃ h : x ∈ G.domain, G ⟨x, h⟩ = v) ↔
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • (P t x - x)) (𝓝[>] 0) (𝓝 v)

namespace FormData

variable (S : FormData H)

theorem isSelfAdjointContractionSemigroup_semigroup :
    IsSelfAdjointContractionSemigroup S.semigroup :=
  ⟨S.semigroup_zero, S.semigroup_add, S.continuous_semigroup_apply,
    S.semigroup_isSelfAdjoint, S.norm_semigroup_le,
    fun t u => cfcSemigroup_inner_nonneg S.R_unitOp t u⟩

theorem isGeneratorOf_generator : IsGeneratorOf S.generator S.semigroup :=
  fun x v => S.tendsto_generator_iff x v

/-- `G ≤ 0`. -/
theorem generator_nonpos {x : H} (hx : x ∈ S.generator.domain) :
    inner ℝ (S.generator ⟨x, hx⟩) x ≤ 0 := by
  have hlim := (S.tendsto_generator_iff x (S.generator ⟨x, hx⟩)).1 ⟨hx, rfl⟩
  have h2 : Tendsto (fun t : ℝ≥0 => inner ℝ ((t : ℝ)⁻¹ • (S.semigroup t x - x)) x) (𝓝[>] 0)
      (𝓝 (inner ℝ (S.generator ⟨x, hx⟩) x)) := hlim.inner tendsto_const_nhds
  refine le_of_tendsto h2 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  rw [inner_smul_left, inner_sub_left]
  simp only [RCLike.conj_to_real]
  have h3 : inner ℝ (S.semigroup t x) x ≤ inner ℝ x x := by
    calc inner ℝ (S.semigroup t x) x ≤ ‖S.semigroup t x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖x‖ * ‖x‖ := mul_le_mul_of_nonneg_right (norm_cfcSemigroup_apply_le S.R_unitOp t x)
          (norm_nonneg _)
      _ = inner ℝ x x := (real_inner_self_eq_norm_mul_norm x).symm
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 ht'.le) (by linarith)

/-- **Existence of the self-adjoint contraction semigroup whose generator extends `-A`.** -/
theorem exists_semigroup :
    ∃ (P : ℝ≥0 → H →L[ℝ] H) (G : H →ₗ.[ℝ] H),
      IsSelfAdjointContractionSemigroup P ∧ IsSelfAdjoint G ∧ G.IsClosed ∧
      Dense (G.domain : Set H) ∧ IsGeneratorOf G P ∧
      (∀ x (hx : x ∈ G.domain), inner ℝ (G ⟨x, hx⟩) x ≤ 0) ∧
      (∀ f : S.D, ∃ h : (f : H) ∈ G.domain, G ⟨f, h⟩ = -S.A f) :=
  ⟨S.semigroup, S.generator, S.isSelfAdjointContractionSemigroup_semigroup,
    S.generator_selfAdjoint, S.generator_isClosed, S.generator_dense_domain,
    S.isGeneratorOf_generator, fun _ hx => S.generator_nonpos hx, S.generator_extends⟩

end FormData

end MarkovTriple.Hilbert
