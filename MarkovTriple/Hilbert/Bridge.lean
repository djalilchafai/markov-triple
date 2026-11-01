import Mathlib
import MarkovTriple.Frozen.FullMarkovTriple
import MarkovTriple.Hilbert.TripleForm
import MarkovTriple.Hilbert.BeurlingDeny

/-!
# Bridge: Friedrichs semigroup of a Markov triple satisfies the frozen `IsSemigroupOf`

For a Markov triple `T` (`Frozen/MarkovTriple.lean`), `T.formData` (see `TripleForm.lean`) is the
form `ℰ(f) = ∫ Γ(f,f)` on `𝒜₀ ⊆ L²(μ)`; `tripleSemigroup T := T.formData.semigroup` is the
`P_t = e^{tL}` built from its Friedrichs extension.

**Theorem** `isSemigroupOf_tripleSemigroup`: if the closed form is *Markovian* (first
Beurling–Deny criterion, `IsMarkovianForm T`: `u ∈ Q ⇒ |u| ∈ Q`, `ℰ(|u|) ≤ ℰ(u)`), then
`IsSemigroupOf T (tripleSemigroup T)`.

The hypothesis `IsMarkovianForm` is the *only* thing not derived from the fields of `MarkovTriple`:
positivity preservation of `P_t` is not a consequence of the Markov-triple axioms alone, because
the diffusion property only applies to `ψ(f) ∈ 𝒜₀` (no stability of `𝒜₀` under smooth `ψ`), so
`|f|` or `ψ_ε(f)` is not known to be in the form domain.  Everything else in `IsSemigroupOf`
(`P 0 = id`, semigroup law, strong continuity, self-adjointness, `P_t 1 = 1`, generator extends
`L|𝒜₀`) is proved with no extra hypothesis.  Essential self-adjointness (`FullMarkovTriple.esa`)
is *not* needed for the existence of a witness; it identifies the generator with the closure of
`L|𝒜₀` (`FullMarkovTriple.generator_graph_eq_closure`) -- see `Closure.lean`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E] (T : _root_.MarkovTriple E)

/-- The `L²(μ)` semigroup `P_t = e^{tL}` of the triple, from the Friedrichs extension of
`ℰ` on `𝒜₀`. -/
noncomputable def tripleSemigroup : ℝ≥0 → (Lp ℝ 2 T.μ →L[ℝ] Lp ℝ 2 T.μ) :=
  (formData T).semigroup

/-- The (first Beurling–Deny) Markov property of the closure of `ℰ` on `𝒜₀`:
`u ∈ Q ⇒ |u| ∈ Q` and `ℰ(|u|) ≤ ℰ(u)`. -/
def IsMarkovianForm : Prop :=
  ∀ u : (formData T).Q, ∃ v : (formData T).Q,
    (v : Lp ℝ 2 T.μ) = |(u : Lp ℝ 2 T.μ)| ∧ (formData T).E v v ≤ (formData T).E u u

section Lemmas

lemma L_one_eq_zero : T.L (1 : E → ℝ) = 0 := by
  have h := (T.diffusion 0 (fun _ => (1 : ℝ)) contDiff_const (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) T.A₀.one_mem).2
  show T.L (fun _ => (1 : ℝ)) = fun _ => 0
  rw [h]
  funext x
  simp

lemma one_mem' : (1 : E → ℝ) ∈ T.A₀ := T.A₀.one_mem

lemma norm_abs_eq (u : Lp ℝ 2 T.μ) : ‖|u|‖ = ‖u‖ := by
  have h : inner ℝ |u| |u| = inner ℝ u u := by
    rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_abs u] with x hx
    rw [hx]
    simp
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg |u|, norm_nonneg u, sq_nonneg (‖|u|‖ - ‖u‖), sq_nonneg (‖|u|‖ + ‖u‖)]

lemma inner_nonneg_of_ae {g w : Lp ℝ 2 T.μ} (hg : 0 ≤ᵐ[T.μ] g) (hw : 0 ≤ᵐ[T.μ] w) :
    0 ≤ inner ℝ g w := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_nonneg_of_ae
  filter_upwards [hg, hw] with x h1 h2
  simp only [Pi.zero_apply] at h1 h2
  simpa [mul_comm] using mul_nonneg h1 h2

end Lemmas

/-- **Positivity** of `P_t`, under the Markov property of the form. -/
theorem tripleSemigroup_nonneg (hM : IsMarkovianForm T) (t : ℝ≥0) {u : Lp ℝ 2 T.μ}
    (hu : 0 ≤ᵐ[T.μ] u) : 0 ≤ᵐ[T.μ] tripleSemigroup T t u := by
  have hC : IsClosed {w : Lp ℝ 2 T.μ | 0 ≤ᵐ[T.μ] w} := by
    have : {w : Lp ℝ 2 T.μ | 0 ≤ᵐ[T.μ] w} = Set.Ici 0 := by
      ext w; exact Lp.coeFn_nonneg w
    rw [this]; exact isClosed_Ici
  have := (formData T).semigroup_mapsTo_of_contraction (fun w => |w|)
    {w : Lp ℝ 2 T.μ | 0 ≤ᵐ[T.μ] w} hC
    (fun c hc x hx => by
      have hx' : 0 ≤ᵐ[T.μ] x := hx
      show 0 ≤ᵐ[T.μ] c • x
      filter_upwards [Lp.coeFn_smul c x, hx'] with a h1 h2
      simp only [Pi.zero_apply] at h2 ⊢
      rw [h1]; simpa using mul_nonneg hc h2)
    (fun u => hM u)
    (fun u => (norm_abs_eq T u).le)
    (fun g hg w => by
      have hg' : 0 ≤ᵐ[T.μ] g := hg
      apply inner_nonneg_of_ae T hg'
      filter_upwards [Lp.coeFn_sub |w| w, Lp.coeFn_abs w] with a h1 h2
      rw [h1, Pi.sub_apply, h2]
      simp only [Pi.zero_apply, sub_nonneg]
      exact le_abs_self _)
    (fun w hw => by
      have hw' : (|w| : Lp ℝ 2 T.μ) = w := hw
      show 0 ≤ᵐ[T.μ] w
      filter_upwards [Lp.coeFn_abs w, Filter.EventuallyEq.of_eq (congrArg (fun z : Lp ℝ 2 T.μ => (z : E → ℝ)) hw')] with a h1 h2
      simp only [Pi.zero_apply]
      rw [← h2, h1]
      exact abs_nonneg _) t hu
  exact this

/-- The unit class `[1]` is fixed by every `P_t` (no extra hypothesis: `L 1 = 0`). -/
theorem tripleSemigroup_one (t : ℝ≥0) (u : Lp ℝ 2 T.μ) (hu : (u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ)) :
    (tripleSemigroup T t u : E → ℝ) =ᵐ[T.μ] (1 : E → ℝ) := by
  have hu1 : u = toLp0 T ⟨1, T.A₀.one_mem⟩ := by
    refine Lp.ext ?_
    exact hu.trans (coeFn_toLp0 T ⟨1, T.A₀.one_mem⟩).symm
  set S := formData T with hS
  set d : S.D := ⟨toLp0 T ⟨1, T.A₀.one_mem⟩, ⟨_, rfl⟩⟩ with hd
  have hA : S.A d = 0 := by
    show formA T ⟨toLp0 T ⟨1, T.A₀.one_mem⟩, ⟨_, rfl⟩⟩ = 0
    rw [formA_apply, Lt0_apply]
    have : (T.L (1 : E → ℝ)) = 0 := L_one_eq_zero T
    simp only [this]
    simp
  have hR : S.R (u : Lp ℝ 2 T.μ) = (1 + (0 : ℝ))⁻¹ • u := by
    have := S.R_resolvent ⟨(d : Lp ℝ 2 T.μ), d.2⟩
    have e : S.emb ⟨(d : Lp ℝ 2 T.μ), d.2⟩ = u := by rw [hu1]; rfl
    have e2 : S.opA ⟨(d : Lp ℝ 2 T.μ), d.2⟩ = 0 := hA
    rw [e, e2, add_zero] at this
    simpa using this
  have := S.semigroup_eigen (le_refl (0 : ℝ)) hR t
  have e : tripleSemigroup T t u = u := by
    have h2 : S.semigroup t u = u := by simpa using this
    exact h2
  rw [e]; exact hu

/-- **Bridge.**  For a Markov triple whose Friedrichs form is Markovian
(`IsMarkovianForm T`), the Friedrichs semigroup satisfies the frozen `IsSemigroupOf`. -/
theorem isSemigroupOf_tripleSemigroup (hM : IsMarkovianForm T) :
    IsSemigroupOf T (tripleSemigroup T) := by
  set S := formData T with hS
  refine ⟨S.semigroup_zero, S.semigroup_add, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    have := ((S.continuous_semigroup_apply u).tendsto (0 : ℝ≥0))
    rw [show S.semigroup 0 u = u by simp [S.semigroup_zero]] at this
    exact this
  · intro t u v
    have h := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (S.semigroup_isSelfAdjoint t)
    exact h u v
  · intro t u hu
    exact tripleSemigroup_nonneg T hM t hu
  · intro t u hu
    exact tripleSemigroup_one T t u hu
  · intro f hf u v hu hv
    set f' : T.A₀ := ⟨f, hf⟩
    have hu' : u = toLp0 T f' := Lp.ext (hu.trans (coeFn_toLp0 T f').symm)
    have hv' : v = Lt0 T f' := Lp.ext (hv.trans (coeFn_Lt0 T f').symm)
    set d : S.D := ⟨toLp0 T f', ⟨f', rfl⟩⟩ with hd
    obtain ⟨hdom, hG⟩ := S.generator_extends d
    have hAd : S.A d = -Lt0 T f' := formA_apply T f'
    have key := (S.tendsto_generator_iff (d : Lp ℝ 2 T.μ) v).1 ⟨hdom, by
      rw [hG, hAd, hv']; simp⟩
    rw [hu']
    exact key

end MarkovTriple.Hilbert
