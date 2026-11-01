import Mathlib
import MarkovTriple.Frozen.FullMarkovTriple
import MarkovTriple.Hilbert.Closure
import MarkovTriple.Hilbert.Bridge
import MarkovTriple.Hilbert.MarkovCriterion

/-!
# Full Markov triples: closure domain (ERRATA F6), conservativeness, and the unconditional bridge

For `F : FullMarkovTriple E` (with `S = formData F.toMarkovTriple`, `R = (1 + A_F)⁻¹`):

* `FullMarkovTriple.resolvent_eq`: if `f ∈ 𝒜` with `f, Lf ∈ L²`, then `R([f] − [Lf]) = [f]`, i.e.
  `f ∈ D(L̄)` (domain of the generator, equal to the closure of `L|𝒜₀` by `esa`) and `L̄ f = Lf`.
  Proof: `⟨R(u−v) − u, (1−L)g⟩ = 0` for all `g ∈ 𝒜₀` by the two integration-by-parts fields
  `ibp_A`, `ibp_A_symm`, so `R(u−v) = u` by the density of `(1−L)𝒜₀` (`esa`).
* `FullMarkovTriple.tripleSemigroup_one`: `P_t 1 = 1` when `μ` is finite, although `1 ∉ 𝒜₀`
  (`1 ∈ 𝒜`, `L 1 = 0` from the chain rule on `𝒜`).
* `isSemigroupOf_full`: **for every full Markov triple the Friedrichs semigroup is a witness of
  `IsSemigroupOf`**, with no extra hypothesis (positivity: `isMarkovianForm`).
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.Hilbert

variable {E : Type*} [MeasurableSpace E]

lemma inner_toLp_toLp {μ : Measure E} {a b : E → ℝ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x ∂μ := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- **Closure domain** (ERRATA F6). -/
theorem _root_.FullMarkovTriple.resolvent_eq (F : FullMarkovTriple E) {f : E → ℝ} (hfA : f ∈ F.A)
    (hf : MemLp f 2 F.μ) (hLf : MemLp (F.L f) 2 F.μ) :
    (formData F.toMarkovTriple).R (hf.toLp f - hLf.toLp (F.L f)) = hf.toLp f := by
  set T := F.toMarkovTriple with hT
  set S := formData T with hS
  set u : Lp ℝ 2 T.μ := hf.toLp f with hu
  set v : Lp ℝ 2 T.μ := hLf.toLp (F.L f) with hv
  set w : Lp ℝ 2 T.μ := S.R (u - v) - u with hw
  have hsub : ∀ y ∈ {y : Lp ℝ 2 T.μ | ∃ g ∈ T.A₀, (y : E → ℝ) =ᵐ[T.μ] g - T.L g},
      inner ℝ w y = 0 := by
    rintro y ⟨g, hg, hy⟩
    set g' : T.A₀ := ⟨g, hg⟩ with hg'
    have hyeq : y = toLp0 T g' - Lt0 T g' := by
      refine Lp.ext ?_
      filter_upwards [hy, Lp.coeFn_sub (toLp0 T g') (Lt0 T g'), coeFn_toLp0 T g',
        coeFn_Lt0 T g'] with x h1 h2 h3 h4
      rw [h1, h2]; simp only [Pi.sub_apply]; rw [h3, h4]
    have hRy : S.R y = toLp0 T g' := by
      have := S.R_resolvent ⟨toLp0 T g', ⟨g', rfl⟩⟩
      have e : S.opA ⟨toLp0 T g', ⟨g', rfl⟩⟩ = -Lt0 T g' := formA_apply T g'
      rw [e] at this
      rw [hyeq, sub_eq_add_neg]
      exact this
    have hg2 : MemLp g 2 T.μ := memLp2 T hg
    have hLg2 : MemLp (T.L g) 2 T.μ := memLp2 T (T.L_mem g hg)
    have e1 : inner ℝ (S.R (u - v)) y = inner ℝ (u - v) (toLp0 T g') := by
      have h := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp S.R_isSelfAdjoint (u - v) y
      have h' : inner ℝ (S.R (u - v)) y = inner ℝ (u - v) (S.R y) := h
      rw [h', hRy]
    have hg'1 : toLp0 T g' = hg2.toLp g := rfl
    have hg'2 : Lt0 T g' = hLg2.toLp (T.L g) := rfl
    have i1 : inner ℝ (u - v) (toLp0 T g') = (∫ x, f x * g x ∂T.μ) - ∫ x, T.L f x * g x ∂T.μ := by
      rw [inner_sub_left, hg'1, hu, hv, inner_toLp_toLp hf hg2, inner_toLp_toLp hLf hg2]
    have i2 : inner ℝ u y = (∫ x, f x * g x ∂T.μ) - ∫ x, f x * T.L g x ∂T.μ := by
      rw [hyeq, inner_sub_right, hg'1, hg'2, hu, inner_toLp_toLp hf hg2,
        inner_toLp_toLp hf hLg2]
    have k1 := (F.ibp_A f hfA hf hLf g hg).2
    have k2 := F.ibp_A_symm f hfA hf hLf g hg
    have k3 : ∫ x, T.L f x * g x ∂T.μ = ∫ x, f x * T.L g x ∂T.μ := by
      have : (fun x => T.L f x * g x) = fun x => g x * T.L f x := by funext x; ring
      rw [this, k1, k2]
    rw [hw, inner_sub_left, e1, i1, i2, k3]; ring
  have hc : IsClosed {y : Lp ℝ 2 T.μ | inner ℝ w y = 0} :=
    isClosed_eq (continuous_const.inner continuous_id) continuous_const
  have hwmem : w ∈ closure {y : Lp ℝ 2 T.μ | ∃ g ∈ T.A₀, (y : E → ℝ) =ᵐ[T.μ] g - T.L g} := by
    rw [F.esa.closure_eq]; trivial
  have hww : inner ℝ w w = 0 := (closure_minimal hsub hc) hwmem
  have : w = 0 := inner_self_eq_zero.mp hww
  exact sub_eq_zero.mp this

lemma _root_.FullMarkovTriple.L_one (F : FullMarkovTriple E) : F.L (1 : E → ℝ) = 0 := by
  have h := (F.diffusion_A 0 (fun _ => (1 : ℝ)) contDiff_const (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i)).2
  show F.L (fun _ => (1 : ℝ)) = fun _ => 0
  rw [h]
  funext x
  simp

/-- **Conservativeness** `P_t 1 = 1` for a full Markov triple (when `1 ∈ L²`, i.e. `μ` finite). -/
theorem _root_.FullMarkovTriple.tripleSemigroup_one (F : FullMarkovTriple E) (t : ℝ≥0)
    (u₀ : Lp ℝ 2 F.μ) (hu : (u₀ : E → ℝ) =ᵐ[F.μ] (1 : E → ℝ)) :
    (tripleSemigroup F.toMarkovTriple t u₀ : E → ℝ) =ᵐ[F.μ] (1 : E → ℝ) := by
  set S := formData F.toMarkovTriple with hS
  have h1 : MemLp (1 : E → ℝ) 2 F.μ := (Lp.memLp u₀).ae_eq hu
  have hL : MemLp (F.L (1 : E → ℝ)) 2 F.μ := by rw [F.L_one]; exact MemLp.zero
  have hone : (1 : E → ℝ) ∈ F.A := F.A.one_mem
  have key := F.resolvent_eq hone h1 hL
  have hv : hL.toLp (F.L (1 : E → ℝ)) = 0 := by
    refine Lp.ext ?_
    filter_upwards [hL.coeFn_toLp, Lp.coeFn_zero ℝ 2 F.μ] with x e1 e2
    rw [e1, e2]; simp [F.L_one]
  have hu1 : u₀ = h1.toLp 1 := Lp.ext (hu.trans h1.coeFn_toLp.symm)
  rw [hv, sub_zero] at key
  have hR : S.R u₀ = (1 + (0 : ℝ))⁻¹ • u₀ := by rw [hu1, key]; simp
  have := S.semigroup_eigen (le_refl (0 : ℝ)) hR t
  have e : tripleSemigroup F.toMarkovTriple t u₀ = u₀ := by
    have h2 : S.semigroup t u₀ = u₀ := by simpa using this
    exact h2
  rw [e]; exact hu

/-- **The Friedrichs semigroup of every full Markov triple is a witness of `IsSemigroupOf`.**
No extra hypothesis: positivity is `isMarkovianForm` (diffusion algebra `𝒜₀`), conservativeness is
`FullMarkovTriple.tripleSemigroup_one` (`esa`, `ibp_A`, `ibp_A_symm`). -/
theorem isSemigroupOf_full (F : FullMarkovTriple E) :
    MarkovTriple.IsSemigroupOf F.toMarkovTriple (tripleSemigroup F.toMarkovTriple) :=
  isSemigroupOf_of_markov_conservative F.toMarkovTriple (isMarkovianForm F.toMarkovTriple)
    (fun t u hu => F.tripleSemigroup_one t u hu)

end MarkovTriple.Hilbert
