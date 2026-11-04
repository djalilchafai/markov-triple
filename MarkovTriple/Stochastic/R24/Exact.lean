import Mathlib
import MarkovTriple.Stochastic.R24.Extend
import MarkovTriple.Stochastic.R23.Triple
import MarkovTriple.Stochastic.KernelRep
import MarkovTriple.Stochastic.Bridge

/-!
# Round 24 (C), part 5: exact Chapman-Kolmogorov, sub-invariance and representation for infinite `μ`

Main results for `hF : IsFellerC0 T` (`T.μ` finite on compacts, full support; `T.μ` may be infinite):

* `fellerKernelInf_zero`, `fellerKernelInf_add`: `κ_0 = id`, `κ_{s+t} = κ_t ∘ₖ κ_s` EXACTLY (all `s, t`, all `x`);
* `fellerKernelInf_bind_le`: `μ.bind κ_t ≤ μ` (symmetry; R23 `bind_le_of_rep`);
* `fellerKernelInf_rep`: representation of `P_t` on all bounded measurable `L²` functions (a.e.);
* `fellerKernelRepInf : KernelRepresentation T`, `fellerSemigroupInf : SubMarkovKernelSemigroup X`,
  `fellerKernelInf_unique`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R23

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

/-- **`κ_0 = id`** -/
theorem fellerKernelInf_zero : fellerKernelInf hF 0 = Kernel.id := by
  ext x : 1
  rw [Kernel.id_apply]
  refine ext_of_integral_cc fun f => ?_
  rw [integral_fellerKernelInf, Qop_zero, integral_dirac]

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] in
/-- the `L²` class of `Q_t f` -/
lemma memLp_Qop (t : ℝ≥0) (f : C_c(X, ℝ)) : MemLp (Qop hF t f) 2 T.μ :=
  (Lp.memLp (T.semigroup t (ccL2 T f))).ae_eq (Qop_ae hF t f)

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] in
lemma semigroup_ccL2_eq (t : ℝ≥0) (f : C_c(X, ℝ)) :
    T.semigroup t (ccL2 T f) = (memLp_Qop hF t f).toLp (Qop hF t f) :=
  Lp.ext ((Qop_ae hF t f).trans (memLp_Qop hF t f).coeFn_toLp.symm)

/-- **Chapman-Kolmogorov for `Q`**: `Q_{s+t} f (x) = ∫ Q_t f dκ_s(x,·)` for every `x`. -/
theorem Qop_add_time (s t : ℝ≥0) (f : C_c(X, ℝ)) (x : X) :
    Qop hF (s + t) f x = ∫ y, Qop hF t f y ∂(fellerKernelInf hF s x) := by
  have h1 : (⇑(Qop hF (s + t) f) : X → ℝ) =ᵐ[T.μ]
      fun x => ∫ y, Qop hF t f y ∂(fellerKernelInf hF s x) := by
    have e : T.semigroup (s + t) (ccL2 T f)
        = T.semigroup s ((memLp_Qop hF t f).toLp (Qop hF t f)) := by
      rw [DiffusionTriple.semigroup_add]
      show T.semigroup s (T.semigroup t (ccL2 T f)) = _
      rw [semigroup_ccL2_eq hF t f]
    have h2 := Qop_ae hF (s + t) f
    rw [e] at h2
    filter_upwards [h2, fellerKernelInf_rep_C0 hF s (Qop hF t f) (memLp_Qop hF t f)] with y a b
    rw [← a, b]
  have hc : Continuous fun x => ∫ y, Qop hF t f y ∂(fellerKernelInf hF s x) :=
    continuous_integral_fellerKernelInf hF s (Qop hF t f)
  exact congrFun (((Qop hF (s + t) f).continuous.ae_eq_iff_eq T.μ hc).1 h1) x

/-- **Exact Chapman-Kolmogorov**: `κ_{s+t} = κ_t ∘ₖ κ_s`, for all `s, t` and all `x`. -/
theorem fellerKernelInf_add (s t : ℝ≥0) :
    fellerKernelInf hF (s + t) = fellerKernelInf hF t ∘ₖ fellerKernelInf hF s := by
  ext x : 1
  refine ext_of_integral_cc fun f => ?_
  have hint : Integrable f ((fellerKernelInf hF t ∘ₖ fellerKernelInf hF s) x) :=
    f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  rw [Kernel.integral_comp hint]
  simp_rw [integral_fellerKernelInf]
  rw [Qop_add_time hF s t f x]

/-- the `L²` class of a `C_0 ∩ L²` function equals any a.e.-equal element -/
lemma rep_of_ae_C0 (s : ℝ≥0) (f : C₀(X, ℝ)) (u : Lp ℝ 2 T.μ) (hu : (u : X → ℝ) =ᵐ[T.μ] f) :
    (T.semigroup s u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(fellerKernelInf hF s x) := by
  have hL : MemLp f 2 T.μ := (Lp.memLp u).ae_eq hu
  have e : u = hL.toLp f := Lp.ext (hu.trans hL.coeFn_toLp.symm)
  rw [e]
  exact fellerKernelInf_rep_C0 hF s f hL

/-- **Sub-invariance** `μ.bind κ_t ≤ μ` -/
theorem fellerKernelInf_bind_le (t : ℝ≥0) : T.μ.bind (fellerKernelInf hF t) ≤ T.μ :=
  bind_le_of_rep (T.semigroup t) (fun _ hu => T.semigroup_nonneg t hu)
    (fun u hu => T.semigroup_le_one t u hu) (T.semigroup_isSelfAdjoint t) (fellerKernelInf hF t)
    (fellerKernelInf_subMarkov hF t) (rep_of_ae_C0 hF t)

/-- **Representation on all bounded measurable `L²` functions** (a.e.) -/
theorem fellerKernelInf_rep (t : ℝ≥0) (g : X → ℝ) (hg : Measurable g) (hb : ∃ C, ∀ x, |g x| ≤ C)
    (hL : MemLp g 2 T.μ) :
    (T.semigroup t (hL.toLp g) : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(fellerKernelInf hF t x) := by
  refine kernelRep_of_dense (D := (ccSet : Set (X → ℝ))) (fellerKernelInf hF)
    (fellerKernelInf_subMarkov hF) (fellerKernelInf_bind_le hF) ?_ ?_ ?_ (cc_dense T) ?_ t g hg hb hL
  · intro f hf; exact hf.1.measurable
  · intro f hf; exact ccSet_bdd hf
  · intro f hf; exact ccSet_memLp T hf
  · intro t f hf
    let f' : C_c(X, ℝ) := ⟨⟨f, hf.1⟩, hf.2⟩
    have := Qop_ae hF t f'
    filter_upwards [this] with x hx
    have h2 : (T.semigroup t ((ccSet_memLp T hf).toLp f) : X → ℝ) x = Qop hF t f' x := hx
    rw [h2, ← integral_fellerKernelInf hF t x f']
    rfl

/-- **The `KernelRepresentation` of a `C_0`-Feller triple**, exact everywhere-defined kernels. -/
noncomputable def fellerKernelRepInf : KernelRepresentation T where
  κ := fellerKernelInf hF
  subMarkov := fellerKernelInf_subMarkov hF
  rep := fun t g hg hb hL => fellerKernelInf_rep hF t g hg hb hL

/-- **The exact sub-Markov kernel semigroup** of a `C_0`-Feller triple (infinite `μ` allowed). -/
noncomputable def fellerSemigroupInf : SubMarkovKernelSemigroup X where
  κ := fellerKernelInf hF
  subMarkov := fellerKernelInf_subMarkov hF
  zero := fellerKernelInf_zero hF
  add := fellerKernelInf_add hF

theorem fellerKernelInf_integral_cc (t : ℝ≥0) (f : C_c(X, ℝ)) (u : Lp ℝ 2 T.μ)
    (hu : (u : X → ℝ) =ᵐ[T.μ] f) :
    ∃ g : C₀(X, ℝ), (∀ x, g x = ∫ y, f y ∂(fellerKernelInf hF t x)) ∧
      (T.semigroup t u : X → ℝ) =ᵐ[T.μ] g := by
  refine ⟨Qop hF t f, fun x => (integral_fellerKernelInf hF t x f).symm, ?_⟩
  have e : u = ccL2 T f := Lp.ext (hu.trans (coeFn_ccL2 f).symm)
  rw [e]
  exact Qop_ae hF t f

/-- **Uniqueness (everywhere)**: a finite-measure kernel which is weakly continuous on `C_c` and represents
`P_t` on `C_c` a.e. coincides with `fellerKernelInf` at every point. -/
theorem fellerKernelInf_unique (t : ℝ≥0) (κ' : Kernel X X) [∀ x, IsFiniteMeasure (κ' x)]
    (hc : ∀ f : C_c(X, ℝ), Continuous fun x => ∫ y, f y ∂(κ' x))
    (hr : ∀ (f : C_c(X, ℝ)) (u : Lp ℝ 2 T.μ), (u : X → ℝ) =ᵐ[T.μ] f →
      (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ' x)) (x : X) :
    κ' x = fellerKernelInf hF t x := by
  refine ext_of_integral_cc fun f => ?_
  rw [integral_fellerKernelInf]
  have h : (fun x => ∫ y, f y ∂(κ' x)) = ⇑(Qop hF t f) :=
    ((hc f).ae_eq_iff_eq T.μ (Qop hF t f).continuous).1
      ((hr f (ccL2 T f) (coeFn_ccL2 f)).symm.trans (Qop_ae hF t f))
  exact congrFun h x

end MarkovTriple.Stochastic.R24
