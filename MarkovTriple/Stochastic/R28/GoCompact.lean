import Mathlib
import MarkovTriple.Stochastic.R28.Transport
import MarkovTriple.Stochastic.FellerStandard

/-!
# Round 28 (M), part 5: the transported semigroup of `goFullTriple` is conservative and Feller on `[-1,1]`

* `goSG_one`: `P_t 1 = 1` (from S11 of `goFullTriple`, `standardSemigroup_one_fin`);
* `goI_isFeller`: `P_t [f]` has a continuous representative for every `f ∈ C([-1,1])`: polynomials are dense (Weierstrass), `P_t`
  maps polynomial classes to polynomial classes (R27 `go_semigroup_poly_cls`), and `isFellerSG_of_dense`.
-/

open MeasureTheory Filter Topology Set Polynomial
open scoped ENNReal NNReal

namespace MarkovTriple.Stochastic.R28

open MarkovTriple.BGL MarkovTriple.BGL.Instances.GegenbauerOpen MarkovTriple.Stochastic MarkovTriple.Stochastic.R27

instance : IsFiniteMeasure goFullTriple.toDiffusionTriple.μ := (inferInstance : IsFiniteMeasure goμ)

instance : IsFiniteMeasure goFullTriple.toStandardTriple.μ := (inferInstance : IsFiniteMeasure goμ)

/-- `P_t 1 = 1` for the original semigroup -/
theorem goP_one (t : ℝ≥0) :
    goFullTriple.toDiffusionTriple.semigroup t goFullTriple.toDiffusionTriple.one2
      = goFullTriple.toDiffusionTriple.one2 := by
  exact standardSemigroup_one_fin goFullTriple.toStandardTriple t

lemma goRestr_one2 : goRestr goFullTriple.toDiffusionTriple.one2 = goSG.one2 := by
  refine Lp.ext ?_
  filter_upwards [coeFn_goRestr goFullTriple.toDiffusionTriple.one2,
    (ae_goμ_iff (p := fun x => (goFullTriple.toDiffusionTriple.one2 : ℝ → ℝ) x = 1)).1
      goFullTriple.toDiffusionTriple.coeFn_one2, goSG.coeFn_one2] with x h1 h2 h3
  rw [h1]
  show (goFullTriple.toDiffusionTriple.one2 : ℝ → ℝ) x.1 = _
  rw [h2]; exact h3.symm

/-- **conservativeness of the transported semigroup** -/
theorem goSG_one (t : ℝ≥0) : goSG.semigroup t goSG.one2 = goSG.one2 := by
  have h := goSemigroupI_restr t goFullTriple.toDiffusionTriple.one2
  rw [goP_one, goRestr_one2] at h
  exact h

/-- the polynomial `q` as a continuous function on `[-1,1]` -/
noncomputable def polyI (q : ℝ[X]) : C(GI, ℝ) := q.toContinuousMapOn (Icc (-1 : ℝ) 1)

lemma polyI_apply (q : ℝ[X]) (x : GI) : polyI q x = q.eval x.1 := by
  simp [polyI, Polynomial.toContinuousMapOn]

lemma goRestr_polyι (q : ℝ[X]) : goRestr (polyι q) = clsC goμI (polyI q) := by
  refine Lp.ext ?_
  filter_upwards [coeFn_goRestr (polyι q),
    (ae_goμ_iff (p := fun x => (polyι q : ℝ → ℝ) x = polyFn q x)).1 (coeFn_polyLp q),
    coeFn_clsC (μ := goμI) (polyI q)] with x h1 h2 h3
  rw [h1]
  show (polyι q : ℝ → ℝ) x.1 = _
  rw [h2, h3, polyI_apply]
  rfl

/-- **`goSG` is Feller** -/
theorem goI_isFeller : IsFellerSG goSG := by
  refine isFellerSG_of_dense goSG (D := (polynomialFunctions (Icc (-1 : ℝ) 1) : Set C(GI, ℝ))) ?_ ?_
  · rw [dense_iff_closure_eq, ← Subalgebra.topologicalClosure_coe, polynomialFunctions_closure_eq_top]; rfl
  · intro t d hd
    obtain ⟨q, -, rfl⟩ : d ∈ Set.range (Polynomial.toContinuousMapOnAlgHom (Icc (-1 : ℝ) 1)) := by
      rwa [← polynomialFunctions_coe]
    obtain ⟨q', hq'⟩ := go_semigroup_poly_cls t q
    refine ⟨polyI q', ?_⟩
    have e : clsC goμI (Polynomial.toContinuousMapOnAlgHom (Icc (-1 : ℝ) 1) q) = goRestr (polyι q) :=
      (goRestr_polyι q).symm
    change (goSemigroupI t (clsC goμI (Polynomial.toContinuousMapOnAlgHom (Icc (-1 : ℝ) 1) q)) : GI → ℝ)
      =ᵐ[goμI] _
    rw [e]
    rw [goSemigroupI_restr, show goFullTriple.toDiffusionTriple.semigroup t (polyι q) = polyι q' from hq',
      goRestr_polyι]
    exact coeFn_clsC (μ := goμI) (polyI q')

end MarkovTriple.Stochastic.R28
