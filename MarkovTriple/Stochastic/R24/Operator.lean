import Mathlib
import MarkovTriple.Stochastic.R23.Triple
import MarkovTriple.Stochastic.FellerKernel

/-!
# Round 24 (C), part 1: the exact operators `Q_t : C_c → C_0` of a `C_0`-Feller triple

`IsFellerC0 T`: for every `t` and every `u ∈ L²(μ)` that is (a.e.) a compactly supported continuous function,
`P_t u` has a representative in `C_0(X)`.  For full-support `μ` this representative is unique, so the a.e.
properties of `P_t` (linearity, positivity, sup-norm bound, `P_0 = id`) become exact properties of
`Q_t : C_c(X,ℝ) → C_0(X,ℝ)`.  See `STATEMENTS_R24_C.md`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R23

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

/-- **`C_0`-Feller property**: `P_t` maps compactly supported continuous functions to (classes of)
`C_0` functions. -/
def IsFellerC0 (T : DiffusionTriple X) : Prop :=
  ∀ (t : ℝ≥0) (f : C_c(X, ℝ)) (u : Lp ℝ 2 T.μ), (u : X → ℝ) =ᵐ[T.μ] f →
    ∃ g : C₀(X, ℝ), (T.semigroup t u : X → ℝ) =ᵐ[T.μ] g

section Cc

variable {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ]

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma cc_memLp (f : C_c(X, ℝ)) : MemLp f 2 T.μ :=
  f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport

/-- the `L²` class of a compactly supported continuous function -/
noncomputable def ccL2 (T : DiffusionTriple X) [IsFiniteMeasureOnCompacts T.μ] (f : C_c(X, ℝ)) :
    Lp ℝ 2 T.μ := (cc_memLp (T := T) f).toLp f

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma coeFn_ccL2 (f : C_c(X, ℝ)) : (ccL2 T f : X → ℝ) =ᵐ[T.μ] f :=
  (cc_memLp (T := T) f).coeFn_toLp

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
lemma ccL2_add (f g : C_c(X, ℝ)) : ccL2 T (f + g) = ccL2 T f + ccL2 T g := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ccL2 (T := T) (f + g), coeFn_ccL2 (T := T) f, coeFn_ccL2 (T := T) g,
    Lp.coeFn_add (ccL2 T f) (ccL2 T g)] with x h1 h2 h3 h4
  rw [h1, h4]; simp [h2, h3]

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
lemma ccL2_smul (c : ℝ) (f : C_c(X, ℝ)) : ccL2 T (c • f) = c • ccL2 T f := by
  refine Lp.ext ?_
  filter_upwards [coeFn_ccL2 (T := T) (c • f), coeFn_ccL2 (T := T) f,
    Lp.coeFn_smul c (ccL2 T f)] with x h1 h2 h3
  rw [h1, h3]; simp [h2]

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
lemma ccL2_nonneg {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x) : 0 ≤ᵐ[T.μ] (ccL2 T f : X → ℝ) := by
  filter_upwards [coeFn_ccL2 (T := T) f] with x hx
  rw [hx]; exact hf x

omit [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] [BorelSpace X]
  [IsFiniteMeasureOnCompacts T.μ] in
/-- sub-Markov bound: `P_t u ≤ c` whenever `u ≤ c`, `c > 0` -/
lemma semigroup_le_const (t : ℝ≥0) (u : Lp ℝ 2 T.μ) {c : ℝ} (hc : 0 < c)
    (hu : (u : X → ℝ) ≤ᵐ[T.μ] fun _ => c) : (T.semigroup t u : X → ℝ) ≤ᵐ[T.μ] fun _ => c := by
  have h1 : ((c⁻¹ • u : Lp ℝ 2 T.μ) : X → ℝ) ≤ᵐ[T.μ] (1 : X → ℝ) := by
    filter_upwards [Lp.coeFn_smul c⁻¹ u, hu] with x h1 h2
    rw [h1]
    simp only [Pi.smul_apply, smul_eq_mul, Pi.one_apply]
    rw [inv_mul_le_iff₀ hc]; simpa using h2
  have h2 := T.semigroup_le_one t _ h1
  filter_upwards [h2, Lp.coeFn_smul c⁻¹ (T.semigroup t u)] with x hx hy
  have e : T.semigroup t (c⁻¹ • u) = c⁻¹ • T.semigroup t u := (T.semigroup t).map_smul c⁻¹ u
  rw [e] at hx
  have hx' : (c⁻¹ • T.semigroup t u : Lp ℝ 2 T.μ) x ≤ 1 := hx
  rw [hy] at hx'
  simp only [Pi.smul_apply, smul_eq_mul] at hx'
  rw [inv_mul_le_iff₀ hc] at hx'
  simpa using hx'

end Cc

section Op

variable {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

/-- the exact (everywhere defined) image `Q_t f ∈ C_0` -/
noncomputable def Qop (t : ℝ≥0) (f : C_c(X, ℝ)) : C₀(X, ℝ) :=
  Classical.choose (hF t f (ccL2 T f) (coeFn_ccL2 f))

omit [T2Space X] [SecondCountableTopology X] [T.μ.IsOpenPosMeasure] [LocallyCompactSpace X] in
lemma Qop_ae (t : ℝ≥0) (f : C_c(X, ℝ)) :
    (T.semigroup t (ccL2 T f) : X → ℝ) =ᵐ[T.μ] ⇑(Qop hF t f) :=
  Classical.choose_spec (hF t f (ccL2 T f) (coeFn_ccL2 f))

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
/-- uniqueness of continuous representatives (full support) -/
lemma Qop_eq_of_ae (t : ℝ≥0) (f : C_c(X, ℝ)) {g : X → ℝ} (hg : Continuous g)
    (h : (T.semigroup t (ccL2 T f) : X → ℝ) =ᵐ[T.μ] g) : (⇑(Qop hF t f) : X → ℝ) = g :=
  ((Qop hF t f).continuous.ae_eq_iff_eq T.μ hg).1 ((Qop_ae hF t f).symm.trans h)

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
lemma Qop_add (t : ℝ≥0) (f g : C_c(X, ℝ)) :
    (⇑(Qop hF t (f + g)) : X → ℝ) = ⇑(Qop hF t f) + ⇑(Qop hF t g) := by
  refine Qop_eq_of_ae hF t (f + g) ((Qop hF t f).continuous.add (Qop hF t g).continuous) ?_
  rw [ccL2_add, map_add]
  filter_upwards [Lp.coeFn_add (T.semigroup t (ccL2 T f)) (T.semigroup t (ccL2 T g)),
    Qop_ae hF t f, Qop_ae hF t g] with x h1 h2 h3
  rw [h1]; simp [h2, h3]

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
lemma Qop_smul (t : ℝ≥0) (c : ℝ) (f : C_c(X, ℝ)) :
    (⇑(Qop hF t (c • f)) : X → ℝ) = c • ⇑(Qop hF t f) := by
  refine Qop_eq_of_ae hF t (c • f) ((Qop hF t f).continuous.const_smul c) ?_
  rw [ccL2_smul, map_smul]
  filter_upwards [Lp.coeFn_smul c (T.semigroup t (ccL2 T f)), Qop_ae hF t f] with x h1 h2
  rw [h1]; simp [h2]

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
lemma Qop_nonneg (t : ℝ≥0) {f : C_c(X, ℝ)} (hf : ∀ x, 0 ≤ f x) (x : X) : 0 ≤ Qop hF t f x := by
  have h := T.semigroup_nonneg t (ccL2_nonneg (T := T) hf)
  have h' : ∀ᵐ y ∂T.μ, 0 ≤ (Qop hF t f).toContinuousMap y := by
    filter_upwards [h, Qop_ae hF t f] with y h1 h2
    have h1' : 0 ≤ (T.semigroup t (ccL2 T f) : X → ℝ) y := h1
    rw [h2] at h1'; exact h1'
  exact cont_nonneg_of_ae (μ := T.μ) (g := (Qop hF t f).toContinuousMap) h' x

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
lemma Qop_zero (f : C_c(X, ℝ)) : (⇑(Qop hF 0 f) : X → ℝ) = f := by
  refine Qop_eq_of_ae hF 0 f f.continuous ?_
  rw [DiffusionTriple.semigroup_zero]
  exact coeFn_ccL2 f

omit [T2Space X] [SecondCountableTopology X] [LocallyCompactSpace X] in
lemma Qop_abs_le (t : ℝ≥0) (f : C_c(X, ℝ)) {C : ℝ} (hC : ∀ y, |f y| ≤ C) (x : X) :
    |Qop hF t f x| ≤ C := by
  have key : ∀ ε : ℝ, 0 < ε → ∀ x, |Qop hF t f x| ≤ C + ε := by
    intro ε hε x
    have hb : ∀ y, |f y| ≤ C + ε := fun y => by linarith [hC y]
    have hpos : 0 < C + ε := by
      have := (abs_nonneg (f x)).trans (hC x); linarith
    have h1 := semigroup_le_const t (ccL2 T f) hpos (by
      filter_upwards [coeFn_ccL2 (T := T) f] with y hy
      rw [hy]; exact (abs_le.1 (hb y)).2)
    have h2 := semigroup_le_const t (-ccL2 T f) hpos (by
      filter_upwards [coeFn_ccL2 (T := T) f, Lp.coeFn_neg (ccL2 T f)] with y hy hn
      rw [hn]; simp only [Pi.neg_apply]; rw [hy]; exact (abs_le.1 (hb y)).1 |> fun h => by linarith)
    rw [map_neg] at h2
    have hbd : ∀ᵐ y ∂T.μ, |(Qop hF t f).toContinuousMap y| ≤ C + ε := by
      filter_upwards [h1, h2, Qop_ae hF t f, Lp.coeFn_neg (T.semigroup t (ccL2 T f))] with y a b c d
      rw [d] at b
      simp only [Pi.neg_apply] at b
      rw [c] at a b
      show |Qop hF t f y| ≤ C + ε
      exact abs_le.2 ⟨by linarith, a⟩
    exact cont_bound_of_ae (μ := T.μ) (g := (Qop hF t f).toContinuousMap) hbd x
  by_contra hcon
  push Not at hcon
  have := key ((|Qop hF t f x| - C) / 2) (by linarith) x
  linarith

end Op

end MarkovTriple.Stochastic.R24
