import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2Weighted
import MarkovTriple.BGL.Instances.Gibbs.Core2Cut

/-!
# Gibbs on `ℝ`: weighted jets of the resolvent and the graph-norm cut-off estimates for `BddHess` (R18, Stream A2)

Statements: `STATEMENTS_R18_Core2.md` (B3, B4).  `resolvent_weighted_L2` derives the list (W) of the statement file from
`memLp_deriv_resolvent` (Caccioppoli), `memLp_of_BE` and `memLp_of_hardy`; `cutoff_ZL_w` is the weighted analogue of
`cutoff_ZL`: the commutators are `ψ_n^{(j)} × (weighted jet of v)` (`j = 1..4`), with `Good` coefficients `ψ_n^{(j)}`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL.Lebesgue (chiR Rn Rn_pos chiR_smooth chiR_cs chiR_eq_one_of)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

/-- a bounded continuous coefficient times an `L²` function is `L²`. -/
lemma memLp_mul_bdd {μ : Measure ℝ} {c g : ℝ → ℝ} {C : ℝ} (hc : Continuous c) (hb : ∀ x, |c x| ≤ C)
    (hg : MemLp g 2 μ) (hgm : AEStronglyMeasurable g μ) : MemLp (fun x => c x * g x) 2 μ :=
  hg.of_le_mul (c := C) (hc.aestronglyMeasurable.mul hgm)
    (Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _))

/-- the atoms of the cut-off coefficient families: `χ_n - 1`, `χ_n', χ_n'', χ_n''', χ_n''''` are `Good`. -/
lemma good_chi_atoms :
    Good (fun n x => chiR (Rn n) x - 1) ∧ Good (fun n x => deriv (chiR (Rn n)) x) ∧
    Good (fun n x => deriv (deriv (chiR (Rn n))) x) ∧
    Good (fun n x => deriv (deriv (deriv (chiR (Rn n)))) x) ∧
    Good (fun n x => deriv (deriv (deriv (deriv (chiR (Rn n))))) x) := by
  obtain ⟨K, hK1, hK⟩ := chiR_iter_bound
  have a0 : UB (fun n x => chiR (Rn n) x) := ⟨K, fun n x => by simpa using hK 0 (by norm_num) n x⟩
  have a1 : UB (fun n x => deriv (chiR (Rn n)) x) := ⟨K, fun n x => by simpa using hK 1 (by norm_num) n x⟩
  have a2 : UB (fun n x => deriv (deriv (chiR (Rn n))) x) :=
    ⟨K, fun n x => by simpa using hK 2 (by norm_num) n x⟩
  have a3 : UB (fun n x => deriv (deriv (deriv (chiR (Rn n)))) x) :=
    ⟨K, fun n x => by simpa using hK 3 (by norm_num) n x⟩
  have a4 : UB (fun n x => deriv (deriv (deriv (deriv (chiR (Rn n))))) x) :=
    ⟨K, fun n x => by simpa using hK 4 (by norm_num) n x⟩
  have ψs : ∀ n, Sm (chiR (Rn n)) := fun n => chiR_smooth _
  have c0 : ∀ n, Continuous (chiR (Rn n)) := fun n => (ψs n).continuous
  have c1 : ∀ n, Continuous (deriv (chiR (Rn n))) := fun n => (ψs n).deriv'.continuous
  have c2 : ∀ n, Continuous (deriv (deriv (chiR (Rn n)))) := fun n => (ψs n).deriv'.deriv'.continuous
  have c3 : ∀ n, Continuous (deriv (deriv (deriv (chiR (Rn n))))) :=
    fun n => (ψs n).deriv'.deriv'.deriv'.continuous
  have c4 : ∀ n, Continuous (deriv (deriv (deriv (deriv (chiR (Rn n)))))) :=
    fun n => (ψs n).deriv'.deriv'.deriv'.deriv'.continuous
  have z : ∀ x, ∀ᶠ n in atTop, chiR (Rn n) x = 1 ∧ deriv (chiR (Rn n)) x = 0 ∧
      deriv (deriv (chiR (Rn n))) x = 0 ∧ deriv (deriv (deriv (chiR (Rn n)))) x = 0 ∧
      deriv (deriv (deriv (deriv (chiR (Rn n))))) x = 0 := by
    intro x
    filter_upwards [chiR_eventually_lt x] with n hn
    exact ⟨chiR_eq_one_of (Rn_pos n) hn.le, chiR_iter_zero hn 0, chiR_iter_zero hn 1,
      chiR_iter_zero hn 2, chiR_iter_zero hn 3⟩
  have one : UB (fun (_ : ℕ) (_ : ℝ) => (1 : ℝ)) := UB.const 1
  refine ⟨⟨fun n => (c0 n).sub continuous_const, a0.sub one, fun x => ?_⟩, ⟨c1, a1, fun x => ?_⟩,
    ⟨c2, a2, fun x => ?_⟩, ⟨c3, a3, fun x => ?_⟩, ⟨c4, a4, fun x => ?_⟩⟩
  · filter_upwards [z x] with n hn
    simp [hn.1]
  · filter_upwards [z x] with n hn
    exact hn.2.1
  · filter_upwards [z x] with n hn
    exact hn.2.2.1
  · filter_upwards [z x] with n hn
    exact hn.2.2.2.1
  · filter_upwards [z x] with n hn
    exact hn.2.2.2.2

namespace GibbsData
variable (G : GibbsData)

/-- a coefficient `c` with `|c| ≤ C (1 + |V'|)` times an `L²` function `g` with `V' g ∈ L²` is `L²`. -/
lemma memLp_mul_growth {c g : ℝ → ℝ} {C : ℝ} (hc : Continuous c) (hC : 0 ≤ C)
    (hb : ∀ x, |c x| ≤ C * (1 + |deriv G.V x|)) (hg : MemLp g 2 G.μ)
    (hVg : MemLp (fun x => deriv G.V x * g x) 2 G.μ) (hgm : AEStronglyMeasurable g G.μ) :
    MemLp (fun x => c x * g x) 2 G.μ := by
  have hdom : MemLp (fun x => C * (‖g x‖ + ‖deriv G.V x * g x‖)) 2 G.μ :=
    (hg.norm.add hVg.norm).const_mul C
  refine hdom.mono (hc.aestronglyMeasurable.mul hgm) (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  have h0 : 0 ≤ C * (|g x| + |deriv G.V x| * |g x|) := by positivity
  have h1 : |c x| * |g x| ≤ C * (1 + |deriv G.V x|) * |g x| :=
    mul_le_mul_of_nonneg_right (hb x) (abs_nonneg _)
  rw [abs_of_nonneg hC, abs_of_nonneg (by positivity : 0 ≤ |g x| + |deriv G.V x| * |g x|)]
  nlinarith [h1]

/-- **B3**: the weighted jets (W) of the resolvent solution are in `L²(μ)` under the growth condition `GrowHess`
(`V'` arbitrary).  Output order: `V'v`, `V'(V'v)`, `v'`, `V''v'`, `V'v'`, `v''`, `V'v''`, `v'''`. -/
theorem resolvent_weighted_L2 (hb : G.GrowHess) {v a : ℝ → ℝ} (hv : Sm v) (ha : a ∈ OA₀)
    (hv2 : MemLp v 2 G.μ) (hL : ∀ x, Lg G.V v x = v x - a x) :
    MemLp (fun x => deriv G.V x * v x) 2 G.μ ∧
    MemLp (fun x => deriv G.V x * (deriv G.V x * v x)) 2 G.μ ∧
    MemLp (deriv v) 2 G.μ ∧ MemLp (fun x => deriv (deriv G.V) x * deriv v x) 2 G.μ ∧
    MemLp (fun x => deriv G.V x * deriv v x) 2 G.μ ∧ MemLp (deriv (deriv v)) 2 G.μ ∧
    MemLp (fun x => deriv G.V x * deriv (deriv v) x) 2 G.μ ∧
    MemLp (deriv (deriv (deriv v))) 2 G.μ := by
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hC 0).1
    have hp : 0 < 1 + |deriv G.V 0| := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hB2 : ∀ x, |deriv (deriv G.V) x| ≤ C * (1 + |deriv G.V x|) := fun x => (hC x).1
  have hρ : ∀ x, -(C * (1 + |deriv G.V x|)) ≤ deriv (deriv G.V) x := fun x => (abs_le.1 (hB2 x)).1
  have hup : ∀ x, deriv (deriv G.V) x ≤ deriv G.V x ^ 2 / 4 + (C + C ^ 2) := by
    intro x
    have h := (abs_le.1 (hB2 x)).2
    nlinarith [sq_nonneg (deriv G.V x / 2 - C), abs_nonneg (deriv G.V x), sq_abs (deriv G.V x),
      abs_mul_abs_self (deriv G.V x), le_abs_self (deriv G.V x), neg_abs_le (deriv G.V x),
      sq_nonneg (|deriv G.V x| / 2 - C)]
  have hCC : 0 ≤ C + C ^ 2 := by positivity
  have h1 := G.memLp_deriv_resolvent hv ha hv2 hL
  have haL : MemLp a 2 G.μ := ha.1.continuous.memLp_of_hasCompactSupport ha.2
  have ha'L : MemLp (deriv a) 2 G.μ :=
    ha.1.deriv'.continuous.memLp_of_hasCompactSupport ha.2.deriv
  have hVv := G.memLp_of_hardy hCC hv hv2 h1 hup
  have hVs : Sm (fun x => deriv G.V x * v x) := G.smooth.deriv'.mul hv
  have hd : deriv (fun x => deriv G.V x * v x) =
      fun x => deriv (deriv G.V) x * v x + deriv G.V x * deriv v x := funext fun x =>
    ((G.smooth.deriv'.hasDerivAt x).mul (hv.hasDerivAt x)).deriv
  -- (BE) for `v'`
  have hq1 : (fun x => deriv (deriv v) x - deriv G.V x * deriv v x) = fun x => v x - a x :=
    funext fun x => by have := hL x; unfold Lg at this; linarith
  have hV1 : MemLp (fun x => deriv G.V x * deriv v x) 2 G.μ :=
    G.memLp_of_BE hC0 hv.deriv' h1 (by rw [hq1]; exact hv2.sub haL) hρ
  have e2 : deriv (deriv v) = fun x => (v x - a x) + deriv G.V x * deriv v x := by
    funext x; have := hL x; unfold Lg at this; linarith
  have h2 : MemLp (deriv (deriv v)) 2 G.μ := by
    rw [e2]; exact (hv2.sub haL).add hV1
  -- `V' (V' v)` (Hardy for `V' v`)
  have hV2v : MemLp (fun x => deriv (deriv G.V) x * v x) 2 G.μ :=
    G.memLp_mul_growth G.smooth.deriv'.deriv'.continuous hC0 hB2 hv2 hVv
      hv.continuous.aestronglyMeasurable
  have hVVd : MemLp (fun x => deriv (deriv G.V) x * v x + deriv G.V x * deriv v x) 2 G.μ :=
    hV2v.add hV1
  have hVV := G.memLp_of_hardy hCC hVs hVv (by rw [hd]; exact hVVd) hup
  -- `V'' v'`
  have hV2 : MemLp (fun x => deriv (deriv G.V) x * deriv v x) 2 G.μ :=
    G.memLp_mul_growth G.smooth.deriv'.deriv'.continuous hC0 hB2 h1 hV1
      hv.deriv'.continuous.aestronglyMeasurable
  -- (BE) for `v''`
  have e3 : deriv (deriv (deriv v)) = fun x => deriv v x - deriv a x + deriv (deriv G.V) x * deriv v x +
      deriv G.V x * deriv (deriv v) x := by
    funext x
    have h3 : deriv (deriv (deriv v)) x = deriv (fun x => (v x - a x) + deriv G.V x * deriv v x) x :=
      congrArg (fun f => deriv f x) e2
    have := (((hv.hasDerivAt x).sub (ha.1.hasDerivAt x)).add
      ((G.smooth.deriv'.hasDerivAt x).mul (hv.deriv'.hasDerivAt x)))
    rw [h3]
    refine this.deriv.trans ?_
    ring
  have hq2 : (fun x => deriv (deriv (deriv v)) x - deriv G.V x * deriv (deriv v) x) =
      fun x => (deriv v x - deriv a x) + deriv (deriv G.V) x * deriv v x :=
    funext fun x => by rw [show deriv (deriv (deriv v)) x = _ from congrFun e3 x]; ring
  have hV1' : MemLp (fun x => deriv G.V x * deriv (deriv v) x) 2 G.μ :=
    G.memLp_of_BE hC0 hv.deriv'.deriv' h2 (by rw [hq2]; exact (h1.sub ha'L).add hV2) hρ
  have h3 : MemLp (deriv (deriv (deriv v))) 2 G.μ := by
    rw [e3]; exact ((h1.sub ha'L).add hV2).add hV1'
  exact ⟨hVv, hVV, h1, hV2, hV1, h2, hV1', h3⟩

/-- **B4**: the three graph-norm cut-off estimates `χ_n v → v`, `L(χ_n v) → L v`, `L²(χ_n v) → L² v` in `L²(μ)`,
under `GrowHess` (`V'` arbitrary). -/
theorem cutoff_ZL_w (hb : G.GrowHess) {v a : ℝ → ℝ} (hv : Sm v) (ha : a ∈ OA₀) (hv2 : MemLp v 2 G.μ)
    (hL : ∀ x, Lg G.V v x = v x - a x) :
    ZL G.μ (fun n x => chiR (Rn n) x * v x - v x) ∧
    ZL G.μ (fun n x => Lg G.V (chiR (Rn n) * v) x - Lg G.V v x) ∧
    ZL G.μ (fun n x => Lg G.V (Lg G.V (chiR (Rn n) * v)) x - Lg G.V (Lg G.V v) x) := by
  obtain ⟨hVv, hVVv, h1, hV2v1, hV1v1, h2, hV1v2, h3⟩ := G.resolvent_weighted_L2 hb hv ha hv2 hL
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := by
    have h := (abs_nonneg _).trans (hC 0).1
    have hp : 0 < 1 + |deriv G.V 0| := by positivity
    exact nonneg_of_mul_nonneg_left h hp
  have hB2 : ∀ x, |deriv (deriv G.V) x| ≤ C * (1 + |deriv G.V x|) := fun x => (hC x).1
  have hB3 : ∀ x, |deriv (deriv (deriv G.V)) x| ≤ C * (1 + |deriv G.V x|) := fun x => (hC x).2
  obtain ⟨g1, gψ1, gψ2, gψ3, gψ4⟩ := good_chi_atoms
  have haL : MemLp a 2 G.μ := ha.1.continuous.memLp_of_hasCompactSupport ha.2
  have hLa : Lg G.V a ∈ OA₀ := G.Lg_mem ha
  have hLaL : MemLp (Lg G.V a) 2 G.μ := hLa.1.continuous.memLp_of_hasCompactSupport hLa.2
  have hVa : MemLp (fun x => deriv G.V x * a x) 2 G.μ :=
    (G.smooth.deriv'.continuous.mul ha.1.continuous).memLp_of_hasCompactSupport ha.2.mul_left
  have hLvf : Lg G.V v = fun x => v x - a x := funext hL
  have hLv : MemLp (Lg G.V v) 2 G.μ := by rw [hLvf]; exact hv2.sub haL
  have hLLvx : ∀ x, Lg G.V (Lg G.V v) x = (v x - a x) - Lg G.V a x := by
    intro x
    have e : Lg G.V v = v - a := by rw [hLvf]; rfl
    rw [e, Lg_sub hv ha.1 x, hL x]
  have hLLv : MemLp (Lg G.V (Lg G.V v)) 2 G.μ := by
    have : Lg G.V (Lg G.V v) = fun x => (v x - a x) - Lg G.V a x := funext hLLvx
    rw [this]; exact (hv2.sub haL).sub hLaL
  have hVLv : MemLp (fun x => deriv G.V x * Lg G.V v x) 2 G.μ := by
    have : (fun x => deriv G.V x * Lg G.V v x) = fun x => deriv G.V x * v x - deriv G.V x * a x := by
      funext x; rw [hL x]; ring
    rw [this]; exact hVv.sub hVa
  have hV3v : MemLp (fun x => deriv (deriv (deriv G.V)) x * v x) 2 G.μ :=
    G.memLp_mul_growth G.smooth.deriv'.deriv'.deriv'.continuous hC0 hB3 hv2 hVv
      hv.continuous.aestronglyMeasurable
  have hV2Vv : MemLp (fun x => deriv (deriv G.V) x * (deriv G.V x * v x)) 2 G.μ :=
    G.memLp_mul_growth G.smooth.deriv'.deriv'.continuous hC0 hB2 hVv hVVv
      (G.smooth.deriv'.continuous.mul hv.continuous).aestronglyMeasurable
  have hV2v : MemLp (fun x => deriv (deriv G.V) x * v x) 2 G.μ :=
    G.memLp_mul_growth G.smooth.deriv'.deriv'.continuous hC0 hB2 hv2 hVv
      hv.continuous.aestronglyMeasurable
  -- the weighted coefficient functions
  set F1 : ℝ → ℝ := fun x => (deriv (deriv G.V) x * (deriv G.V x * v x) - deriv (deriv (deriv G.V)) x * v x)
    - 4 * (deriv (deriv G.V) x * deriv v x) - 4 * (deriv G.V x * deriv (deriv v) x) +
    4 * deriv (deriv (deriv v)) x - 2 * (deriv G.V x * Lg G.V v x) with hF1
  set F2 : ℝ → ℝ := fun x => (deriv G.V x * (deriv G.V x * v x) - 2 * (deriv (deriv G.V) x * v x))
    - 4 * (deriv G.V x * deriv v x) + 4 * deriv (deriv v) x + 2 * Lg G.V v x with hF2
  set F3 : ℝ → ℝ := fun x => -2 * (deriv G.V x * v x) + 4 * deriv v x with hF3
  set Fa : ℝ → ℝ := fun x => -(deriv G.V x * v x) + 2 * deriv v x with hFa
  have mF1 : MemLp F1 2 G.μ :=
    ((((hV2Vv.sub hV3v).sub (hV2v1.const_mul 4)).sub (hV1v2.const_mul 4)).add (h3.const_mul 4)).sub
      (hVLv.const_mul 2)
  have mF2 : MemLp F2 2 G.μ :=
    ((((hVVv.sub (hV2v.const_mul 2)).sub (hV1v1.const_mul 4)).add (h2.const_mul 4))).add
      (hLv.const_mul 2)
  have mF3 : MemLp F3 2 G.μ := (hVv.const_mul (-2)).add (h1.const_mul 4)
  have mFa : MemLp Fa 2 G.μ := hVv.neg.add (h1.const_mul 2)
  refine ⟨?_, ?_, ?_⟩
  · exact (ZL.of_good g1 hv2).congr (fun n x => by ring)
  · refine (((ZL.of_good g1 hLv).add (ZL.of_good gψ2 hv2)).add (ZL.of_good gψ1 mFa)).congr
      (fun n x => ?_)
    rw [L_mul_expand (chiR_smooth _) hv x]
    have e : Lg G.V (chiR (Rn n)) x = deriv (deriv (chiR (Rn n))) x - deriv G.V x * deriv (chiR (Rn n)) x := rfl
    rw [e]
    simp only [hFa]
    ring
  · refine (((((ZL.of_good g1 hLLv).add (ZL.of_good gψ4 hv2)).add (ZL.of_good gψ1 mF1)).add
      (ZL.of_good gψ2 mF2)).add (ZL.of_good gψ3 mF3)).congr (fun n x => ?_)
    rw [LL_mul_expand G.smooth (chiR_smooth _) hv x]
    have e : Lg G.V (chiR (Rn n)) x = deriv (deriv (chiR (Rn n))) x - deriv G.V x * deriv (chiR (Rn n)) x := rfl
    simp only [cc0, cc1, cc2, cc3, cc4, hF1, hF2, hF3]
    rw [e]
    ring

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
