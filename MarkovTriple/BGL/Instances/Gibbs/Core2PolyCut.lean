import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2PolyW

/-!
# Gibbs on `ℝ`: weighted jets and graph-norm cut-off estimates under `PolyHess` (R19, Stream A4)

Statements: `STATEMENTS_R19_Core2.md` (D3, D4).  Same scheme as `Core2WCut.lean` (R18), with `GrowHess` replaced by `PolyHess`:
the coefficients `V''`, `V'V''`, `V'''`, `V'² - 2V''` are polynomially dominated by `V'` (`memLp_mul_poly`) and the weights `V'^n v`,
`V'^n v'` come from the cascade `resolvent_pow_L2`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL.Lebesgue (chiR Rn Rn_pos chiR_smooth chiR_cs chiR_eq_one_of)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- the eight weighted jets of the resolvent solution (same output as `resolvent_weighted_L2`). -/
theorem resolvent_weighted_L2_poly (hb : G.PolyHess) {v a : ℝ → ℝ} (hv : Sm v) (ha : a ∈ OA₀)
    (hv2 : MemLp v 2 G.μ) (hL : ∀ x, Lg G.V v x = v x - a x) :
    MemLp (fun x => deriv G.V x * v x) 2 G.μ ∧
    MemLp (fun x => deriv G.V x * (deriv G.V x * v x)) 2 G.μ ∧
    MemLp (deriv v) 2 G.μ ∧ MemLp (fun x => deriv (deriv G.V) x * deriv v x) 2 G.μ ∧
    MemLp (fun x => deriv G.V x * deriv v x) 2 G.μ ∧ MemLp (deriv (deriv v)) 2 G.μ ∧
    MemLp (fun x => deriv G.V x * deriv (deriv v) x) 2 G.μ ∧
    MemLp (deriv (deriv (deriv v))) 2 G.μ := by
  obtain ⟨hlow, hsub, -⟩ := hb
  obtain ⟨Cw, hCw0, hρ⟩ := hlow
  obtain ⟨D, hD0, hD⟩ := G.abs_V2_le ⟨Cw, hCw0, hρ⟩ hsub
  have hpow := G.resolvent_pow_L2 ⟨Cw, hCw0, hρ⟩ hsub hv ha hv2 hL
  have h1 := G.memLp_deriv_resolvent hv ha hv2 hL
  have haL : MemLp a 2 G.μ := ha.1.continuous.memLp_of_hasCompactSupport ha.2
  have ha'L : MemLp (deriv a) 2 G.μ :=
    ha.1.deriv'.continuous.memLp_of_hasCompactSupport ha.2.deriv
  have hVv : MemLp (fun x => deriv G.V x * v x) 2 G.μ := by simpa using (hpow 1).1
  have hVV : MemLp (fun x => deriv G.V x * (deriv G.V x * v x)) 2 G.μ := by
    have e : (fun x => deriv G.V x * (deriv G.V x * v x)) = fun x => deriv G.V x ^ 2 * v x :=
      funext fun x => by ring
    rw [e]; exact (hpow 2).1
  have hV1 : MemLp (fun x => deriv G.V x * deriv v x) 2 G.μ := by simpa using (hpow 1).2
  have hV2 : MemLp (fun x => deriv (deriv G.V) x * deriv v x) 2 G.μ :=
    G.memLp_mul_poly G.smooth.deriv'.deriv'.continuous hD0 hD h1 (hpow 2).2
      hv.deriv'.continuous.aestronglyMeasurable
  have e2 : deriv (deriv v) = fun x => (v x - a x) + deriv G.V x * deriv v x := by
    funext x; have := hL x; unfold Lg at this; linarith
  have h2 : MemLp (deriv (deriv v)) 2 G.μ := by
    rw [e2]; exact (hv2.sub haL).add hV1
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
    G.memLp_of_BE hCw0 hv.deriv'.deriv' h2 (by rw [hq2]; exact (h1.sub ha'L).add hV2) hρ
  have h3 : MemLp (deriv (deriv (deriv v))) 2 G.μ := by
    rw [e3]; exact ((h1.sub ha'L).add hV2).add hV1'
  exact ⟨hVv, hVV, h1, hV2, hV1, h2, hV1', h3⟩

/-- the three graph-norm cut-off estimates `χ_n v → v`, `L(χ_n v) → L v`, `L²(χ_n v) → L² v` in `L²(μ)` under `PolyHess`. -/
theorem cutoff_ZL_p (hb : G.PolyHess) {v a : ℝ → ℝ} (hv : Sm v) (ha : a ∈ OA₀) (hv2 : MemLp v 2 G.μ)
    (hL : ∀ x, Lg G.V v x = v x - a x) :
    ZL G.μ (fun n x => chiR (Rn n) x * v x - v x) ∧
    ZL G.μ (fun n x => Lg G.V (chiR (Rn n) * v) x - Lg G.V v x) ∧
    ZL G.μ (fun n x => Lg G.V (Lg G.V (chiR (Rn n) * v)) x - Lg G.V (Lg G.V v) x) := by
  obtain ⟨hVv, hVVv, h1, hV2v1, hV1v1, h2, hV1v2, h3⟩ := G.resolvent_weighted_L2_poly hb hv ha hv2 hL
  obtain ⟨hlow, hsub, ⟨C3, N, hC3⟩⟩ := hb
  obtain ⟨D, hD0, hD⟩ := G.abs_V2_le hlow hsub
  have hpow := G.resolvent_pow_L2 hlow hsub hv ha hv2 hL
  have hC30 : 0 ≤ C3 := by
    have h := (abs_nonneg _).trans (hC3 0)
    have hp : 0 < 1 + |deriv G.V 0| ^ N := by positivity
    exact nonneg_of_mul_nonneg_left h hp
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
    G.memLp_mul_poly G.smooth.deriv'.deriv'.deriv'.continuous hC30 hC3 hv2 (hpow N).1
      hv.continuous.aestronglyMeasurable
  have hV2Vv : MemLp (fun x => deriv (deriv G.V) x * (deriv G.V x * v x)) 2 G.μ := by
    refine G.memLp_mul_poly G.smooth.deriv'.deriv'.continuous hD0 hD hVv ?_
      (G.smooth.deriv'.continuous.mul hv.continuous).aestronglyMeasurable
    have e : (fun x => deriv G.V x ^ 2 * (deriv G.V x * v x)) = fun x => deriv G.V x ^ 3 * v x :=
      funext fun x => by ring
    rw [e]; exact (hpow 3).1
  have hV2v : MemLp (fun x => deriv (deriv G.V) x * v x) 2 G.μ :=
    G.memLp_mul_poly G.smooth.deriv'.deriv'.continuous hD0 hD hv2 (hpow 2).1
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
