import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2WMain

/-!
# Non-vacuity of `BddHess` with `ρ > 0` (R18, Stream A2, target B7)

`V(x) = x²/2 + ½ cos x` is a non-Gaussian, uniformly convex (`V'' = 1 - ½ cos x ≥ ½`, so `CD(½, ∞)`) potential with
unbounded `V' = x - ½ sin x` (so `BddJet` of Round 17 FAILS: `cosGibbs_not_bddJet`) and bounded `V'' ∈ [½, 3/2]`,
`V''' = ½ sin x`.  Hence `gibbsFull_core2_of_bddHess` and `gibbs_mem_domain_of_Γ₂_bddHess` apply to a genuine example with
`ρ = ½ > 0`, where the R17 statements were vacuous (ERRATA R17-M1).  A second example, `x⁴/4 + x²/2` (`ρ = 1`, `V', V'', V'''`
all unbounded), satisfies the growth condition `GrowHess` and not `BddHess`.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.Gibbs

/-- `V(x) = x²/2 + ½ cos x`. -/
noncomputable def cosV : ℝ → ℝ := fun x => x ^ 2 / 2 + Real.cos x / 2

lemma hasDerivAt_cosV (x : ℝ) : HasDerivAt cosV (x - Real.sin x / 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  have h2 : HasDerivAt (fun y : ℝ => Real.cos y / 2) (-Real.sin x / 2) x :=
    (Real.hasDerivAt_cos x).div_const 2
  refine (h1.add h2).congr_deriv ?_
  ring

lemma deriv_cosV : deriv cosV = fun x => x - Real.sin x / 2 := funext fun x => (hasDerivAt_cosV x).deriv

lemma hasDerivAt_dcosV (x : ℝ) : HasDerivAt (fun y : ℝ => y - Real.sin y / 2) (1 - Real.cos x / 2) x :=
  ((hasDerivAt_id x).sub ((Real.hasDerivAt_sin x).div_const 2)).congr_deriv (by simp)

lemma deriv_deriv_cosV : deriv (deriv cosV) = fun x => 1 - Real.cos x / 2 := by
  rw [deriv_cosV]; exact funext fun x => (hasDerivAt_dcosV x).deriv

lemma hasDerivAt_ddcosV (x : ℝ) : HasDerivAt (fun y : ℝ => 1 - Real.cos y / 2) (Real.sin x / 2) x :=
  (((hasDerivAt_const x (1 : ℝ)).sub ((Real.hasDerivAt_cos x).div_const 2))).congr_deriv (by ring)

lemma deriv3_cosV : deriv (deriv (deriv cosV)) = fun x => Real.sin x / 2 := by
  rw [deriv_deriv_cosV]; exact funext fun x => (hasDerivAt_ddcosV x).deriv

lemma cosV_smooth : Sm cosV :=
  ((contDiff_id.pow 2).div_const 2).add (Real.contDiff_cos.div_const 2)

lemma cosV_integrable : Integrable (fun x => Real.exp (-cosV x)) := by
  have hI : Integrable (fun x : ℝ => Real.exp (1 / 2) * Real.exp (-(1 / 2) * x ^ 2)) :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)).const_mul _
  refine hI.mono' (Real.continuous_exp.comp cosV_smooth.continuous.neg).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  unfold cosV
  nlinarith [Real.neg_one_le_cos x]

/-- the Gibbs data `e^{-(x²/2 + ½ cos x)}`. -/
noncomputable def cosGibbs : GibbsData where
  V := cosV
  smooth := cosV_smooth
  integrable := cosV_integrable

/-- bounded `V''`, `V'''`. -/
theorem cosGibbs_bddHess : cosGibbs.BddHess := by
  refine ⟨⟨3 / 2, fun x => ?_⟩, ⟨1 / 2, fun x => ?_⟩⟩
  · show |deriv (deriv cosV) x| ≤ 3 / 2
    rw [deriv_deriv_cosV, abs_le]
    constructor <;> nlinarith [Real.neg_one_le_cos x, Real.cos_le_one x]
  · show |deriv (deriv (deriv cosV)) x| ≤ 1 / 2
    rw [deriv3_cosV, abs_le]
    constructor <;> nlinarith [Real.neg_one_le_sin x, Real.sin_le_one x]

/-- uniform convexity: `V'' ≥ ½`, i.e. `ρ = ½ > 0`. -/
theorem cosGibbs_convex : ∀ x, (1 / 2 : ℝ) ≤ deriv (deriv cosGibbs.V) x := fun x => by
  show (1 / 2 : ℝ) ≤ deriv (deriv cosV) x
  rw [deriv_deriv_cosV]
  nlinarith [Real.cos_le_one x]

/-- the Round 17 hypothesis `BddJet` FAILS for this uniformly convex potential (`V'` is unbounded). -/
theorem cosGibbs_not_bddJet : ¬ cosGibbs.BddJet := by
  rintro ⟨⟨C, hC⟩, -, -⟩
  have h : |deriv cosV (|C| + 1)| ≤ C := hC (|C| + 1)
  rw [deriv_cosV] at h
  have hs := Real.sin_le_one (|C| + 1)
  have hs' := Real.neg_one_le_sin (|C| + 1)
  have hCa := le_abs_self C
  have hab := le_abs_self (|C| + 1 - Real.sin (|C| + 1) / 2)
  simp only at h hab
  linarith

/-- **B7**: `Core2` for the uniformly convex, non-Gaussian, unbounded-`V'` potential `x²/2 + ½ cos x`. -/
theorem cosGibbs_core2 : cosGibbs.gibbsFull_unconditional.Core2 :=
  cosGibbs.gibbsFull_core2_of_bddHess cosGibbs_bddHess

/-- **B7**: the unconditional converse of Prop. 3.3.17 for `μ ∝ e^{-x²/2 - ½cos x}` with `ρ = ½`. -/
theorem cosGibbs_mem_domain_of_Γ₂ {f : ℝ → ℝ} (hf : f ∈ cosGibbs.gibbsFull_unconditional.A)
    (hf2 : MemLp f 2 cosGibbs.μ)
    (hG : Integrable (FullTriple.G cosGibbs.gibbsFull_unconditional f f) cosGibbs.μ)
    (hG2 : Integrable (cosGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) cosGibbs.μ) :
    ∃ hF : hf2.toLp f ∈ cosGibbs.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((cosGibbs.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 cosGibbs.μ) : ℝ → ℝ) =ᵐ[cosGibbs.μ] cosGibbs.gibbsFull_unconditional.L f :=
  cosGibbs.gibbs_mem_domain_of_Γ₂_bddHess cosGibbs_bddHess cosGibbs_convex hf hf2 hG hG2

/-! ### A quartic example (`V'' ~ x²`, `V''' ~ x`: NOT in `BddHess`, but in `GrowHess`), `ρ = 1` -/

/-- `V(x) = x⁴/4 + x²/2`. -/
noncomputable def quarV : ℝ → ℝ := fun x => x ^ 4 / 4 + x ^ 2 / 2

lemma hasDerivAt_quarV (x : ℝ) : HasDerivAt quarV (x ^ 3 + x) x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 4 / 4) (x ^ 3) x := by
    simpa using (hasDerivAt_pow 4 x).div_const 4
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    simpa using (hasDerivAt_pow 2 x).div_const 2
  refine (h1.add h2).congr_deriv ?_
  ring

lemma deriv_quarV : deriv quarV = fun x => x ^ 3 + x := funext fun x => (hasDerivAt_quarV x).deriv

lemma deriv_deriv_quarV : deriv (deriv quarV) = fun x => 3 * x ^ 2 + 1 := by
  rw [deriv_quarV]
  funext x
  have h1 : HasDerivAt (fun y : ℝ => y ^ 3 + y) (3 * x ^ 2 + 1) x := by
    exact ((hasDerivAt_pow 3 x).add (hasDerivAt_id x)).congr_deriv (by norm_num)
  exact h1.deriv

lemma deriv3_quarV : deriv (deriv (deriv quarV)) = fun x => 6 * x := by
  rw [deriv_deriv_quarV]
  funext x
  have h1 : HasDerivAt (fun y : ℝ => 3 * y ^ 2 + 1) (6 * x) x := by
    have := ((hasDerivAt_pow 2 x).const_mul 3).add_const 1
    refine this.congr_deriv ?_
    simp; ring
  exact h1.deriv

lemma quarV_smooth : Sm quarV :=
  ((contDiff_id.pow 4).div_const 4).add ((contDiff_id.pow 2).div_const 2)

lemma quarV_integrable : Integrable (fun x => Real.exp (-quarV x)) := by
  have hI : Integrable (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  refine hI.mono' (Real.continuous_exp.comp quarV_smooth.continuous.neg).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  unfold quarV
  nlinarith [sq_nonneg (x ^ 2), sq_nonneg x]

/-- the Gibbs data `e^{-(x⁴/4 + x²/2)}`. -/
noncomputable def quarGibbs : GibbsData where
  V := quarV
  smooth := quarV_smooth
  integrable := quarV_integrable

/-- `V'' = 3x² + 1 ≥ 1`: uniformly convex, `ρ = 1`. -/
theorem quarGibbs_convex : ∀ x, (1 : ℝ) ≤ deriv (deriv quarGibbs.V) x := fun x => by
  show (1 : ℝ) ≤ deriv (deriv quarV) x
  rw [deriv_deriv_quarV]
  nlinarith [sq_nonneg x]

/-- growth condition `|V''|, |V'''| ≤ 6 (1 + |V'|)`. -/
theorem quarGibbs_growHess : quarGibbs.GrowHess := by
  refine ⟨6, fun x => ?_⟩
  have e : |deriv quarV x| = |x| * (x ^ 2 + 1) := by
    rw [deriv_quarV]
    show |x ^ 3 + x| = _
    rw [show x ^ 3 + x = x * (x ^ 2 + 1) by ring, abs_mul, abs_of_pos (by positivity : 0 < x ^ 2 + 1)]
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have ha := abs_nonneg x
  constructor
  · show |deriv (deriv quarV) x| ≤ 6 * (1 + |deriv quarV x|)
    rw [deriv_deriv_quarV, e]
    show |3 * x ^ 2 + 1| ≤ _
    rw [abs_of_pos (by positivity : 0 < 3 * x ^ 2 + 1)]
    rcases le_total |x| 1 with h | h
    · nlinarith [mul_nonneg ha (sq_nonneg x)]
    · nlinarith [mul_nonneg ha (sq_nonneg x), mul_le_mul_of_nonneg_right h (sq_nonneg x)]
  · show |deriv (deriv (deriv quarV)) x| ≤ 6 * (1 + |deriv quarV x|)
    rw [deriv3_quarV, e]
    show |6 * x| ≤ _
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6)]
    nlinarith [mul_nonneg ha (sq_nonneg x)]

/-- `quarGibbs` is outside `BddHess`: `V''' = 6x` is unbounded. -/
theorem quarGibbs_not_bddHess : ¬ quarGibbs.BddHess := by
  rintro ⟨-, ⟨C, hC⟩⟩
  have h : |deriv (deriv (deriv quarV)) (|C| + 1)| ≤ C := hC (|C| + 1)
  rw [deriv3_quarV] at h
  simp only at h
  have h2 := le_abs_self (6 * (|C| + 1))
  have h3 := le_abs_self C
  nlinarith [abs_nonneg C]

/-- **`Core2` for the quartic uniformly convex potential `x⁴/4 + x²/2`** (`ρ = 1`, `V'`, `V''`, `V'''` all unbounded). -/
theorem quarGibbs_core2 : quarGibbs.gibbsFull_unconditional.Core2 :=
  quarGibbs.gibbsFull_core2_of_growHess quarGibbs_growHess

/-- the unconditional converse of Prop. 3.3.17 for `μ ∝ e^{-x⁴/4 - x²/2}` with `ρ = 1`. -/
theorem quarGibbs_mem_domain_of_Γ₂ {f : ℝ → ℝ} (hf : f ∈ quarGibbs.gibbsFull_unconditional.A)
    (hf2 : MemLp f 2 quarGibbs.μ)
    (hG : Integrable (FullTriple.G quarGibbs.gibbsFull_unconditional f f) quarGibbs.μ)
    (hG2 : Integrable (quarGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) quarGibbs.μ) :
    ∃ hF : hf2.toLp f ∈ quarGibbs.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((quarGibbs.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 quarGibbs.μ) : ℝ → ℝ) =ᵐ[quarGibbs.μ] quarGibbs.gibbsFull_unconditional.L f :=
  quarGibbs.gibbs_mem_domain_of_Γ₂_growHess quarGibbs_growHess quarGibbs_convex hf hf2 hG hG2

end MarkovTriple.BGL.Instances.Gibbs
