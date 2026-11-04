import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2PolyMain
import MarkovTriple.BGL.Instances.Gibbs.Core2WExample

/-!
# Non-vacuity of `PolyHess` outside `GrowHess`, with `ρ > 0` (R19, Stream A4, target D7)

`V(x) = exp(x²)`: `V' = 2x e^{x²}`, `V'' = (2 + 4x²) e^{x²} ≥ 2` (so `CD(2, ∞)`, `ρ = 2 > 0`), `V''' = (12x + 8x³) e^{x²}`.
It satisfies `PolyHess` (`V'' ≥ 0`; `V'' = o(V'²)`; `|V'''| ≤ 60 (1 + V'²)`) but NOT `GrowHess` (`V'' / V' = (1 + 2x⁻²) x → ∞`), so
the Round 18 theorem does not apply and the Round 19 theorem does.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.Gibbs

/-- `V(x) = exp(x²)`. -/
noncomputable def expV : ℝ → ℝ := fun x => Real.exp (x ^ 2)

lemma hasDerivAt_expV (x : ℝ) : HasDerivAt expV (2 * x * Real.exp (x ^ 2)) x := by
  have := (Real.hasDerivAt_exp (x ^ 2)).comp x (hasDerivAt_pow 2 x)
  refine this.congr_deriv ?_
  simp; ring

lemma deriv_expV : deriv expV = fun x => 2 * x * Real.exp (x ^ 2) :=
  funext fun x => (hasDerivAt_expV x).deriv

lemma hasDerivAt_dexpV (x : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y * Real.exp (y ^ 2)) ((2 + 4 * x ^ 2) * Real.exp (x ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by simpa using (hasDerivAt_id x).const_mul 2
  have h2 := (Real.hasDerivAt_exp (x ^ 2)).comp x (hasDerivAt_pow 2 x)
  refine (h1.mul h2).congr_deriv ?_
  simp; ring

lemma deriv_deriv_expV : deriv (deriv expV) = fun x => (2 + 4 * x ^ 2) * Real.exp (x ^ 2) := by
  rw [deriv_expV]; exact funext fun x => (hasDerivAt_dexpV x).deriv

lemma hasDerivAt_ddexpV (x : ℝ) :
    HasDerivAt (fun y : ℝ => (2 + 4 * y ^ 2) * Real.exp (y ^ 2))
      ((12 * x + 8 * x ^ 3) * Real.exp (x ^ 2)) x := by
  have h1 : HasDerivAt (fun y : ℝ => 2 + 4 * y ^ 2) (8 * x) x := by
    have := ((hasDerivAt_pow 2 x).const_mul 4).const_add 2
    refine this.congr_deriv ?_
    simp; ring
  have h2 := (Real.hasDerivAt_exp (x ^ 2)).comp x (hasDerivAt_pow 2 x)
  refine (h1.mul h2).congr_deriv ?_
  simp; ring

lemma deriv3_expV : deriv (deriv (deriv expV)) = fun x => (12 * x + 8 * x ^ 3) * Real.exp (x ^ 2) := by
  rw [deriv_deriv_expV]; exact funext fun x => (hasDerivAt_ddexpV x).deriv

lemma expV_smooth : Sm expV :=
  Real.contDiff_exp.comp (contDiff_id.pow 2)

lemma expV_integrable : Integrable (fun x => Real.exp (-expV x)) := by
  have hI : Integrable (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) :=
    integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 2)
  refine hI.mono' (Real.continuous_exp.comp expV_smooth.continuous.neg).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine Real.exp_le_exp.2 ?_
  unfold expV
  nlinarith [Real.add_one_le_exp (x ^ 2), sq_nonneg x]

/-- the Gibbs data `e^{-e^{x²}}`. -/
noncomputable def expGibbs : GibbsData where
  V := expV
  smooth := expV_smooth
  integrable := expV_integrable

lemma expE_ge (x : ℝ) : 1 + x ^ 2 ≤ Real.exp (x ^ 2) := by
  have := Real.add_one_le_exp (x ^ 2)
  linarith

/-- uniform convexity: `V'' ≥ 2`, i.e. `ρ = 2 > 0` (`CD(2, ∞)`). -/
theorem expGibbs_convex : ∀ x, (2 : ℝ) ≤ deriv (deriv expGibbs.V) x := fun x => by
  show (2 : ℝ) ≤ deriv (deriv expV) x
  rw [deriv_deriv_expV]
  have h := expE_ge x
  nlinarith [sq_nonneg x, mul_nonneg (sq_nonneg x) (sq_nonneg x)]

/-- `V'' = o(V'²)`. -/
theorem expGibbs_sub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
    ∀ x, deriv (deriv expGibbs.V) x ≤ ε * deriv expGibbs.V x ^ 2 + B := by
  intro ε hε
  set M : ℝ := max 1 (3 / (2 * ε)) with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM2 : 3 / (2 * ε) ≤ M := le_max_right _ _
  refine ⟨(2 + 4 * M) * Real.exp M, by positivity, fun x => ?_⟩
  show deriv (deriv expV) x ≤ ε * deriv expV x ^ 2 + _
  rw [deriv_deriv_expV, deriv_expV]
  simp only
  have hE := expE_ge x
  have hEpos : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  rcases le_or_gt M (x ^ 2) with h | h
  · have h3 : 3 / (2 * ε) ≤ Real.exp (x ^ 2) := by linarith
    have h4 : 3 ≤ Real.exp (x ^ 2) * (2 * ε) := (div_le_iff₀ (by positivity)).1 h3
    have h5 : 3 / 2 ≤ ε * Real.exp (x ^ 2) := by linarith
    have h6 := mul_le_mul_of_nonneg_left h5 (by positivity : 0 ≤ 4 * x ^ 2 * Real.exp (x ^ 2))
    have h7 : 0 ≤ (x ^ 2 - 1) * Real.exp (x ^ 2) := mul_nonneg (by linarith) hEpos.le
    have h8 : 0 ≤ (2 + 4 * M) * Real.exp M := by positivity
    nlinarith [h6, h7, h8]
  · have h9 : Real.exp (x ^ 2) ≤ Real.exp M := Real.exp_le_exp.2 h.le
    have h10 : (2 + 4 * x ^ 2) * Real.exp (x ^ 2) ≤ (2 + 4 * M) * Real.exp M :=
      mul_le_mul (by linarith) h9 hEpos.le (by positivity)
    nlinarith [sq_nonneg (2 * x * Real.exp (x ^ 2)), mul_nonneg hε.le (sq_nonneg (2 * x * Real.exp (x ^ 2)))]

/-- `|V'''| ≤ 60 (1 + |V'|²)`. -/
theorem expGibbs_third : ∃ C : ℝ, ∃ N : ℕ, ∀ x,
    |deriv (deriv (deriv expGibbs.V)) x| ≤ C * (1 + |deriv expGibbs.V x| ^ N) := by
  refine ⟨60, 2, fun x => ?_⟩
  show |deriv (deriv (deriv expV)) x| ≤ 60 * (1 + |deriv expV x| ^ 2)
  rw [deriv3_expV, deriv_expV]
  simp only
  rw [sq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hE := expE_ge x
  have hEpos : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  have hax := abs_nonneg x
  have hx2 : |x| ^ 2 = x ^ 2 := sq_abs x
  have hxE : |x| ≤ Real.exp (x ^ 2) := by nlinarith [sq_nonneg (|x| - 1)]
  have hpoly : |12 * x + 8 * x ^ 3| ≤ 12 * |x| + 8 * |x| ^ 3 := by
    calc |12 * x + 8 * x ^ 3| ≤ |12 * x| + |8 * x ^ 3| := abs_add_le _ _
      _ = 12 * |x| + 8 * |x| ^ 3 := by
        rw [abs_mul, abs_mul, abs_pow]; norm_num
  rcases le_or_gt 1 |x| with h | h
  · have h1 : 12 * |x| + 8 * |x| ^ 3 ≤ 20 * |x| ^ 3 := by nlinarith [mul_nonneg hax (sq_nonneg (|x| - 1))]
    have h2 : |x| ^ 3 * Real.exp (x ^ 2) ≤ x ^ 2 * Real.exp (x ^ 2) ^ 2 := by
      have : |x| ^ 3 * Real.exp (x ^ 2) = x ^ 2 * (|x| * Real.exp (x ^ 2)) := by rw [← hx2]; ring
      rw [this]
      have := mul_le_mul_of_nonneg_right hxE hEpos.le
      nlinarith [this, sq_nonneg x]
    have h3 := mul_le_mul_of_nonneg_right (hpoly.trans h1) hEpos.le
    nlinarith [h2, h3, mul_nonneg (sq_nonneg x) (sq_nonneg (Real.exp (x ^ 2)))]
  · have hx : x ^ 2 < 1 := by nlinarith
    have hEle : Real.exp (x ^ 2) ≤ 3 := by
      have h1 : Real.exp (x ^ 2) ≤ Real.exp 1 := Real.exp_le_exp.2 hx.le
      have := Real.exp_one_lt_d9
      linarith
    have h1 : 12 * |x| + 8 * |x| ^ 3 ≤ 20 := by nlinarith [mul_nonneg hax hax, mul_nonneg hax (mul_nonneg hax hax)]
    have h3 := mul_le_mul (hpoly.trans h1) hEle hEpos.le (by norm_num)
    nlinarith [h3, mul_nonneg (sq_nonneg x) (sq_nonneg (Real.exp (x ^ 2)))]

/-- **D7**: `V = exp(x²)` satisfies `PolyHess`. -/
theorem expGibbs_polyHess : expGibbs.PolyHess := by
  refine ⟨⟨0, le_refl _, fun x => ?_⟩, expGibbs_sub, expGibbs_third⟩
  have := expGibbs_convex x
  simp only [zero_mul, neg_zero]
  linarith

/-- `expGibbs` is OUTSIDE `GrowHess`: `V''/V' ~ 2x` is unbounded. -/
theorem expGibbs_not_growHess : ¬ expGibbs.GrowHess := by
  rintro ⟨C, hC⟩
  have h := (hC (|C| + 2)).1
  change |deriv (deriv expV) (|C| + 2)| ≤ C * (1 + |deriv expV (|C| + 2)|) at h
  rw [deriv_deriv_expV, deriv_expV] at h
  simp only at h
  set x : ℝ := |C| + 2 with hx
  have hC0 := abs_nonneg C
  have hCa := le_abs_self C
  have hx2 : 2 ≤ x := by rw [hx]; linarith
  have hE := expE_ge x
  have hEpos : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  have hE1 : 1 ≤ Real.exp (x ^ 2) := by nlinarith [sq_nonneg x]
  rw [abs_of_pos (by positivity : 0 < (2 + 4 * x ^ 2) * Real.exp (x ^ 2)),
    abs_of_pos (by positivity : 0 < 2 * x * Real.exp (x ^ 2))] at h
  have hxE : 0 < x * Real.exp (x ^ 2) := by positivity
  have h1 : 1 ≤ x * Real.exp (x ^ 2) := by nlinarith
  have h2 : C * (1 + 2 * x * Real.exp (x ^ 2)) ≤ |C| * (3 * (x * Real.exp (x ^ 2))) := by
    have : 1 + 2 * x * Real.exp (x ^ 2) ≤ 3 * (x * Real.exp (x ^ 2)) := by nlinarith
    calc C * (1 + 2 * x * Real.exp (x ^ 2)) ≤ |C| * (1 + 2 * x * Real.exp (x ^ 2)) :=
          mul_le_mul_of_nonneg_right hCa (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left this hC0
  have h3 : (4 * x) * (x * Real.exp (x ^ 2)) ≤ (3 * |C|) * (x * Real.exp (x ^ 2)) := by
    nlinarith [mul_nonneg (sq_nonneg x) hEpos.le]
  have h4 := le_of_mul_le_mul_right h3 hxE
  rw [hx] at h4
  linarith

/-- **`Core2` for `V = exp(x²)`** (`ρ = 2`; `V'' / V'` unbounded, so `GrowHess` fails: new in Round 19). -/
theorem expGibbs_core2 : expGibbs.gibbsFull_unconditional.Core2 :=
  expGibbs.gibbsFull_core2_of_polyHess expGibbs_polyHess

/-- the unconditional converse of Prop. 3.3.17 for `μ ∝ e^{-e^{x²}}` with `ρ = 2`. -/
theorem expGibbs_mem_domain_of_Γ₂ {f : ℝ → ℝ} (hf : f ∈ expGibbs.gibbsFull_unconditional.A)
    (hf2 : MemLp f 2 expGibbs.μ)
    (hG : Integrable (FullTriple.G expGibbs.gibbsFull_unconditional f f) expGibbs.μ)
    (hG2 : Integrable (expGibbs.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) expGibbs.μ) :
    ∃ hF : hf2.toLp f ∈ expGibbs.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((expGibbs.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ :
        Lp ℝ 2 expGibbs.μ) : ℝ → ℝ) =ᵐ[expGibbs.μ] expGibbs.gibbsFull_unconditional.L f :=
  expGibbs.gibbs_mem_domain_of_Γ₂_polyHess expGibbs_polyHess expGibbs_convex hf hf2 hG hG2

end MarkovTriple.BGL.Instances.Gibbs
