import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2Main

/-!
# Non-vacuity of `BddJet` (R17, Stream A, target A5)

`V(x) = √(1 + x²)` (the hyperbolic / Laplace-type potential, `e^{-V} ~ e^{-|x|}`) is a `GibbsData` with bounded
`V', V'', V'''`: `|V'| ≤ 1`, `0 < V'' = (1+x²)^{-3/2} ≤ 1`, `|V'''| = 3|x|(1+x²)^{-5/2} ≤ 3`.  So
`gibbsFull_core2` / `gibbs_mem_domain_of_Γ₂` apply to a genuine non-compact, non-Gaussian example.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.Gibbs

/-- `V(x) = √(1 + x²)`. -/
noncomputable def sqrtV : ℝ → ℝ := fun x => Real.sqrt (1 + x ^ 2)

lemma one_le_sqrtV (x : ℝ) : 1 ≤ sqrtV x := by
  unfold sqrtV
  exact (Real.le_sqrt' one_pos).2 (by nlinarith [sq_nonneg x])

lemma sqrtV_sq (x : ℝ) : sqrtV x ^ 2 = 1 + x ^ 2 := by
  unfold sqrtV
  exact Real.sq_sqrt (by positivity)

lemma abs_le_sqrtV (x : ℝ) : |x| ≤ sqrtV x := by
  unfold sqrtV
  exact Real.abs_le_sqrt (by nlinarith [sq_nonneg x])

lemma hasDerivAt_sqrtV (x : ℝ) : HasDerivAt sqrtV (x / sqrtV x) x := by
  have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have h2 := h1.sqrt (by positivity)
  refine h2.congr_deriv ?_
  have : sqrtV x ≠ 0 := by have := one_le_sqrtV x; positivity
  show 2 * x / (2 * sqrtV x) = x / sqrtV x
  field_simp

lemma deriv_sqrtV : deriv sqrtV = fun x => x / sqrtV x := funext fun x => (hasDerivAt_sqrtV x).deriv

lemma hasDerivAt_dV (x : ℝ) : HasDerivAt (fun y => y / sqrtV y) ((sqrtV x ^ 3)⁻¹) x := by
  have h := (hasDerivAt_id x).div (hasDerivAt_sqrtV x) (by have := one_le_sqrtV x; positivity)
  refine h.congr_deriv ?_
  have hs : sqrtV x ≠ 0 := by have := one_le_sqrtV x; positivity
  have h2 := sqrtV_sq x
  simp only [id]
  field_simp
  nlinarith [h2]

lemma deriv_deriv_sqrtV : deriv (deriv sqrtV) = fun x => (sqrtV x ^ 3)⁻¹ := by
  rw [deriv_sqrtV]; exact funext fun x => (hasDerivAt_dV x).deriv

lemma hasDerivAt_ddV (x : ℝ) : HasDerivAt (fun y => (sqrtV y ^ 3)⁻¹) (-(3 * x) / sqrtV x ^ 5) x := by
  have hs : sqrtV x ≠ 0 := by have := one_le_sqrtV x; positivity
  have h3 : HasDerivAt (fun y => sqrtV y ^ 3) (3 * sqrtV x ^ 2 * (x / sqrtV x)) x := by
    simpa using (hasDerivAt_sqrtV x).fun_pow 3
  have h := h3.inv (pow_ne_zero 3 hs)
  refine h.congr_deriv ?_
  field_simp

lemma deriv3_sqrtV : deriv (deriv (deriv sqrtV)) = fun x => -(3 * x) / sqrtV x ^ 5 := by
  rw [deriv_deriv_sqrtV]; exact funext fun x => (hasDerivAt_ddV x).deriv

lemma sqrtV_smooth : Sm sqrtV :=
  (contDiff_const.add (contDiff_id.pow 2)).sqrt (fun x => by positivity)

lemma sqrtV_integrable : Integrable (fun x => Real.exp (-sqrtV x)) := by
  have hI := (integrable_inv_one_add_sq).const_mul 2
  refine hI.mono' (Real.continuous_exp.comp sqrtV_smooth.continuous.neg).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hs := one_le_sqrtV x
  have h2 := sqrtV_sq x
  have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ sqrtV x by linarith)
  rw [Real.exp_neg]
  have hpos : 0 < 1 + x ^ 2 := by positivity
  have : (1 + x ^ 2) / 2 ≤ Real.exp (sqrtV x) := by nlinarith [sq_nonneg (sqrtV x)]
  calc (Real.exp (sqrtV x))⁻¹ ≤ ((1 + x ^ 2) / 2)⁻¹ :=
        inv_anti₀ (by positivity) this
    _ = 2 * (1 + x ^ 2)⁻¹ := by field_simp

/-- the Gibbs data `e^{-√(1+x²)}`. -/
noncomputable def sqrtGibbs : GibbsData where
  V := sqrtV
  smooth := sqrtV_smooth
  integrable := sqrtV_integrable

/-- **A5 (non-vacuity)**: `√(1+x²)` has bounded `V', V'', V'''`. -/
theorem sqrtGibbs_bddJet : sqrtGibbs.BddJet := by
  refine ⟨⟨1, fun x => ?_⟩, ⟨1, fun x => ?_⟩, ⟨3, fun x => ?_⟩⟩
  · show |deriv sqrtV x| ≤ 1
    rw [deriv_sqrtV]
    have hs := one_le_sqrtV x
    rw [abs_div, abs_of_pos (by linarith : 0 < sqrtV x), div_le_one (by linarith)]
    exact abs_le_sqrtV x
  · show |deriv (deriv sqrtV) x| ≤ 1
    rw [deriv_deriv_sqrtV]
    have hs := one_le_sqrtV x
    have : 1 ≤ sqrtV x ^ 3 := one_le_pow₀ hs
    rw [abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ this
  · show |deriv (deriv (deriv sqrtV)) x| ≤ 3
    rw [deriv3_sqrtV]
    have hs := one_le_sqrtV x
    have hx := abs_le_sqrtV x
    have h5 : 0 < sqrtV x ^ 5 := by positivity
    rw [abs_div, abs_neg, abs_mul, abs_of_pos h5, abs_of_pos (by norm_num : (0 : ℝ) < 3), div_le_iff₀ h5]
    have : sqrtV x ≤ sqrtV x ^ 5 := by
      calc sqrtV x = sqrtV x ^ 1 := (pow_one _).symm
        _ ≤ sqrtV x ^ 5 := pow_le_pow_right₀ hs (by norm_num)
    nlinarith

/-- the bounded-jet unconditional converse applies to `e^{-√(1+x²)}dx`. -/
theorem sqrtGibbs_core2 : sqrtGibbs.gibbsFull_unconditional.Core2 :=
  sqrtGibbs.gibbsFull_core2 sqrtGibbs_bddJet

end MarkovTriple.BGL.Instances.Gibbs
