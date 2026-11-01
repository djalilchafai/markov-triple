import Mathlib
import MarkovTriple.Frozen.MarkovTriple
/-! # Round-3 audit (G2): the polynomial-growth test class for Ornstein–Uhlenbeck is INCOMPATIBLE with
the frozen `MarkovTriple` (`comp_mem` for all smooth `ψ`, `ψ 0 = 0`, together with `memLp`).

Theorem `no_identity_in_A0_gaussian`: for ANY `T : MarkovTriple ℝ` with `T.μ = N(0,1)`, the identity
function is not in `T.A₀` (so polynomials ⊄ `T.A₀`).  Witness: `ψ(z) = exp(z²) − 1`, `ψ(0) = 0`;
`ψ(x) ∉ L¹(N(0,1))` since `exp(x²)·exp(−x²/2)` is not integrable. -/
open MeasureTheory ProbabilityTheory
namespace Frozen3Audit

/-- `exp(x²) − 1` is not `N(0,1)`-integrable. -/
lemma not_integrable_expsq : ¬ Integrable (fun x : ℝ => Real.exp (x ^ 2) - 1) (gaussianReal 0 1) := by
  intro h
  have h1 : Integrable (fun x : ℝ => Real.exp (x ^ 2)) (gaussianReal 0 1) :=
    (h.add (integrable_const (1 : ℝ))).congr (Filter.Eventually.of_forall fun x => by simp)
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : NNReal) ≠ 0)] at h1
  change Integrable _ ((volume : Measure ℝ).withDensity fun x => ENNReal.ofReal (gaussianPDFReal 0 1 x)) at h1
  rw [integrable_withDensity_iff_integrable_smul' (by fun_prop) (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)] at h1
  have h2 : Integrable (fun x : ℝ => Real.exp (x ^ 2 / 2) / Real.sqrt (2 * Real.pi)) := by
    refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, smul_eq_mul, ENNReal.toReal_ofReal]
    have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    rw [ENNReal.toReal_ofReal (by positivity), mul_assoc, ← Real.exp_add]
    have : -(x - 0) ^ 2 / 2 + x ^ 2 = x ^ 2 / 2 := by ring
    rw [this]; field_simp
  have h3 : Integrable (fun _ : ℝ => (Real.sqrt (2 * Real.pi))⁻¹) := by
    refine h2.mono' aestronglyMeasurable_const (Filter.Eventually.of_forall fun x => ?_)
    have hp : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hp), div_eq_mul_inv]
    have : 1 ≤ Real.exp (x ^ 2 / 2) := Real.one_le_exp (by positivity)
    nlinarith [inv_pos.2 hp]
  rw [integrable_const_iff] at h3
  rcases h3 with h3 | h3
  · exact (inv_pos.2 (Real.sqrt_pos.2 (by positivity : (0:ℝ) < 2 * Real.pi))).ne' h3
  · have := h3.measure_univ_lt_top
    rw [Real.volume_univ] at this; exact absurd this (by simp)

open MarkovTriple in
/-- no `MarkovTriple` over `N(0,1)` has the identity (hence any polynomial of degree ≥ 1) in `A₀`. -/
theorem no_identity_in_A0_gaussian (T : MarkovTriple ℝ) (hμ : T.μ = gaussianReal 0 1) :
    (id : ℝ → ℝ) ∉ T.A₀ := by
  intro hid
  let ψ : (Fin 1 → ℝ) → ℝ := fun z => Real.exp (z 0 ^ 2) - 1
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := by
    have : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 1 → ℝ => z 0) := contDiff_apply ℝ ℝ 0
    exact (Real.contDiff_exp.comp (this.pow 2)).sub contDiff_const
  have h0 : ψ 0 = 0 := by simp [ψ]
  have hm := T.comp_mem 1 ψ hψ h0 (fun _ => id) (fun _ => hid)
  have hl := T.memLp _ hm 1 (by simp)
  rw [memLp_one_iff_integrable, hμ] at hl
  exact not_integrable_expsq hl
/-- On an infinite measure space the Markov clause `u =ᵐ 1 → P t u =ᵐ 1` of `IsSemigroupOf` is vacuous
(no `u ∈ L²` equals `1`): conservativeness is invisible to the frozen predicate for infinite `μ`. -/
theorem markov_clause_vacuous_lebesgue (u : Lp ℝ 2 (volume : Measure ℝ)) :
    ¬ ((u : ℝ → ℝ) =ᵐ[volume] (1 : ℝ → ℝ)) := by
  intro h
  have h1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 (volume : Measure ℝ) := (Lp.memLp u).ae_eq h
  rw [memLp_const_iff (by norm_num) (by norm_num)] at h1
  rcases h1 with h1 | h1
  · exact one_ne_zero h1
  · rw [Real.volume_univ] at h1; exact absurd h1 (by simp)

end Frozen3Audit
#print axioms Frozen3Audit.no_identity_in_A0_gaussian
#print axioms Frozen3Audit.markov_clause_vacuous_lebesgue
