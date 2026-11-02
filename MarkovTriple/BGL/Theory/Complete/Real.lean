import Mathlib
import MarkovTriple.BGL.Frozen.Complete
import MarkovTriple.BGL.Instances.Lebesgue.Cutoff

/-!
# Completeness (BGL Def. 3.3.9) of one-dimensional diffusion triples with `𝒜₀ ⊇ C_c^∞(ℝ)`

Real cutoffs: `ζ_k(x) = χ(x / (M (k+1)))` with `χ(x) = smoothTransition(2 - x²)` (`= 1` on `[-1,1]`,
compactly supported, radially nonincreasing) and `M ≥ max(1, ‖χ'‖_∞)`.  Then `ζ_k ∈ C_c^∞`, `0 ≤ ζ_k ≤ 1`,
`ζ_k ↑ 1` everywhere, and `ζ_k'² ≤ (M(k+1))⁻² ‖χ'‖²_∞ ≤ 1/(k+1)²`.

This applies to every `DiffusionTriple` on `ℝ` whose test algebra contains `C_c^∞` and whose carré du champ is
`Γ(f,f) = f'²` on it: in particular Lebesgue (`C_c^∞`, `μ` infinite) and OU (`C_c^∞`, `μ = γ` finite, but
`1 ∉ 𝒜₀`, so genuine cutoffs are needed).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Complete

open MarkovTriple.BGL.Lebesgue

/-- the cutoff scale `M ≥ max (1, ‖χ'‖_∞)`. -/
noncomputable def scaleM : ℝ := max 1 (Classical.choose chi_deriv_bound)

lemma scaleM_pos : 0 < scaleM := lt_of_lt_of_le one_pos (le_max_left _ _)

lemma chi_deriv_le (x : ℝ) : |deriv chi x| ≤ scaleM :=
  ((Classical.choose_spec chi_deriv_bound).2 x).trans (le_max_right _ _)

/-- `ζ_k = χ(· / (M (k+1)))`. -/
noncomputable def zeta (k : ℕ) : ℝ → ℝ := chiR (scaleM * ((k : ℝ) + 1))

lemma Rk_pos (k : ℕ) : 0 < scaleM * ((k : ℝ) + 1) := mul_pos scaleM_pos (by positivity)

lemma zeta_smooth (k : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (zeta k) := chiR_smooth _

lemma zeta_cs (k : ℕ) : HasCompactSupport (zeta k) := chiR_cs (Rk_pos k).ne'

lemma zeta_nonneg (k : ℕ) (x : ℝ) : 0 ≤ zeta k x := chi_nonneg _

lemma zeta_mono (k : ℕ) (x : ℝ) : zeta k x ≤ zeta (k + 1) x := by
  unfold zeta chiR chi
  apply Real.smoothTransition.monotone
  have hR := Rk_pos k
  have h1 : scaleM * ((k : ℝ) + 1) ≤ scaleM * (((k + 1 : ℕ) : ℝ) + 1) := by
    have := scaleM_pos
    push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h2 : (x / (scaleM * (((k + 1 : ℕ) : ℝ) + 1))) ^ 2 ≤ (x / (scaleM * ((k : ℝ) + 1))) ^ 2 := by
    rw [div_pow, div_pow]
    exact div_le_div_of_nonneg_left (sq_nonneg x) (by positivity)
      (pow_le_pow_left₀ hR.le h1 2)
  linarith

lemma zeta_tendsto (x : ℝ) : Tendsto (fun k => zeta k x) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (⌈|x|⌉₊)] with k hk
  symm
  apply chi_eq_one
  have hM := scaleM_pos
  have h1 : |x| ≤ (k : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hk)
  rw [abs_div, abs_of_pos (Rk_pos k), div_le_one (Rk_pos k)]
  have : (k : ℝ) ≤ scaleM * ((k : ℝ) + 1) := by
    have := le_max_left 1 (Classical.choose chi_deriv_bound)
    unfold scaleM
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  linarith

lemma zeta_deriv_sq_le (k : ℕ) (x : ℝ) : (deriv (zeta k) x) ^ 2 ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by
  unfold zeta
  rw [deriv_chiR]
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hM := scaleM_pos
  have h : |deriv chi (x / (scaleM * ((k : ℝ) + 1))) / (scaleM * ((k : ℝ) + 1))| ≤
      1 / ((k : ℝ) + 1) := by
    rw [abs_div, abs_of_pos (Rk_pos k), div_le_div_iff₀ (Rk_pos k) hk]
    have := chi_deriv_le (x / (scaleM * ((k : ℝ) + 1)))
    nlinarith
  exact sq_le_sq' (by linarith [abs_le.1 h]) (abs_le.1 h).2

/-- **Completeness from real cutoffs.** -/
theorem isComplete_of_real (D : DiffusionTriple ℝ)
    (hA : ∀ f : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f → f ∈ D.A₀)
    (hΓ : ∀ f ∈ D.A₀, D.Γ f f =ᵐ[D.μ] fun x => deriv f x * deriv f x) :
    D.IsComplete := by
  refine ⟨zeta, fun k => hA _ (zeta_smooth k) (zeta_cs k),
    fun k => Eventually.of_forall (zeta_nonneg k), fun k => Eventually.of_forall (zeta_mono k),
    Eventually.of_forall zeta_tendsto, fun k => ?_⟩
  filter_upwards [hΓ _ (hA _ (zeta_smooth k) (zeta_cs k))] with x hx
  rw [hx]
  nlinarith [zeta_deriv_sq_le k x]

end MarkovTriple.BGL.Complete
