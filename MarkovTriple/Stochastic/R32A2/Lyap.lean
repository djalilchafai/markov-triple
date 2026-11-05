import Mathlib
import MarkovTriple.Stochastic.R32A2.Comp
import MarkovTriple.Stochastic.R31X.Cutoff

/-!
# Round 32 (A2), part 2: decay at infinity from a Lyapunov family on `ℝ^d`

See `STATEMENTS_R32_A2.md`.  `h > 0` continuous with `h → 0` at infinity, approximated from below by test functions `u_n ∈ 𝒜₀`
(`u_n = h` on `|y| ≤ n`) with `L u_n ≤ λ u_n + ε_n`, `ε_n → 0`.  The comparison principle gives `P_t φ_K ≤ m⁻¹ e^{λt} h` a.e.
for a cut-off `φ_K ≤ m⁻¹ u_n`, hence everywhere for the continuous representative; with `rd_isFellerC0_iff_cutoff` this is `IsFellerC0`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R32A2

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R30T MarkovTriple.Stochastic.R31X

variable {d : ℕ} (S : FullTriple (Rd d)) [IsFiniteMeasure S.toDiffusionTriple.μ]
  [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ] [S.toDiffusionTriple.μ.IsOpenPosMeasure]

theorem rd_isFellerC0_of_lyapunov (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d)
    {lam : ℝ} (hlam : 0 < lam) (h : Rd d → ℝ) (hh : Continuous h) (hpos : ∀ y, 0 < h y)
    (hdec : Tendsto h (cocompact (Rd d)) (𝓝 0)) (u : ℕ → Rd d → ℝ) (hu : ∀ n, u n ∈ A₀ d)
    (hu0 : ∀ n y, 0 ≤ u n y ∧ u n y ≤ h y) (hue : ∀ (n : ℕ) y, ‖y‖ ≤ n → u n y = h y)
    (ε : ℕ → ℝ) (hεpos : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hL : ∀ n x, S.toDiffusionTriple.L (u n) x ≤ lam * u n x + ε n) :
    IsFellerC0 S.toDiffusionTriple := by
  set D := S.toDiffusionTriple with hD
  rw [rd_isFellerC0_iff_cutoff S hA hA₀]
  intro t K hK
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall (0 : Rd d)
  set R : ℝ := max R0 0 with hRdef
  have hR : K ⊆ Metric.closedBall (0 : Rd d) R :=
    hR0.trans (Metric.closedBall_subset_closedBall (le_max_left _ _))
  have hR0' : 0 ≤ R := le_max_right _ _
  refine ⟨cutoffCc R, cutoffCc_mem R, fun y hy => cutoffCc_one R y ?_, fun g hg => ?_⟩
  · simpa [Metric.mem_closedBall, dist_zero_right] using hR hy
  -- a positive lower bound of `h` on the ball `closedBall 0 (R+1)`
  obtain ⟨y0, hy0m, hy0⟩ := (isCompact_closedBall (0 : Rd d) (R + 1)).exists_isMinOn
    ⟨0, by simp; linarith⟩ hh.continuousOn
  set m : ℝ := h y0 with hmdef
  have hmpos : 0 < m := hpos y0
  have hm : ∀ y, ‖y‖ ≤ R + 1 → m ≤ h y := fun y hy =>
    hy0 (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
  obtain ⟨N, hN⟩ := exists_nat_ge (R + 1)
  set c : ℝ := (Real.exp (lam * t) - 1) / lam with hc
  -- nonnegativity of `g`
  have hg0 : ∀ x, 0 ≤ g x := by
    have h0 : 0 ≤ᵐ[D.μ] (D.semigroup t (ccL2 D (cutoffCc R)) : Rd d → ℝ) :=
      D.semigroup_nonneg t (ccL2_nonneg (T := D) fun y => (cutoffCc_mem R y).1)
    have h1 : (fun _ : Rd d => (0 : ℝ)) ≤ᵐ[D.μ] g := by
      filter_upwards [h0, hg] with x h1 h2
      rw [← h2]; exact h1
    exact fun x => le_of_ae_le_cont S continuous_const g.continuous h1 x
  -- upper bound for `n ≥ N`
  have hub : ∀ n, N ≤ n → ∀ x, g x ≤ m⁻¹ * (Real.exp (lam * t) * h x + ε n * c) := by
    intro n hn x
    set f : D.A₀ := ⟨u n, hA₀ ▸ hu n⟩ with hf
    have hle : (ccL2 D (cutoffCc R) : Rd d → ℝ) ≤ᵐ[D.μ] ((m⁻¹ • D.cls f : Lp ℝ 2 D.μ) : Rd d → ℝ) := by
      filter_upwards [coeFn_ccL2 (T := D) (cutoffCc R), Lp.coeFn_smul m⁻¹ (D.cls f),
        DiffusionTriple.coeFn_cls D f] with y h1 h2 h3
      rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul]
      have hu1 : 0 ≤ u n y := (hu0 n y).1
      by_cases hy : ‖y‖ ≤ R + 1
      · have hnn : ‖y‖ ≤ n := hy.trans (hN.trans (by exact_mod_cast hn))
        have e : (f : Rd d → ℝ) y = h y := hue n y hnn
        rw [e, cutoffCc_apply]
        have := hm y hy
        refine (max_le zero_le_one (min_le_left _ _)).trans ?_
        rw [← div_eq_inv_mul, le_div_iff₀ hmpos]; linarith
      · rw [cutoffCc_apply, max_eq_left (by
          have : R + 1 < ‖y‖ := not_le.1 hy
          exact (min_le_right _ _).trans (by linarith))]
        exact mul_nonneg (inv_nonneg.2 hmpos.le) hu1
    have hmono := D.semigroup_mono t hle
    have hcmp := semigroup_comparison D f hlam (hεpos n) (Filter.Eventually.of_forall (hL n)) t
    have e1 : D.semigroup t (m⁻¹ • D.cls f) = m⁻¹ • D.semigroup t (D.cls f) := map_smul _ _ _
    rw [e1] at hmono
    have hae : g ≤ᵐ[D.μ] fun x => m⁻¹ * (Real.exp (lam * t) * h x + ε n * c) := by
      filter_upwards [hmono, Lp.coeFn_smul m⁻¹ (D.semigroup t (D.cls f)), hcmp, hg,
        (Filter.Eventually.of_forall fun x => (hu0 n x).2 : ∀ᵐ x ∂D.μ, u n x ≤ h x)] with y h1 h2 h3 h4 h5
      rw [h2, Pi.smul_apply, smul_eq_mul] at h1
      rw [← h4]
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 hmpos.le))
      have : Real.exp (lam * t) * (f : Rd d → ℝ) y ≤ Real.exp (lam * t) * h y :=
        mul_le_mul_of_nonneg_left h5 (Real.exp_pos _).le
      have h3' := h3
      simp only [hc] at h3' ⊢
      linarith
    exact le_of_ae_le_cont S (u := g) (v := fun x => m⁻¹ * (Real.exp (lam * t) * h x + ε n * c))
      g.continuous (by fun_prop) hae x
  have hlim : ∀ x, g x ≤ m⁻¹ * (Real.exp (lam * t) * h x) := by
    intro x
    have hT : Tendsto (fun n => m⁻¹ * (Real.exp (lam * t) * h x + ε n * c)) atTop
        (𝓝 (m⁻¹ * (Real.exp (lam * t) * h x + 0 * c))) :=
      tendsto_const_nhds.mul (tendsto_const_nhds.add (hε0.mul_const c))
    rw [zero_mul, add_zero] at hT
    exact ge_of_tendsto hT (eventually_atTop.2 ⟨N, fun n hn => hub n hn x⟩)
  have hdec' : Tendsto (fun x => m⁻¹ * (Real.exp (lam * t) * h x)) (cocompact (Rd d)) (𝓝 0) := by
    have := (hdec.const_mul (Real.exp (lam * t))).const_mul m⁻¹
    simpa using this
  exact squeeze_zero hg0 hlim hdec'

end MarkovTriple.Stochastic.R32A2
