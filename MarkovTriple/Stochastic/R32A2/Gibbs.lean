import Mathlib
import MarkovTriple.Stochastic.R32A2.Cut
import MarkovTriple.Stochastic.R31U.Instances
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdExample

/-!
# Round 32 (A2), part 5: `IsFellerC0` for the Gibbs semigroup on `ℝ^d` under linear growth of `∇V`

See `STATEMENTS_R32_A2.md`.  `u_R = cut_R · h` satisfies `L u_R ≤ λ u_R + (K + 12 d K)/(1+R⁴)`; with `R_n = (n+1)(d+1)` this feeds
`rd_isFellerC0_of_lyapunov`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.Stochastic.R32A2

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R30T MarkovTriple.Stochastic.R31X MarkovTriple.Stochastic.R31U

variable {d : ℕ}

/-- the truncated Lyapunov function `cut_R · h ∈ C_c^∞` -/
noncomputable def uR (R : ℝ) : Rd d → ℝ := fun y => cut R y * hL y

lemma uR_eq (R : ℝ) : (uR R : Rd d → ℝ) = (cut R : Rd d → ℝ) * hL := rfl

lemma Lr_cutmul_le (G : GibbsRdData d) {lam K : ℝ} (hlam : ∀ y, Lr G.V hL y ≤ lam * hL y) (hK0 : 0 ≤ K)
    (hK : ∀ R : ℝ, 1 ≤ R → ∀ y : Rd d, |Lr G.V (cut R) y| ≤ K ∧ ∀ i, |pderiv (cut R) i y| ≤ K)
    {R : ℝ} (hR : 1 ≤ R) (y : Rd d) :
    Lr G.V (uR R) y ≤ lam * uR R y + (K + 12 * d * K) / (1 + R ^ 4) := by
  have hR0 : 0 < R := by linarith
  have hu : uR R y = cut R y * hL y := rfl
  rw [hu, uR_eq, Lr_mul (sm_cut R) sm_hL]
  have hc0 := cut_nonneg R y
  have hh0 := hL_pos y
  have hmain : cut R y * Lr G.V hL y ≤ lam * (cut R y * hL y) := by
    calc cut R y * Lr G.V hL y ≤ cut R y * (lam * hL y) := mul_le_mul_of_nonneg_left (hlam y) hc0
      _ = lam * (cut R y * hL y) := by ring
  have hE0 : 0 ≤ (K + 12 * d * K) / (1 + R ^ 4) := by positivity
  by_cases hy : qd y < R ^ 2
  · obtain ⟨h1, h2⟩ := cut_vanish' G hR0 hy
    have hG : Gr (cut R) hL y = 0 := by
      unfold Gr; simp [h1]
    rw [h2, hG]
    nlinarith
  · push Not at hy
    have hq := qd_nonneg y
    have hh : hL y ≤ 1 / (1 + R ^ 4) := by
      unfold hL phi
      rw [one_div]
      refine inv_anti₀ (by positivity) ?_
      have : R ^ 4 ≤ qd y ^ 2 := by
        have : (R ^ 2) ^ 2 ≤ qd y ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
        nlinarith
      linarith
    obtain ⟨hKL, hKg⟩ := hK R hR y
    have hGr : Gr (cut R) hL y ≤ d * (K * (6 * hL y)) := by
      unfold Gr
      calc ∑ i, pderiv (cut R) i y * pderiv hL i y ≤ ∑ _i : Fin d, K * (6 * hL y) := by
            refine Finset.sum_le_sum fun i _ => ?_
            calc pderiv (cut R) i y * pderiv hL i y ≤ |pderiv (cut R) i y * pderiv hL i y| := le_abs_self _
              _ = |pderiv (cut R) i y| * |pderiv hL i y| := abs_mul _ _
              _ ≤ K * (6 * hL y) := mul_le_mul (hKg i) (abs_pderiv_hL i y) (abs_nonneg _) hK0
        _ = d * (K * (6 * hL y)) := by simp
    have hLc : hL y * Lr G.V (cut R) y ≤ hL y * K :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans hKL) hh0.le
    have hfin : hL y * K + 2 * (d * (K * (6 * hL y))) ≤ (K + 12 * d * K) / (1 + R ^ 4) := by
      have : hL y * K + 2 * (d * (K * (6 * hL y))) = (K + 12 * d * K) * hL y := by ring
      rw [this]
      calc (K + 12 * d * K) * hL y ≤ (K + 12 * d * K) * (1 / (1 + R ^ 4)) :=
            mul_le_mul_of_nonneg_left hh (by positivity)
        _ = _ := by ring
    linarith

lemma norm_sq_le_qd (y : Rd d) : ‖y‖ ^ 2 ≤ qd y := by
  have h : ‖y‖ ≤ Real.sqrt (qd y) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs]
    exact Real.abs_le_sqrt (sq_le_qd i y)
  exact (Real.le_sqrt (norm_nonneg _) (qd_nonneg y)).1 h

lemma qd_le_norm_sq (y : Rd d) : qd y ≤ d * ‖y‖ ^ 2 := by
  unfold qd
  calc ∑ i, y i ^ 2 ≤ ∑ _i : Fin d, ‖y‖ ^ 2 := by
        refine Finset.sum_le_sum fun i _ => ?_
        have := norm_le_pi_norm y i
        rw [Real.norm_eq_abs] at this
        calc y i ^ 2 = |y i| ^ 2 := (sq_abs _).symm
          _ ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    _ = d * ‖y‖ ^ 2 := by simp

lemma hL_tendsto : Tendsto (hL : Rd d → ℝ) (cocompact (Rd d)) (𝓝 0) := by
  have h1 : Tendsto (fun y : Rd d => 1 + ‖y‖ ^ 4) (cocompact (Rd d)) atTop :=
    tendsto_atTop_add_const_left _ _ ((tendsto_pow_atTop (by norm_num : 4 ≠ 0)).comp tendsto_norm_cocompact_atTop)
  have h2 : Tendsto (fun y : Rd d => (1 + ‖y‖ ^ 4)⁻¹) (cocompact (Rd d)) (𝓝 0) :=
    tendsto_inv_atTop_zero.comp h1
  refine squeeze_zero (fun y => (hL_pos y).le) (fun y => ?_) h2
  unfold hL phi
  refine inv_anti₀ (by positivity) ?_
  have := norm_sq_le_qd y
  have : ‖y‖ ^ 4 ≤ qd y ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) this 2
    nlinarith
  linarith

/-- **`IsFellerC0` for the Gibbs semigroup on `ℝ^d` under linear growth of `∇V`.** -/
theorem gibbsRdFull_isFellerC0_of_linGrowth (G : GibbsRdData d) {C : ℝ}
    (hC : ∀ (x : Rd d) (i : Fin d), |pderiv G.V i x| ≤ C * (1 + ∑ j, |x j|)) :
    IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple := by
  obtain ⟨lam, hlam0, hlam⟩ := Lr_hL_le G hC
  obtain ⟨K, hK0, hK⟩ := cut_bounds_lin G hC
  set K2 : ℝ := K + 12 * d * K with hK2
  have hK20 : 0 ≤ K2 := by positivity
  set Rn : ℕ → ℝ := fun n => ((n : ℝ) + 1) * ((d : ℝ) + 1) with hRn
  have hRn1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ Rn n := fun n => by
    simp only [hRn]; nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n), (Nat.cast_nonneg d : (0:ℝ) ≤ d)]
  have hRn0 : ∀ n : ℕ, 1 ≤ Rn n := fun n => by
    have := hRn1 n; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have : IsProbabilityMeasure G.gibbsRdFull_unconditional.toDiffusionTriple.μ :=
    (inferInstance : IsProbabilityMeasure G.toEll.μ)
  refine rd_isFellerC0_of_lyapunov G.gibbsRdFull_unconditional rfl rfl hlam0 hL sm_hL.continuous hL_pos
    hL_tendsto (fun n => uR (Rn n)) (fun n => ?_) (fun n y => ?_) (fun n y hy => ?_)
    (fun n => (K2 + 1) / (1 + Rn n ^ 4)) (fun n => by positivity) ?_ (fun n x => ?_)
  · -- membership in `A₀`
    have hR0 : 0 < Rn n := by linarith [hRn0 n]
    exact ⟨(sm_cut _).mul sm_hL, (hcs_cut hR0).mul_right⟩
  · exact ⟨mul_nonneg (cut_nonneg _ _) (hL_pos y).le,
      mul_le_of_le_one_left (hL_pos y).le (cut_le_one _ _)⟩
  · have hR0 : 0 < Rn n := by linarith [hRn0 n]
    have h1 : qd y ≤ (Rn n) ^ 2 := by
      calc qd y ≤ d * ‖y‖ ^ 2 := qd_le_norm_sq y
        _ ≤ d * (n : ℝ) ^ 2 := by
            gcongr
        _ ≤ (Rn n) ^ 2 := by
            simp only [hRn]
            have : (0:ℝ) ≤ n := Nat.cast_nonneg n
            have : (0:ℝ) ≤ d := Nat.cast_nonneg d
            nlinarith [mul_nonneg ‹(0:ℝ) ≤ n› ‹(0:ℝ) ≤ d›, sq_nonneg (n : ℝ), mul_nonneg (sq_nonneg (n:ℝ)) ‹(0:ℝ) ≤ d›]
    show cut (Rn n) y * hL y = hL y
    rw [cut_eq_one hR0 h1, one_mul]
  · have h1 : Tendsto (fun n : ℕ => (K2 + 1) * (1 / ((n : ℝ) + 1))) atTop (𝓝 ((K2 + 1) * 0)) :=
      tendsto_const_nhds.mul tendsto_one_div_add_atTop_nhds_zero_nat
    rw [mul_zero] at h1
    refine squeeze_zero (fun n => by positivity) (fun n => ?_) h1
    rw [← div_eq_mul_one_div]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    have := hRn1 n
    have h4 : Rn n ≤ Rn n ^ 4 := by
      have := hRn0 n
      nlinarith [pow_le_pow_right₀ this (by norm_num : 1 ≤ 4)]
    linarith
  · have hu : G.gibbsRdFull_unconditional.toDiffusionTriple.L (uR (Rn n)) x = Lr G.V (uR (Rn n)) x := by
      show G.toEll.L (uR (Rn n)) x = _
      exact congrFun (G.toEll_L (f := uR (Rn n)) ((sm_cut _).mul sm_hL)) x
    rw [hu]
    refine (Lr_cutmul_le G hlam hK0 hK (hRn0 n) x).trans ?_
    have : K2 / (1 + Rn n ^ 4) ≤ (K2 + 1) / (1 + Rn n ^ 4) :=
      div_le_div_of_nonneg_right (by linarith) (by positivity)
    linarith

/-- bounded Hessian (i.e. Lipschitz `∇V`) implies linear growth of `∇V` (as `BddHess3.grad_growth`, without the third derivative) -/
lemma linGrowth_of_hessBdd (G : GibbsRdData d) (hH : ∃ C : ℝ, ∀ (x : Rd d) (i j : Fin d),
    |pderiv (pderiv G.V i) j x| ≤ C) :
    ∃ C : ℝ, ∀ (x : Rd d) (i : Fin d), |pderiv G.V i x| ≤ C * (1 + ∑ j, |x j|) := by
  obtain ⟨C2, hC2⟩ := hH
  refine ⟨(∑ i, |pderiv G.V i 0|) + max C2 0, fun x i => ?_⟩
  set g := pderiv G.V i with hg
  have hgs : Sm g := G.smooth.pderiv i
  have hmv : ‖g ((1:ℝ) • x) - g ((0:ℝ) • x)‖ ≤ (max C2 0 * l1 x) * ‖(1 : ℝ) - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ => g (s • x)) (f' := fun t => ∑ j, x j * pderiv g j (t • x))
      (s := Set.Icc (0 : ℝ) 1) (C := max C2 0 * l1 x)
      (fun t _ => (hasDerivAt_ray hgs x t).hasDerivWithinAt) (fun t _ => ?_)
      (convex_Icc 0 1) (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold l1
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC2 (t • x) i j).trans (le_max_left _ _)) (abs_nonneg _)
  simp only [one_smul, zero_smul, norm_one, Real.norm_eq_abs, sub_zero, mul_one] at hmv
  have h0 : |g 0| ≤ ∑ i, |pderiv G.V i 0| :=
    Finset.single_le_sum (f := fun i => |pderiv G.V i 0|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h1 : |g x| ≤ |g 0| + |g x - g 0| := by
    have := abs_add_le (g 0) (g x - g 0)
    simpa using this
  have hl : 0 ≤ l1 x := l1_nonneg x
  have hm : 0 ≤ max C2 0 := le_max_right _ _
  have hS : 0 ≤ ∑ i, |pderiv G.V i 0| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  show |g x| ≤ (∑ i, |pderiv G.V i 0| + max C2 0) * (1 + l1 x)
  nlinarith [mul_nonneg hS hl, mul_nonneg hm hl]

/-- **`IsFellerC0` for a Gibbs semigroup with bounded Hessian (`∇V` Lipschitz).** -/
theorem gibbsRdFull_isFellerC0_of_hessBdd (G : GibbsRdData d)
    (hH : ∃ C : ℝ, ∀ (x : Rd d) (i j : Fin d), |pderiv (pderiv G.V i) j x| ≤ C) :
    IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple := by
  obtain ⟨C, hC⟩ := linGrowth_of_hessBdd G hH
  exact gibbsRdFull_isFellerC0_of_linGrowth G hC

/-- the bridge, unconditional under linear growth of `∇V` and convexity -/
noncomputable def gibbsRdFull_bridge_of_linGrowth (G : GibbsRdData d) (hV : HessGe G.V 0) {C : ℝ}
    (hC : ∀ (x : Rd d) (i : Fin d), |pderiv G.V i x| ≤ C * (1 + ∑ j, |x j|)) :
    MarkovProcessBridge G.gibbsRdFull_unconditional.toDiffusionTriple :=
  gibbsRdFull_bridge_of_feller_U G hV (gibbsRdFull_isFellerC0_of_linGrowth G hC)

/-- the bridge for convex `V` with bounded Hessian -/
noncomputable def gibbsRdFull_bridge_of_hessBdd (G : GibbsRdData d) (hV : HessGe G.V 0)
    (hH : ∃ C : ℝ, ∀ (x : Rd d) (i j : Fin d), |pderiv (pderiv G.V i) j x| ≤ C) :
    MarkovProcessBridge G.gibbsRdFull_unconditional.toDiffusionTriple :=
  gibbsRdFull_bridge_of_feller_U G hV (gibbsRdFull_isFellerC0_of_hessBdd G hH)

/-! ### Non-vacuity: the non-Gaussian example `V = |x|²/2 + cos(x₀)/2` -/

theorem cosData_isFellerC0 (n : ℕ) : IsFellerC0 (cosData n).gibbsRdFull_unconditional.toDiffusionTriple :=
  gibbsRdFull_isFellerC0_of_hessBdd _ (cosData_bddHess3 n).hess

theorem gaussData_isFellerC0 (n : ℕ) : IsFellerC0 (gaussData n).gibbsRdFull_unconditional.toDiffusionTriple :=
  gibbsRdFull_isFellerC0_of_hessBdd _ (gaussData_bddHess3 n).hess

/-- an unconditional Markov process bridge for the non-Gaussian Gibbs semigroup `cosData` -/
noncomputable def cosData_bridge (n : ℕ) :
    MarkovProcessBridge (cosData n).gibbsRdFull_unconditional.toDiffusionTriple :=
  gibbsRdFull_bridge_of_hessBdd _ (fun x v => by
    have := hessGe_cosV n x v
    have h0 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    show 0 * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, pderiv (pderiv (cosV n) i) j x * v i * v j
    nlinarith) (cosData_bddHess3 n).hess

end MarkovTriple.Stochastic.R32A2
