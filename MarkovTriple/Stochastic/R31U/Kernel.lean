import Mathlib
import MarkovTriple.Stochastic.R31U.Lip
import MarkovTriple.Stochastic.R24.Feller

/-!
# Round 31 (U), part 5: `κ_s(x,·) ≪ μ` at EVERY `x` (U3)

Let `K` be compact with `μ(K) = 0`, `f_n ↓ 1_K` in `C_c`.  Then `‖P_s f_n‖₂ ≤ ‖f_n‖₂ → 0` and the continuous representatives `Q_s f_n` are
locally uniformly Lipschitz (`rd_smoothing_lip`, data bounded by `1`); a Chebyshev argument on a small ball around `x` (full support)
gives `Q_s f_n (x) → 0`, i.e. `κ_s(x,K) = 0`.  Inner regularity of the Riesz measure `κ_s(x,·)` finishes.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R31U

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R30T

/-- the cut-off `f_n = (1 - (n+1) dist(·,K))⁺` -/
noncomputable def cut {d : ℕ} (K : Set (Rd d)) (n : ℕ) (y : Rd d) : ℝ :=
  max 0 (1 - ((n : ℝ) + 1) * Metric.infDist y K)

section Cut

variable {d : ℕ} {K : Set (Rd d)}

lemma cut_cont (n : ℕ) : Continuous (cut K n) := by
  unfold cut
  exact continuous_const.max (continuous_const.sub (continuous_const.mul (Metric.continuous_infDist_pt K)))

lemma cut_nonneg (n : ℕ) (y : Rd d) : 0 ≤ cut K n y := le_max_left _ _

lemma cut_le_one (n : ℕ) (y : Rd d) : cut K n y ≤ 1 := by
  unfold cut
  refine max_le zero_le_one ?_
  have : 0 ≤ ((n : ℝ) + 1) * Metric.infDist y K := mul_nonneg (by positivity) Metric.infDist_nonneg
  linarith

lemma cut_one {n : ℕ} {y : Rd d} (hy : y ∈ K) : cut K n y = 1 := by
  unfold cut
  rw [Metric.infDist_zero_of_mem hy]; simp

lemma cut_mem_cthickening (hK : IsCompact K) (hne : K.Nonempty) (n : ℕ) {y : Rd d} (hy : cut K n y ≠ 0) :
    y ∈ Metric.cthickening (1 / ((n : ℝ) + 1)) K := by
  have h1 : 0 < 1 - ((n : ℝ) + 1) * Metric.infDist y K := by
    by_contra hle
    push Not at hle
    apply hy
    unfold cut
    exact max_eq_left hle
  obtain ⟨z, hz, hdz⟩ := hK.exists_infDist_eq_dist hne y
  refine Metric.mem_cthickening_of_dist_le y z _ K hz ?_
  rw [← hdz, le_div_iff₀ (by positivity)]
  nlinarith

lemma cut_hasCompactSupport (hK : IsCompact K) (hne : K.Nonempty) (n : ℕ) :
    HasCompactSupport (cut K n) := by
  refine HasCompactSupport.intro (hK.cthickening (r := 1 / ((n : ℝ) + 1))) fun y hy => ?_
  by_contra h
  exact hy (cut_mem_cthickening hK hne n h)

end Cut

variable {d : ℕ} (S : FullTriple (Rd d)) [IsFiniteMeasure S.toDiffusionTriple.μ]
  [S.toDiffusionTriple.μ.IsOpenPosMeasure]

/-- a compact `μ`-null set is `κ_s(x,·)`-null -/
theorem kernel_null_compact (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d) (hCD : S.CD 0 ∞)
    (hell : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
      c * ∑ i, pderiv g i x ^ 2 ≤ S.toDiffusionTriple.ΓA g g x)
    (hF : IsFellerC0 S.toDiffusionTriple) (s : ℝ≥0) (hs : 0 < s) (x : Rd d)
    {K : Set (Rd d)} (hK : IsCompact K) (hμK : S.toDiffusionTriple.μ K = 0) :
    fellerKernelInf hF s x K = 0 := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  set μ := S.toDiffusionTriple.μ with hμ
  obtain ⟨Kl, hKl0, hKl⟩ := rd_smoothing_lip S hA hA₀ hCD hell (‖x‖ + 2)
  set L : ℝ := Kl / Real.sqrt s with hL
  have hL0 : 0 ≤ L := by positivity
  have key : ∀ η : ℝ, 0 < η → (fellerKernelInf hF s x).real K < η := by
    intro η hη
    set r : ℝ := min 1 (η / (2 * (L + 1))) with hr
    have hr0 : 0 < r := lt_min one_pos (by positivity)
    have hr1 : r ≤ 1 := min_le_left _ _
    have hLr : L * r < η / 2 := by
      have h1 : r ≤ η / (2 * (L + 1)) := min_le_right _ _
      calc L * r ≤ L * (η / (2 * (L + 1))) := mul_le_mul_of_nonneg_left h1 hL0
        _ < η / 2 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by positivity)]
          nlinarith
    set B : Set (Rd d) := Metric.ball x r with hB
    have hBpos : 0 < μ.real B := by
      have h1 : 0 < μ B := Metric.isOpen_ball.measure_pos μ ⟨x, Metric.mem_ball_self hr0⟩
      exact ENNReal.toReal_pos h1.ne' (measure_ball_lt_top).ne
    set ρ0 : ℝ := (η / 2) ^ 2 * μ.real B with hρ0
    have hρ0pos : 0 < ρ0 := by positivity
    -- measure of the thickenings tends to `μ K = 0`
    have ht := tendsto_measure_cthickening_of_isCompact (μ := μ) hK
    rw [hμK] at ht
    have hδ0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    have ht' := ht.comp hδ0
    have hev := (ht'.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ENNReal.ofReal ρ0 by simpa using hρ0pos)))
    obtain ⟨n, hn⟩ := hev.exists
    set f : C_c(Rd d, ℝ) := ⟨⟨cut K n, cut_cont n⟩, cut_hasCompactSupport hK hne n⟩ with hf
    have hfapply : ∀ y, f y = cut K n y := fun y => rfl
    have hf1 : ∀ y, |f y| ≤ 1 := fun y => by
      rw [hfapply, abs_of_nonneg (cut_nonneg n y)]; exact cut_le_one n y
    -- `‖f‖₂² < ρ0`
    have hfnorm : ‖ccL2 S.toDiffusionTriple f‖ ^ 2 < ρ0 := by
      have hint : Integrable (fun y => (ccL2 S.toDiffusionTriple f : Rd d → ℝ) y ^ 2) μ :=
        (Lp.memLp (ccL2 S.toDiffusionTriple f)).integrable_sq
      have hnorm : ‖ccL2 S.toDiffusionTriple f‖ ^ 2 = ∫ y, (ccL2 S.toDiffusionTriple f : Rd d → ℝ) y ^ 2 ∂μ := by
        rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
        simp only [RCLike.inner_apply, conj_trivial, sq]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        ring
      rw [hnorm]
      have hmeas : MeasurableSet (Metric.cthickening (1 / ((n : ℝ) + 1)) K) :=
        Metric.isClosed_cthickening.measurableSet
      have hle : ∫ y, (ccL2 S.toDiffusionTriple f : Rd d → ℝ) y ^ 2 ∂μ ≤
          ∫ y, (Metric.cthickening (1 / ((n : ℝ) + 1)) K).indicator (fun _ => (1 : ℝ)) y ∂μ := by
        refine integral_mono_ae hint ((integrable_const (1 : ℝ)).indicator hmeas) ?_
        filter_upwards [coeFn_ccL2 (T := S.toDiffusionTriple) f] with y hy
        rw [hy, hfapply]
        by_cases hyc : y ∈ Metric.cthickening (1 / ((n : ℝ) + 1)) K
        · rw [Set.indicator_of_mem hyc]
          have := cut_nonneg (K := K) n y
          have := cut_le_one (K := K) n y
          nlinarith
        · rw [Set.indicator_of_notMem hyc]
          have : cut K n y = 0 := by
            by_contra hne'
            exact hyc (cut_mem_cthickening hK hne n hne')
          rw [this]; simp
      refine hle.trans_lt ?_
      rw [integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
      have h3 : μ (Metric.cthickening (1 / ((n : ℝ) + 1)) K) < ENNReal.ofReal ρ0 := hn
      exact ENNReal.toReal_lt_of_lt_ofReal h3
    set u : Lp ℝ 2 μ := S.toDiffusionTriple.semigroup s (ccL2 S.toDiffusionTriple f) with hu
    have hun : ‖u‖ ^ 2 < (η / 2) ^ 2 * μ.real B := by
      have h1 : ‖u‖ ≤ ‖ccL2 S.toDiffusionTriple f‖ :=
        DiffusionTriple.norm_semigroup_apply_le S.toDiffusionTriple s _
      calc ‖u‖ ^ 2 ≤ ‖ccL2 S.toDiffusionTriple f‖ ^ 2 := by gcongr
        _ < _ := hfnorm
    obtain ⟨y, hyB, hy⟩ := exists_small_of_norm_lt (by positivity : 0 < η / 2) u _ (Qop_ae hF s f) hun
    have hyB' : dist y x < r := hyB
    have hxy : ‖x - y‖ < r := by rw [← dist_eq_norm, dist_comm]; exact hyB'
    have hyR : ‖y‖ < ‖x‖ + 2 := by
      have := norm_sub_norm_le y x
      rw [dist_eq_norm] at hyB'
      linarith
    have hlip := hKl s hs 1 f hf1 (Qop hF s f).toContinuousMap (Qop_ae hF s f) x y (by linarith) hyR
    have hlip' : |Qop hF s f x - Qop hF s f y| ≤ L * r := by
      refine hlip.trans ?_
      have : Kl * 1 / Real.sqrt s * ‖x - y‖ = L * ‖x - y‖ := by rw [hL]; ring
      show Kl * 1 / Real.sqrt s * ‖x - y‖ ≤ L * r
      rw [this]
      exact mul_le_mul_of_nonneg_left hxy.le hL0
    -- `κ.real K ≤ Q f (x)`
    have hκ : (fellerKernelInf hF s x).real K ≤ Qop hF s f x := by
      rw [← integral_fellerKernelInf hF s x f]
      have hKm : MeasurableSet K := hK.isClosed.measurableSet
      rw [← integral_indicator_one hKm]
      refine integral_mono ((integrable_const (1 : ℝ)).indicator hKm) ?_ ?_
      · exact (f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport)
      · intro z
        by_cases hz : z ∈ K
        · rw [Set.indicator_of_mem hz, hfapply, cut_one hz]; simp
        · rw [Set.indicator_of_notMem hz]; exact (cut_nonneg n z)
    have : Qop hF s f x ≤ |Qop hF s f y| + |Qop hF s f x - Qop hF s f y| := by
      have := abs_sub_abs_le_abs_sub (Qop hF s f x) (Qop hF s f y)
      linarith [le_abs_self (Qop hF s f x)]
    have hy' : |Qop hF s f y| < η / 2 := hy
    linarith
  have h0 : (fellerKernelInf hF s x).real K ≤ 0 := le_of_forall_pos_le_add fun η hη => by
    have := key η hη; linarith
  have : IsFiniteMeasure (fellerKernelInf hF s x) := R24.fellerMeasure_finite hF s x
  have h1 : ((fellerKernelInf hF s x) K).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
  exact ((ENNReal.toReal_eq_zero_iff _).1 h1).resolve_right (measure_ne_top _ _)

/-- **U3** (frozen statement): `κ_s(x,·) ≪ μ` at every `x`. -/
theorem rd_kernel_ac (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d) (hCD : S.CD 0 ∞)
    (hell : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
      c * ∑ i, pderiv g i x ^ 2 ≤ S.toDiffusionTriple.ΓA g g x)
    (hF : IsFellerC0 S.toDiffusionTriple) (s : ℝ≥0) (hs : 0 < s) (x : Rd d) :
    fellerKernelInf hF s x ≪ S.toDiffusionTriple.μ := by
  intro A hA0
  have hA' : S.toDiffusionTriple.μ (toMeasurable S.toDiffusionTriple.μ A) = 0 := by
    rw [measure_toMeasurable]; exact hA0
  refine measure_mono_null (subset_toMeasurable S.toDiffusionTriple.μ A) ?_
  have : IsFiniteMeasure (fellerKernelInf hF s x) := R24.fellerMeasure_finite hF s x
  have : (fellerKernelInf hF s x).Regular := R24.fellerMeasure_regular hF s x
  rw [(measurableSet_toMeasurable S.toDiffusionTriple.μ A).measure_eq_iSup_isCompact]
  refine le_antisymm (iSup₂_le fun K hKsub => iSup_le fun hK => ?_) zero_le
  exact (kernel_null_compact S hA hA₀ hCD hell hF s hs x hK (measure_mono_null hKsub hA')).le

end MarkovTriple.Stochastic.R31U
