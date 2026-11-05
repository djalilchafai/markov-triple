import Mathlib
import MarkovTriple.Stochastic.R30T.Regularity
import MarkovTriple.Stochastic.R30T.Ellip

/-!
# Round 31 (X): reduction of decay at infinity to ONE cut-off function per compact set

See `STATEMENTS_R31_X.md`.  Positivity of the Markov semigroup (`semigroup_mono`) and a squeeze reduce
`IsFellerC0` (equivalently, by R30T G2, decay at infinity of `P_t f`, `f ∈ C_c`) to decay of `P_t φ_K`, where
`φ_K ∈ C_c`, `0 ≤ φ_K ≤ 1`, `φ_K = 1` on `K`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R31X

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R30T

/-- a continuous cut-off equal to `1` on `closedBall 0 R`, supported in `closedBall 0 (R+1)` -/
noncomputable def cutoffCc {d : ℕ} (R : ℝ) : C_c(Rd d, ℝ) where
  toFun y := max 0 (min 1 (R + 1 - ‖y‖))
  continuous_toFun := by fun_prop
  hasCompactSupport' := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Rd d) (R + 1)) fun y hy => ?_
    have : R + 1 < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right] using hy
    show max 0 (min 1 (R + 1 - ‖y‖)) = 0
    rw [max_eq_left]
    exact (min_le_right _ _).trans (by linarith)

lemma cutoffCc_apply {d : ℕ} (R : ℝ) (y : Rd d) : cutoffCc R y = max 0 (min 1 (R + 1 - ‖y‖)) := rfl

lemma cutoffCc_mem {d : ℕ} (R : ℝ) (y : Rd d) : 0 ≤ cutoffCc R y ∧ cutoffCc R y ≤ 1 := by
  rw [cutoffCc_apply]
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma cutoffCc_one {d : ℕ} (R : ℝ) (y : Rd d) (hy : ‖y‖ ≤ R) : cutoffCc R y = 1 := by
  rw [cutoffCc_apply, min_eq_left (by linarith), max_eq_right zero_le_one]

section Generic

variable {d : ℕ} (S : FullTriple (Rd d)) [IsFiniteMeasureOnCompacts S.toDiffusionTriple.μ]
  [S.toDiffusionTriple.μ.IsOpenPosMeasure]

theorem rd_isFellerC0_iff_cutoff (hA : S.A = Afull d) (hA₀ : S.A₀ = A₀ d) :
    IsFellerC0 S.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (K : Set (Rd d)), IsCompact K →
      ∃ φ : C_c(Rd d, ℝ), (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧ (∀ y ∈ K, φ y = 1) ∧
        ∀ g : C(Rd d, ℝ),
          (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple φ) : Rd d → ℝ)
            =ᵐ[S.toDiffusionTriple.μ] g → Tendsto g (cocompact (Rd d)) (𝓝 0) := by
  rw [rd_isFellerC0_iff_decay S hA hA₀]
  constructor
  · intro hdec t K hK
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Rd d)
    refine ⟨cutoffCc R, cutoffCc_mem R, fun y hy => cutoffCc_one R y ?_, fun g hg => hdec t _ g hg⟩
    simpa [Metric.mem_closedBall, dist_zero_right] using hR hy
  · intro h t f g hg
    set D := S.toDiffusionTriple with hD
    obtain ⟨φ, hφ01, hφK, hφdec⟩ := h t (tsupport f) f.hasCompactSupport
    obtain ⟨C, hC⟩ : ∃ C, ∀ y, |f y| ≤ C := by
      obtain ⟨C, hC⟩ := f.continuous.norm.bddAbove_range_of_hasCompactSupport
        (by simpa using f.hasCompactSupport.norm)
      exact ⟨C, fun y => hC ⟨y, rfl⟩⟩
    have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
    obtain ⟨gφ, -, hgφ⟩ := rd_semigroup_cc_exists_cont S hA hA₀ t φ (C := 1) (fun y => by
      rw [abs_of_nonneg (hφ01 y).1]; exact (hφ01 y).2)
    -- pointwise domination `|f| ≤ C φ`
    have hdom : ∀ y, |f y| ≤ C * φ y := by
      intro y
      by_cases hy : y ∈ tsupport f
      · rw [hφK y hy, mul_one]; exact hC y
      · have : f y = 0 := image_eq_zero_of_notMem_tsupport hy
        rw [this, abs_zero]; exact mul_nonneg hC0 (hφ01 y).1
    have hP : ∀ σ : ℝ, σ = 1 ∨ σ = -1 → ∀ x, σ * g x ≤ C * gφ x := by
      intro σ hσ
      have hlo : ((σ • ccL2 D f : Lp ℝ 2 D.μ) : Rd d → ℝ) ≤ᵐ[D.μ]
          ((C • ccL2 D φ : Lp ℝ 2 D.μ) : Rd d → ℝ) := by
        filter_upwards [Lp.coeFn_smul σ (ccL2 D f), Lp.coeFn_smul C (ccL2 D φ),
          coeFn_ccL2 (T := D) f, coeFn_ccL2 (T := D) φ] with y h1 h2 h3 h4
        rw [h1, h2, Pi.smul_apply, Pi.smul_apply, h3, h4, smul_eq_mul, smul_eq_mul]
        have := hdom y
        rcases hσ with rfl | rfl
        · rw [one_mul]; exact (le_abs_self _).trans this
        · rw [neg_one_mul]; exact (neg_le_abs _).trans this
      have hm := D.semigroup_mono t hlo
      rw [map_smul, map_smul] at hm
      have hc : ((σ • D.semigroup t (ccL2 D f) : Lp ℝ 2 D.μ) : Rd d → ℝ) ≤ᵐ[D.μ]
          fun x => C * gφ x := by
        filter_upwards [hm, Lp.coeFn_smul C (D.semigroup t (ccL2 D φ)), hgφ] with y h1 h2 h3
        rw [h2, Pi.smul_apply, h3, smul_eq_mul] at h1
        exact h1
      have hc2 : (fun x => σ * g x) ≤ᵐ[D.μ] fun x => C * gφ x := by
        filter_upwards [hc, Lp.coeFn_smul σ (D.semigroup t (ccL2 D f)), hg] with y h1 h2 h3
        rw [h2, Pi.smul_apply, h3, smul_eq_mul] at h1
        exact h1
      exact fun x => le_of_ae_le_cont S (u := fun x => σ * g x) (v := fun x => C * gφ x)
        (continuous_const.mul g.continuous) (continuous_const.mul gφ.continuous) hc2 x
    have hbd : ∀ x, ‖g x‖ ≤ C * |gφ x| := by
      intro x
      rw [Real.norm_eq_abs, abs_le]
      have a := hP 1 (Or.inl rfl) x
      have b := hP (-1) (Or.inr rfl) x
      have c : C * gφ x ≤ C * |gφ x| := mul_le_mul_of_nonneg_left (le_abs_self _) hC0
      constructor <;> linarith
    have hdφ : Tendsto (fun x => C * |gφ x|) (cocompact (Rd d)) (𝓝 0) := by
      have := ((hφdec gφ hgφ).abs).const_mul C
      simpa using this
    exact squeeze_zero_norm hbd hdφ

end Generic

section Instances

variable {d : ℕ}

theorem gibbsRdFull_isFellerC0_iff_cutoff (G : GibbsRdData d) :
    IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (K : Set (Rd d)), IsCompact K →
      ∃ φ : C_c(Rd d, ℝ), (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧ (∀ y ∈ K, φ y = 1) ∧
        ∀ g : C(Rd d, ℝ),
          (G.gibbsRdFull_unconditional.toDiffusionTriple.semigroup t
            (ccL2 G.gibbsRdFull_unconditional.toDiffusionTriple φ) : Rd d → ℝ)
            =ᵐ[G.gibbsRdFull_unconditional.toDiffusionTriple.μ] g → Tendsto g (cocompact (Rd d)) (𝓝 0) :=
  rd_isFellerC0_iff_cutoff G.gibbsRdFull_unconditional rfl rfl

theorem fullU_isFellerC0_iff_cutoff (E : EllData d) :
    IsFellerC0 E.fullU.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (K : Set (Rd d)), IsCompact K →
      ∃ φ : C_c(Rd d, ℝ), (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧ (∀ y ∈ K, φ y = 1) ∧
        ∀ g : C(Rd d, ℝ),
          (E.fullU.toDiffusionTriple.semigroup t (ccL2 E.fullU.toDiffusionTriple φ) : Rd d → ℝ)
            =ᵐ[E.fullU.toDiffusionTriple.μ] g → Tendsto g (cocompact (Rd d)) (𝓝 0) :=
  rd_isFellerC0_iff_cutoff E.fullU rfl rfl

theorem riemFull_isFellerC0_iff_cutoff (R : Riemannian.RiemData d) :
    IsFellerC0 R.riemFull_unconditional.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (K : Set (Rd d)), IsCompact K →
      ∃ φ : C_c(Rd d, ℝ), (∀ y, 0 ≤ φ y ∧ φ y ≤ 1) ∧ (∀ y ∈ K, φ y = 1) ∧
        ∀ g : C(Rd d, ℝ),
          (R.riemFull_unconditional.toDiffusionTriple.semigroup t
            (ccL2 R.riemFull_unconditional.toDiffusionTriple φ) : Rd d → ℝ)
            =ᵐ[R.riemFull_unconditional.toDiffusionTriple.μ] g → Tendsto g (cocompact (Rd d)) (𝓝 0) :=
  rd_isFellerC0_iff_cutoff R.riemFull_unconditional rfl rfl

end Instances

end MarkovTriple.Stochastic.R31X
