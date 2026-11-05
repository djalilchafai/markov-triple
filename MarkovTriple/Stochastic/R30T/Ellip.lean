import Mathlib
import MarkovTriple.Stochastic.R30T.Regularity

/-!
# Round 30 (T), part 6: local ellipticity of `EllData` and the initial condition / reduced bridges for `fullU`, `riemFull`

`a_pos` + continuity of `a` + compactness of `{|x| ≤ R} × S^{d-1}` give a local uniform ellipticity constant `c(R)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R30T

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R27 MarkovTriple.Stochastic.R29

variable {d : ℕ}

/-- **local uniform ellipticity** of the co-metric. -/
theorem ellData_local_ell (E : EllData d) (R : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (x v : Rd d), ‖x‖ ≤ R → c * ∑ i, v i ^ 2 ≤ ∑ i, ∑ j, E.a i j x * v i * v j := by
  set K : Set (Rd d × Rd d) := {z | ‖z.1‖ ≤ R ∧ ∑ i, z.2 i ^ 2 = 1} with hK
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · refine IsClosed.inter ?_ ?_
      · exact isClosed_le (continuous_norm.comp continuous_fst) continuous_const
      · exact isClosed_eq (continuous_finsetSum _ fun i _ => ((continuous_apply i).comp continuous_snd).pow 2)
          continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : Rd d)) (r := max R 0)).prod
        (Metric.isBounded_closedBall (x := (0 : Rd d)) (r := 1)) |>.subset ?_
      intro z hz
      refine ⟨?_, ?_⟩
      · rw [mem_closedBall_zero_iff]; exact hz.1.trans (le_max_left _ _)
      · rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
        intro i
        have : z.2 i ^ 2 ≤ 1 := by
          rw [← hz.2]
          exact Finset.single_le_sum (f := fun j => z.2 j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
        rw [Real.norm_eq_abs]
        exact abs_le_one_iff_mul_self_le_one.2 (by nlinarith)
  set F : Rd d × Rd d → ℝ := fun z => ∑ i, ∑ j, E.a i j z.1 * z.2 i * z.2 j with hF
  have hFc : Continuous F := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact (((E.a_smooth i j).continuous.comp continuous_fst).mul ((continuous_apply i).comp continuous_snd)).mul
      ((continuous_apply j).comp continuous_snd)
  by_cases hne : K.Nonempty
  · obtain ⟨z0, hz0K, hz0⟩ := hKc.exists_isMinOn hne hFc.continuousOn
    have hv0 : z0.2 ≠ 0 := by
      intro h0
      have := hz0K.2
      simp [h0] at this
    have hpos : 0 < F z0 := E.a_pos z0.1 z0.2 hv0
    refine ⟨F z0, hpos, fun x v hx => ?_⟩
    by_cases hs : ∑ i, v i ^ 2 = 0
    · have : ∀ i, v i = 0 := fun i => by
        have h1 : v i ^ 2 = 0 :=
          le_antisymm (hs ▸ Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ i)) (sq_nonneg _)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 h1
      simp [this]
    · have hspos : 0 < ∑ i, v i ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hs)
      set s := ∑ i, v i ^ 2 with hs'
      set u : Rd d := fun i => v i / Real.sqrt s with hu
      have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
      have hun : ∑ i, u i ^ 2 = 1 := by
        simp only [hu, div_pow, Real.sq_sqrt hspos.le]
        rw [← Finset.sum_div]; exact div_self hs
      have hmem : (x, u) ∈ K := ⟨hx, hun⟩
      have hle := hz0 hmem
      have hFu : F (x, u) = (∑ i, ∑ j, E.a i j x * v i * v j) / s := by
        simp only [hF, hu]
        have : ∀ i j, E.a i j x * (v i / Real.sqrt s) * (v j / Real.sqrt s)
            = (E.a i j x * v i * v j) / s := fun i j => by
          field_simp
          rw [Real.sq_sqrt hspos.le]
          ring
        simp only [this]
        rw [Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => (Finset.sum_div _ _ _).symm
      have : F z0 ≤ (∑ i, ∑ j, E.a i j x * v i * v j) / s := hFu ▸ hle
      rw [le_div_iff₀ hspos] at this
      linarith
  · refine ⟨1, one_pos, fun x v hx => ?_⟩
    by_cases hs : ∑ i, v i ^ 2 = 0
    · have : ∀ i, v i = 0 := fun i => by
        have h1 : v i ^ 2 = 0 :=
          le_antisymm (hs ▸ Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _)
            (Finset.mem_univ i)) (sq_nonneg _)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 h1
      simp [this]
    · exfalso
      have hspos : 0 < ∑ i, v i ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hs)
      set s := ∑ i, v i ^ 2 with hs'
      have hsq : 0 < Real.sqrt s := Real.sqrt_pos.2 hspos
      apply hne
      refine ⟨(x, fun i => v i / Real.sqrt s), hx, ?_⟩
      simp only [div_pow, Real.sq_sqrt hspos.le]
      rw [← Finset.sum_div]; exact div_self hs

/-- the local ellipticity hypothesis `hell` of `rd_initial_condition` holds for `EllData`'s `diff` -/
theorem ellData_hell (E : EllData d) : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
    c * ∑ i, pderiv g i x ^ 2 ≤ E.diff.ΓA g g x := by
  intro R
  obtain ⟨c, hc, h⟩ := ellData_local_ell E R
  refine ⟨c, hc, fun g hg x hx => ?_⟩
  rw [E.ΓA_eq hg hg]
  exact h x (fun i => pderiv g i x) hx

section Instances

variable (E : EllData d) (R : Riemannian.RiemData d)

/-- `fullU`, convex case (`Curv 0`): pointwise initial condition for the exact `C_0` operators -/
theorem fullU_hinit (hC : E.Curv 0) (hF : IsFellerC0 E.fullU.toDiffusionTriple) (x : Rd d) (f : C_c(Rd d, ℝ)) :
    Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδt⟩ := rd_initial_condition E.fullU rfl rfl (E.fullU_CD hC) (ellData_hell E) f x hε
  refine ⟨δ, hδ, fun {t} _ ht => ?_⟩
  have htδ : t < δ := by
    rw [NNReal.dist_eq] at ht
    simpa using ht
  have := hδt t htδ (Qop hF t f).toContinuousMap (Qop_ae hF t f)
  rw [Real.dist_eq]
  exact this

/-- `riemFull`, convex case (`Curv 0`) -/
theorem riemFull_hinit (hC : R.Curv 0) (hF : IsFellerC0 R.riemFull_unconditional.toDiffusionTriple) (x : Rd d)
    (f : C_c(Rd d, ℝ)) :
    Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδt⟩ := rd_initial_condition R.riemFull_unconditional rfl rfl (R.riemFull_CD_unconditional hC)
    (ellData_hell R.toEll) f x hε
  refine ⟨δ, hδ, fun {t} _ ht => ?_⟩
  have htδ : t < δ := by
    rw [NNReal.dist_eq] at ht
    simpa using ht
  have := hδt t htδ (Qop hF t f).toContinuousMap (Qop_ae hF t f)
  rw [Real.dist_eq]
  exact this

/-- R29 `fullU_bridge_of_feller` with (d) discharged (`Curv 0`) -/
noncomputable def fullU_bridge_of_feller_ac (hC : E.Curv 0) (hF : IsFellerC0 E.fullU.toDiffusionTriple)
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ E.fullU.μ) :
    MarkovProcessBridge E.fullU.toDiffusionTriple :=
  fullU_bridge_of_feller E hF hac (fun x f => fullU_hinit E hC hF x f)

/-- R29 `riemFull_bridge_of_feller` with (d) discharged (`Curv 0`) -/
noncomputable def riemFull_bridge_of_feller_ac (hC : R.Curv 0)
    (hF : IsFellerC0 R.riemFull_unconditional.toDiffusionTriple)
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ R.riemFull_unconditional.μ) :
    MarkovProcessBridge R.riemFull_unconditional.toDiffusionTriple :=
  riemFull_bridge_of_feller R hF hac (fun x f => riemFull_hinit R hC hF x f)

end Instances

end MarkovTriple.Stochastic.R30T
