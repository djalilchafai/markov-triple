import Mathlib
import MarkovTriple.Stochastic.R25.HeatKernel
import MarkovTriple.Stochastic.R24.Operator
import MarkovTriple.BGL.Instances.LebesgueRd.Full.Main

/-!
# Round 25 (E), part 2: `(ℝ^d, Lebesgue)` is `C_0`-Feller
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R25

open MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ ψ : (Fin d → ℝ) → ℝ}

lemma continuous_heatRd (hc : Continuous φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (a : ℝ) :
    Continuous (heatRd a φ) := by
  unfold heatRd
  exact continuous_of_dominated (bound := fun _ => C)
    (fun x => (hc.comp (by fun_prop)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun z => by simpa using hC _) (integrable_const C)
    (ae_of_all _ fun z => hc.comp (by fun_prop))

lemma tendsto_heatRd_cocompact (hc : Continuous φ) (hcs : HasCompactSupport φ) (a : ℝ) :
    Tendsto (heatRd a φ) (cocompact (Fin d → ℝ)) (𝓝 0) := by
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hcs
  have : (cocompact (Fin d → ℝ)).IsCountablyGenerated := by
    rw [← comap_dist_left_atTop_eq_cocompact (0 : Fin d → ℝ)]; infer_instance
  have := tendsto_integral_filter_of_dominated_convergence (μ := gam d)
    (l := cocompact (Fin d → ℝ)) (F := fun x z => φ (x - a • z)) (f := fun _ => (0 : ℝ))
    (fun _ => C)
    (Eventually.of_forall fun x => (hc.comp (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun x => ae_of_all _ fun z => hC _) (integrable_const C)
    (ae_of_all _ fun z => hcs.is_zero_at_infty.comp ((Homeomorph.subRight (a • z)).isClosedEmbedding.tendsto_cocompact))
  rw [integral_zero] at this
  exact this

/-- symmetry of Gaussian smoothing for continuous bounded integrable functions -/
theorem integral_mul_heat_comm_gen (hφc : Continuous φ) (hψc : Continuous ψ) {C D : ℝ}
    (hC : ∀ x, |φ x| ≤ C) (hD : ∀ x, |ψ x| ≤ D) (hφi : Integrable φ volume)
    (hψi : Integrable ψ volume) (a : ℝ) :
    ∫ x, ψ x * heatRd a φ x = ∫ x, φ x * heatRd a ψ x := by
  have h1 : ∀ x, ψ x * heatRd a φ x = ∫ z, ψ x * φ (x - a • z) ∂(gam d) := fun x => by
    unfold heatRd; rw [integral_const_mul]
  have h2 : ∀ y, φ y * heatRd a ψ y = ∫ z, φ y * ψ (y + a • z) ∂(gam d) := fun y => by
    unfold heatRd
    rw [← integral_const_mul, ← integral_gam_neg (fun z => φ y * ψ (y - a • z))]
    simp
  simp only [h1, h2]
  have hint1 : Integrable (Function.uncurry fun (x z : Fin d → ℝ) => ψ x * φ (x - a • z))
      (volume.prod (gam d)) := by
    refine Integrable.mono' (((hψi.norm).comp_fst (gam d)).const_mul C)
      ((hψc.comp continuous_fst).mul (hφc.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
  have hint2 : Integrable (Function.uncurry fun (z y : Fin d → ℝ) => φ y * ψ (y + a • z))
      ((gam d).prod volume) := by
    refine Integrable.mono' (((hφi.norm).comp_snd (gam d)).const_mul D)
      ((hφc.comp continuous_snd).mul (hψc.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
    rw [mul_comm D]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg _)
  rw [integral_integral_swap hint1, ← integral_integral_swap hint2]
  congr 1
  funext z
  have := integral_add_right_eq_self (μ := (volume : Measure (Fin d → ℝ)))
    (fun x => ψ x * φ (x - a • z)) (a • z)
  simp only [add_sub_cancel_right] at this
  rw [← this]
  congr 1
  funext y
  ring

lemma memLp_heat_gen (hc : Continuous φ) {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (hi : Integrable φ volume)
    (a : ℝ) : MemLp (heatRd a φ) 2 volume := by
  have hint := integrable_heat_gen hc hi a
  rw [memLp_two_iff_integrable_sq hint.aestronglyMeasurable]
  refine Integrable.mono' (hint.norm.const_mul C) (hint.aestronglyMeasurable.pow 2)
    (ae_of_all _ fun x => ?_)
  have h0 := abs_heat_le hC a x
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  nlinarith [abs_nonneg (heatRd a φ x), sq_abs (heatRd a φ x)]

open MarkovTriple.BGL in
lemma semigroup_cc_aux (hd : 1 ≤ d) (t : ℝ≥0) (f : C_c(Fin d → ℝ, ℝ))
    (u : Lp ℝ 2 (lebesgueRdDiffusion d hd).μ)
    (hu : (u : (Fin d → ℝ) → ℝ) =ᵐ[(lebesgueRdDiffusion d hd).μ] f) :
    ((lebesgueRdDiffusion d hd).semigroup t u : (Fin d → ℝ) → ℝ)
      =ᵐ[(lebesgueRdDiffusion d hd).μ] heatRd (Real.sqrt (2 * t)) f := by
  change (u : (Fin d → ℝ) → ℝ) =ᵐ[volume] f at hu
  change ((lebesgueRdDiffusion d hd).semigroup t u : (Fin d → ℝ) → ℝ) =ᵐ[volume] _
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hC' : ∀ x, |f x| ≤ C := fun x => by simpa using hC x
  have hfi : Integrable f volume := f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  have hL := memLp_heat_gen f.continuous hC' hfi (Real.sqrt (2 * t))
  have key : (lebesgueRdDiffusion d hd).semigroup t u = hL.toLp _ := by
    rw [← sub_eq_zero]
    refine (lebesgueRdDiffusion d hd).eq_zero_of_orth _ (fun g => ?_)
    rw [inner_sub_left, sub_eq_zero]
    obtain ⟨D, hD⟩ := bdd_of_A₀ g.2
    have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1
      ((lebesgueRdDiffusion d hd).semigroup_isSelfAdjoint t) u ((lebesgueRdDiffusion d hd).cls g)
    refine hsym.trans ?_
    have e : (lebesgueRdDiffusion d hd).semigroup t ((lebesgueRdDiffusion d hd).cls g) =
        heatL2 g.1 (Real.sqrt (2 * t)) := semigroup_eq_heatRd hd g.2 t
    erw [e]
    rw [L2_inner_eq, L2_inner_eq]
    have h1 : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)),
        (u : (Fin d → ℝ) → ℝ) x * (heatL2 g.1 (Real.sqrt (2 * t)) : (Fin d → ℝ) → ℝ) x
          = f x * heatRd (Real.sqrt (2 * t)) g.1 x := by
      filter_upwards [hu, coeFn_heatL2 g.2 (Real.sqrt (2 * t))] with x h1 h2
      rw [h1, h2]
    have h2 : ∀ᵐ x ∂(volume : Measure (Fin d → ℝ)),
        (hL.toLp _ : (Fin d → ℝ) → ℝ) x * ((lebesgueRdDiffusion d hd).cls g : (Fin d → ℝ) → ℝ) x
          = g.1 x * heatRd (Real.sqrt (2 * t)) f x := by
      filter_upwards [hL.coeFn_toLp, (lebesgueRdDiffusion d hd).coeFn_cls g] with x h1 h2
      rw [h1, h2, mul_comm]; rfl
    rw [integral_congr_ae h1, integral_congr_ae h2]
    exact (integral_mul_heat_comm_gen f.continuous (smooth g.2).continuous hC' hD
      hfi (integrable_of g.2) _).symm
  rw [key]
  exact hL.coeFn_toLp

open MarkovTriple.BGL in
/-- **Extension of `semigroup_eq_heatRd` from `C_c^∞` to `C_c`**: for a compactly supported continuous `f` and an
`L²` class `u` of `f`, `P_t u = heatRd (√(2t)) f` a.e. -/
theorem lebesgueRd_semigroup_cc (hd : 1 ≤ d) (t : ℝ≥0) (f : C_c(Fin d → ℝ, ℝ))
    (u : Lp ℝ 2 (lebesgueRdFull d hd).toDiffusionTriple.μ)
    (hu : (u : (Fin d → ℝ) → ℝ) =ᵐ[(lebesgueRdFull d hd).toDiffusionTriple.μ] f) :
    ((lebesgueRdFull d hd).toDiffusionTriple.semigroup t u : (Fin d → ℝ) → ℝ)
      =ᵐ[(lebesgueRdFull d hd).toDiffusionTriple.μ] heatRd (Real.sqrt (2 * t)) f :=
  semigroup_cc_aux hd t f u hu

open MarkovTriple.BGL MarkovTriple.Stochastic.R24 in
/-- **`(ℝ^d, Lebesgue)` is `C_0`-Feller**; the `C_0` representative of `P_t f` is `heatRd (√(2t)) f`. -/
theorem lebesgueRd_isFellerC0 (hd : 1 ≤ d) : IsFellerC0 (lebesgueRdFull d hd).toDiffusionTriple := by
  intro t f u hu
  obtain ⟨C, hC⟩ := f.continuous.bounded_above_of_compact_support f.hasCompactSupport
  have hC' : ∀ x, |f x| ≤ C := fun x => by simpa using hC x
  refine ⟨⟨⟨heatRd (Real.sqrt (2 * t)) f, continuous_heatRd f.continuous hC' _⟩,
    tendsto_heatRd_cocompact f.continuous f.hasCompactSupport _⟩, ?_⟩
  exact lebesgueRd_semigroup_cc hd t f u hu

instance lebesgueRd_finiteOnCompacts (hd : 1 ≤ d) :
    IsFiniteMeasureOnCompacts (lebesgueRdFull d hd).toDiffusionTriple.μ :=
  inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure (Fin d → ℝ)))

instance lebesgueRd_openPos (hd : 1 ≤ d) :
    (lebesgueRdFull d hd).toDiffusionTriple.μ.IsOpenPosMeasure :=
  inferInstanceAs ((volume : Measure (Fin d → ℝ)).IsOpenPosMeasure)

end MarkovTriple.Stochastic.R25
