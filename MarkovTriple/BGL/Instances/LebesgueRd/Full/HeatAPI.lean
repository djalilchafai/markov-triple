import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatDefs
import MarkovTriple.BGL.Instances.LebesgueRd.Full.HeatAux

/-!
# Heat flow on `ℝ^d`: pointwise, smoothness, `L²` facts (Round 24, stream A, STATEMENTS_R24_A.md, part H-a)

Port of `Instances/Lebesgue/Heat.lean` to `ℝ^d`; the decay `tendsto_heatL2_zero` uses the density of
`gam d` (`HeatAux.lean`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ} {φ ψ : (Fin d → ℝ) → ℝ}

theorem heatRd_zero (φ : (Fin d → ℝ) → ℝ) : heatRd 0 φ = φ := by
  funext x; simp [heatRd]

lemma bdd_of_A₀ {f : (Fin d → ℝ) → ℝ} (hf : f ∈ A₀ d) : ∃ C, ∀ x, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (smooth hf).continuous.bounded_above_of_compact_support (cs hf)
  exact ⟨C, fun x => by simpa using hC x⟩

lemma fderiv_apply_mem (hφ : φ ∈ A₀ d) (y : Fin d → ℝ) : (fun w => fderiv ℝ φ w y) ∈ A₀ d :=
  mem_A₀.2 ⟨((smooth hφ).fderiv_right (by simp)).clm_apply contDiff_const,
    (cs hφ).fderiv_apply ℝ y⟩

lemma hasFDerivAt_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) (x : Fin d → ℝ) :
    HasFDerivAt (heatRd a φ) (∫ z, fderiv ℝ φ (x - a • z) ∂(gam d)) x := by
  obtain ⟨C, hC⟩ := bdd_of_A₀ hφ
  have hcont' : Continuous (fderiv ℝ φ) := (smooth hφ).continuous_fderiv (by simp)
  obtain ⟨C', hC'⟩ := hcont'.bounded_above_of_compact_support (HasCompactSupport.fderiv (𝕜 := ℝ) (cs hφ))
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := gam d)
    (F := fun x z => φ (x - a • z)) (F' := fun x z => fderiv ℝ φ (x - a • z)) (x₀ := x)
    (bound := fun _ => C') (s := Set.univ) Filter.univ_mem
    (Eventually.of_forall fun y =>
      ((smooth hφ).continuous.comp (by fun_prop)).aestronglyMeasurable)
    (integrable_comp_gam (smooth hφ).continuous hC a x)
    (hcont'.comp (by fun_prop)).aestronglyMeasurable
    (ae_of_all _ fun z y _ => by simpa using hC' _) (integrable_const C')
    (ae_of_all _ fun z y _ => by
      have := (hasFDerivAt_of (smooth hφ) (y - a • z)).comp y
        ((hasFDerivAt_id y).sub_const (a • z))
      exact (this : HasFDerivAt (fun x => φ (x - a • z)) _ y).congr_fderiv (by simp))

lemma fderiv_heatRd_apply (hφ : φ ∈ A₀ d) (a : ℝ) (x y : Fin d → ℝ) :
    fderiv ℝ (heatRd a φ) x y = heatRd a (fun w => fderiv ℝ φ w y) x := by
  obtain ⟨C', hC'⟩ := ((smooth hφ).continuous_fderiv (by simp)).bounded_above_of_compact_support
    (HasCompactSupport.fderiv (𝕜 := ℝ) (cs hφ))
  rw [(hasFDerivAt_heatRd hφ a x).fderiv, ContinuousLinearMap.integral_apply]
  · rfl
  · exact Integrable.of_bound (C := C')
      (((smooth hφ).continuous_fderiv (by simp)).comp (by fun_prop)).aestronglyMeasurable
      (ae_of_all _ fun z => hC' _)

theorem heatRd_smooth (hφ : φ ∈ A₀ d) (a : ℝ) : Sm (heatRd a φ) := by
  show ContDiff ℝ (⊤ : ℕ∞) _
  rw [contDiff_infty]
  intro n
  induction n generalizing φ with
  | zero =>
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun x =>
      (hasFDerivAt_heatRd hφ a x).continuousAt)
  | succ n ih =>
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hasFDerivAt_heatRd hφ a x).differentiableAt, by simp, fun y => ?_⟩
    have : (fun x => fderiv ℝ (heatRd a φ) x y) = heatRd a (fun w => fderiv ℝ φ w y) :=
      funext fun x => fderiv_heatRd_apply hφ a x y
    rw [this]
    exact ih (fderiv_apply_mem hφ y)

theorem dd_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) (i : Fin d) :
    dd i (heatRd a φ) = heatRd a (dd i φ) :=
  funext fun x => fderiv_heatRd_apply hφ a x _

theorem Lf_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) : Lf (heatRd a φ) = heatRd a (Lf φ) := by
  funext x
  have h1 : ∀ i, dd i (dd i (heatRd a φ)) = heatRd a (dd i (dd i φ)) := fun i => by
    rw [dd_heatRd hφ a i, dd_heatRd (dd_mem hφ i) a i]
  have hint : ∀ i, Integrable (fun z => dd i (dd i φ) (x - a • z)) (gam d) := fun i => by
    obtain ⟨C, hC⟩ := bdd_of_A₀ (dd_mem (dd_mem hφ i) i)
    exact integrable_comp_gam (smooth (dd_mem (dd_mem hφ i) i)).continuous hC a x
  simp only [Lf, h1]
  unfold heatRd
  show _ = ∫ z, ∑ i, dd i (dd i φ) (x - a • z) ∂(gam d)
  rw [integral_finsetSum _ (fun i _ => hint i)]

theorem abs_heatRd_le {C : ℝ} (hC : ∀ x, |φ x| ≤ C) (a : ℝ) (x : Fin d → ℝ) :
    |heatRd a φ x| ≤ C := abs_heat_le hC a x

theorem integrable_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) : Integrable (heatRd a φ) volume :=
  integrable_heat_gen (smooth hφ).continuous (integrable_of hφ) a

theorem memLp_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) : MemLp (heatRd a φ) 2 volume := by
  obtain ⟨C, hC⟩ := bdd_of_A₀ hφ
  have hint := integrable_heatRd hφ a
  rw [memLp_two_iff_integrable_sq hint.aestronglyMeasurable]
  refine Integrable.mono' (hint.norm.const_mul C) (hint.aestronglyMeasurable.pow 2)
    (ae_of_all _ fun x => ?_)
  have h0 := abs_heat_le hC a x
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  nlinarith [abs_nonneg (heatRd a φ x), sq_abs (heatRd a φ x)]

theorem integral_heatRd (hφ : φ ∈ A₀ d) (a : ℝ) : ∫ x, heatRd a φ x = ∫ x, φ x :=
  integral_heat_gen (smooth hφ).continuous (integrable_of hφ) a

theorem coeFn_heatL2 (hφ : φ ∈ A₀ d) (a : ℝ) :
    (heatL2 φ a : (Fin d → ℝ) → ℝ) =ᵐ[volume] heatRd a φ := by
  have h := memLp_heatRd hφ a
  simp only [heatL2, h, ↓reduceDIte]
  exact MemLp.coeFn_toLp _

/-- `heatL2 φ 0` is the `L²` class of `φ`. -/
theorem heatL2_zero (hφ : φ ∈ A₀ d) : heatL2 φ 0 = (memLp_of hφ 2).toLp φ := by
  refine Lp.ext ?_
  filter_upwards [coeFn_heatL2 hφ 0, (memLp_of hφ 2).coeFn_toLp] with x h1 h2
  rw [h1, h2, heatRd_zero]

/-- symmetry of Gaussian smoothing. -/
theorem integral_mul_heatRd_comm (hφ : φ ∈ A₀ d) (hψ : ψ ∈ A₀ d) (a : ℝ) :
    ∫ x, ψ x * heatRd a φ x = ∫ x, φ x * heatRd a ψ x := by
  obtain ⟨C, hC⟩ := bdd_of_A₀ hφ
  obtain ⟨D, hD⟩ := bdd_of_A₀ hψ
  have hφc := (smooth hφ).continuous
  have hψc := (smooth hψ).continuous
  have h1 : ∀ x, ψ x * heatRd a φ x = ∫ z, ψ x * φ (x - a • z) ∂(gam d) := fun x => by
    unfold heatRd; rw [integral_const_mul]
  have h2 : ∀ y, φ y * heatRd a ψ y = ∫ z, φ y * ψ (y + a • z) ∂(gam d) := fun y => by
    unfold heatRd
    rw [← integral_const_mul, ← integral_gam_neg (fun z => φ y * ψ (y - a • z))]
    simp
  simp only [h1, h2]
  have hint1 : Integrable (Function.uncurry fun (x z : Fin d → ℝ) => ψ x * φ (x - a • z))
      (volume.prod (gam d)) := by
    refine Integrable.mono' ((((integrable_of hψ).norm).comp_fst (gam d)).const_mul C)
      ((hψc.comp continuous_fst).mul (hφc.comp (by fun_prop))).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    simp only [Function.uncurry, norm_mul, Real.norm_eq_abs]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg _)
  have hint2 : Integrable (Function.uncurry fun (z y : Fin d → ℝ) => φ y * ψ (y + a • z))
      ((gam d).prod volume) := by
    refine Integrable.mono' ((((integrable_of hφ).norm).comp_snd (gam d)).const_mul D)
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

lemma norm_heatL2_sq (hφ : φ ∈ A₀ d) (b : ℝ) : ‖heatL2 φ b‖ ^ 2 = ∫ x, heatRd b φ x ^ 2 := by
  have h := memLp_heatRd hφ b
  simp only [heatL2, h, ↓reduceDIte]
  exact norm_sq_toLp h

lemma integrable_sq_A₀ (hφ : φ ∈ A₀ d) : Integrable (fun y => φ y ^ 2) volume :=
  (integrable_of (mul_mem hφ hφ)).congr (ae_of_all _ fun y => by simp [pow_two])

lemma integral_sq_heat_le (hφ : φ ∈ A₀ d) (a : ℝ) : ∫ x, heatRd a φ x ^ 2 ≤ ∫ x, φ x ^ 2 := by
  obtain ⟨C, hC⟩ := bdd_of_A₀ hφ
  have hc := (smooth hφ).continuous
  calc ∫ x, heatRd a φ x ^ 2 ≤ ∫ x, heatRd a (fun y => φ y ^ 2) x :=
        integral_mono (memLp_heatRd hφ a).integrable_sq
          (integrable_heat_gen (hc.pow 2) (integrable_sq_A₀ hφ) a) fun x => sq_heat_le hc hC a x
    _ = ∫ x, φ x ^ 2 := integral_heat_gen (hc.pow 2) (integrable_sq_A₀ hφ) a

/-- contraction in `L²` (Jensen + translation invariance). -/
theorem norm_heatL2_le (hφ : φ ∈ A₀ d) (a : ℝ) : ‖heatL2 φ a‖ ≤ ‖heatL2 φ 0‖ := by
  have h0 : ‖heatL2 φ 0‖ ^ 2 = ∫ x, φ x ^ 2 := by
    rw [norm_heatL2_sq hφ 0]; simp only [heatRd_zero]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
    (by rw [norm_heatL2_sq hφ a, h0]; exact integral_sq_heat_le hφ a)

lemma ae_gam_affine {a : ℝ} (ha : a ≠ 0) (x : Fin d → ℝ) {P : (Fin d → ℝ) → Prop}
    (h : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), P y) : ∀ᵐ z ∂(gam d), P (x - a • z) := by
  have hq : Measure.QuasiMeasurePreserving (fun z : Fin d → ℝ => x - a • z) volume volume :=
    (((volume : Measure (Fin d → ℝ)).measurePreserving_sub_left x).quasiMeasurePreserving).comp
      (Measure.quasiMeasurePreserving_smul (volume : Measure (Fin d → ℝ)) ha)
  exact gam_absolutelyContinuous.ae_le (hq.ae h)

/-- `S11` ingredient: `heatRd a (uₙ) → 1` pointwise for `a ≠ 0` if `uₙ → 1` a.e. with `|uₙ| ≤ 1` a.e. -/
theorem heatRd_tendsto_one {a : ℝ} (ha : a ≠ 0) {u : ℕ → (Fin d → ℝ) → ℝ} (hmeas : ∀ n, Measurable (u n))
    (hle : ∀ n, ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), |u n y| ≤ 1)
    (hlim : ∀ᵐ y ∂(volume : Measure (Fin d → ℝ)), Tendsto (fun n => u n y) atTop (𝓝 1))
    (x : Fin d → ℝ) : Tendsto (fun n => heatRd a (u n) x) atTop (𝓝 1) := by
  have h1 : ∫ z, (1:ℝ) ∂(gam d) = 1 := by simp
  rw [← h1]
  refine tendsto_integral_of_dominated_convergence (fun _ => (1:ℝ))
    (fun n => ((hmeas n).comp (by fun_prop)).aestronglyMeasurable) (integrable_const _)
    (fun n => ?_) ?_
  · filter_upwards [ae_gam_affine ha x (hle n)] with z hz
    simpa using hz
  · filter_upwards [ae_gam_affine ha x hlim] with z hz using hz

/-- `S10` ingredient: the smoothed test function tends to `0` in `L²` as the scale `a → ∞`
(`|heatRd a φ| ≤ ‖φ‖₁ (2π a²)^{-d/2}`). -/
theorem tendsto_heatL2_zero (hφ : φ ∈ A₀ d) (hd : 1 ≤ d) :
    Tendsto (fun a : ℝ => heatL2 φ a) atTop (𝓝 0) := by
  have hc := (smooth hφ).continuous
  have hi := integrable_of hφ
  set I : ℝ := ∫ y, |φ y| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  set K : ℝ := ((√(2 * Real.pi))⁻¹) ^ d with hK
  have hK0 : 0 ≤ K := by positivity
  have hbound : ∀ a : ℝ, 0 < a → ‖heatL2 φ a‖ ^ 2 ≤ K * I * (a ^ d)⁻¹ * I := by
    intro a ha
    have ha' : a ≠ 0 := ha.ne'
    set M : ℝ := K * (|(a ^ d)⁻¹| * I) with hM
    have hM0 : 0 ≤ M := by positivity
    have habs : Continuous fun y => |φ y| := hc.abs
    have hiabs : Integrable (fun y => |φ y|) volume := hi.abs
    have hheat := integrable_heat_gen hc hi a
    have hheat_abs := integrable_heat_gen habs hiabs a
    calc ‖heatL2 φ a‖ ^ 2 = ∫ x, heatRd a φ x ^ 2 := norm_heatL2_sq hφ a
      _ ≤ ∫ x, M * ‖heatRd a φ x‖ :=
          integral_mono (memLp_heatRd hφ a).integrable_sq (hheat.norm.const_mul M) fun x => by
            have h1 := abs_heat_le_sup hi ha' x
            rw [Real.norm_eq_abs, ← sq_abs, pow_two]
            exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = M * ∫ x, ‖heatRd a φ x‖ := integral_const_mul _ _
      _ ≤ M * ∫ x, heatRd a (fun y => |φ y|) x := by
          refine mul_le_mul_of_nonneg_left (integral_mono hheat.norm hheat_abs fun x => ?_) hM0
          exact abs_heat_le_heat_abs a x
      _ = M * I := by rw [integral_heat_gen habs hiabs a]
      _ = K * I * (a ^ d)⁻¹ * I := by
          rw [hM, abs_of_nonneg (by positivity)]; ring
  have hlim : Tendsto (fun a : ℝ => K * I * (a ^ d)⁻¹ * I) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (α := ℝ) (by omega : d ≠ 0)))
    have := (h.const_mul (K * I)).mul_const I
    simpa using this
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hlim
  simp only [Real.sqrt_zero] at hsqrt
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hsqrt
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  exact Real.le_sqrt_of_sq_le (hbound a ha)

end MarkovTriple.BGL.LebesgueRd
