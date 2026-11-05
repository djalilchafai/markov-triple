import Mathlib
import MarkovTriple.Stochastic.SphereFeller
import MarkovTriple.Stochastic.FellerMeasurable
import MarkovTriple.BGL.Instances.SphereOpen.Basic

/-!
# Round 29 (O), part 2: the zonal `S³` Feller kernels do not charge `μZ`-null sets, at every starting point

For `t > 0` and `u ∈ L²(μZ)`, `P_t u = Σ_k e^{-k(k+2)t} ⟨e_k, u⟩ e_k` has a continuous representative `G` with the SUP-norm bound
`‖G‖_∞ ≤ C_t ‖u‖_{L²}`, `C_t = Σ_k e^{-tk}(k+1)` (since `|U_k| ≤ k+1`).  Hence `f ↦ ∫ f dκ_t(x,·)` is `L²(μZ)`-bounded at EVERY `x`,
so `κ_t(x, ·) ≪ μZ` for every `x ∈ [-1,1]` (not only a.e.); in particular the two poles `{±1}` (`μZ`-null) are `κ_t(x,·)`-null.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace

namespace MarkovTriple.Stochastic.R29

open MarkovTriple.BGL MarkovTriple.BGL.Instances.Sphere MarkovTriple.Stochastic MarkovTriple.Stochastic.Sphere

/-- the sup-norm constant `C_t = Σ_k e^{-tk}(k+1)` -/
noncomputable def Ct (t : ℝ≥0) : ℝ := ∑' k : ℕ, Real.exp (-(t : ℝ) * k) * ((k : ℝ) + 1)

theorem smoothing_sup {t : ℝ≥0} (ht : 0 < t) (u : Lp ℝ 2 μZ) :
    ∃ G : C(Zon, ℝ), ((PZ t u : Lp ℝ 2 μZ) : Zon → ℝ) =ᵐ[μZ] G ∧ ‖G‖ ≤ ‖u‖ * Ct t := by
  set w : Lp ℝ 2 μZ := PZ t u with hw
  set c : ℕ → ℝ := fun k => inner ℝ (eZ k) w with hc
  have htr : (0 : ℝ) < t := by exact_mod_cast ht
  have hck : ∀ k, c k = Real.exp (-lamZ k * t) * inner ℝ (eZ k) u := by
    intro k
    simp only [hc, hw]
    rw [← inner_PZ, semigroup_eZ, real_inner_smul_left]
  have hbound : ∀ k, |c k| ≤ ‖u‖ * Real.exp (-t * k) := by
    intro k
    rw [hck, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h1 : |inner ℝ (eZ k) u| ≤ ‖u‖ := by
      have := abs_real_inner_le_norm (eZ k) u
      rwa [norm_eZ, one_mul] at this
    have h2 : Real.exp (-lamZ k * t) ≤ Real.exp (-t * k) := by
      apply Real.exp_le_exp.2
      have : (k : ℝ) ≤ lamZ k := by
        unfold lamZ
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        nlinarith
      nlinarith
    calc Real.exp (-lamZ k * t) * |inner ℝ (eZ k) u|
        ≤ Real.exp (-t * k) * ‖u‖ := mul_le_mul h2 h1 (abs_nonneg _) (Real.exp_pos _).le
      _ = _ := by ring
  let UC : ℕ → C(Zon, ℝ) := fun k => ⟨UZ k, continuous_of_mem (UZ_mem k)⟩
  have hUCn : ∀ k, ‖UC k‖ ≤ k + 1 := by
    intro k
    refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
    rw [Real.norm_eq_abs]
    show |UZ k x| ≤ _
    exact abs_Utheta_le k _
  have hs0 : Summable fun k : ℕ => Real.exp (-t * k) * ((k : ℝ) + 1) := by
    have h1 := Real.summable_pow_mul_exp_neg_nat_mul 1 htr
    have h0 := Real.summable_pow_mul_exp_neg_nat_mul 0 htr
    refine (h1.add h0).congr fun k => ?_
    simp only [pow_one, pow_zero, one_mul]; ring
  have hsumm : Summable fun k : ℕ => ‖u‖ * Real.exp (-t * k) * ((k : ℝ) + 1) :=
    (hs0.mul_left ‖u‖).congr fun k => by ring
  have hle : ∀ k, ‖c k • UC k‖ ≤ ‖u‖ * Real.exp (-t * k) * ((k : ℝ) + 1) := fun k => by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hbound k) (hUCn k) (norm_nonneg _) (by positivity)
  have hnorm : Summable fun k : ℕ => ‖c k • UC k‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hle hsumm
  have hsm : Summable fun k : ℕ => c k • UC k := Summable.of_norm hnorm
  obtain ⟨G, hG⟩ : ∃ G : C(Zon, ℝ), G = ∑' k : ℕ, c k • UC k := ⟨_, rfl⟩
  have hsum : HasSum (fun k : ℕ => c k • UC k) G := by rw [hG]; exact hsm.hasSum
  have hL := (ContinuousMap.toLp (E := ℝ) 2 μZ ℝ).hasSum hsum
  have hL2 : HasSum (fun k : ℕ => c k • eZ k) w := by
    have := bZ.hasSum_repr w
    simpa [bZ_apply, bZ.repr_apply_apply, hc] using this
  have hLw : HasSum (fun k : ℕ => c k • eZ k) (ContinuousMap.toLp (E := ℝ) 2 μZ ℝ G) := by
    have e : ∀ k : ℕ, ContinuousMap.toLp (E := ℝ) 2 μZ ℝ (c k • UC k) = c k • eZ k := by
      intro k
      rw [map_smul]
      congr 1
    have e' : (fun k : ℕ => ContinuousMap.toLp (E := ℝ) 2 μZ ℝ (c k • UC k)) =
        fun k : ℕ => c k • eZ k := funext e
    rw [← e']; exact hL
  have hwG : w = ContinuousMap.toLp (E := ℝ) 2 μZ ℝ G := hL2.unique hLw
  have hae : (w : Zon → ℝ) =ᵐ[μZ] G := by
    rw [hwG]; exact ContinuousMap.coeFn_toLp _ _
  refine ⟨G, hae, ?_⟩
  rw [hG]
  calc ‖∑' k : ℕ, c k • UC k‖ ≤ ∑' k : ℕ, ‖c k • UC k‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' k : ℕ, ‖u‖ * Real.exp (-t * k) * ((k : ℝ) + 1) := hnorm.tsum_le_tsum hle hsumm
    _ = ‖u‖ * Ct t := by
      rw [Ct, ← tsum_mul_left]
      refine tsum_congr fun k => ?_
      ring_nf

/-- **Pointwise `L²` bound for the Feller kernels of the zonal sphere**: at EVERY `x`, `|∫ f dκ_t(x,·)| ≤ C_t ‖[f]‖_{L²(μZ)}`. -/
theorem sphere_kernel_bound {t : ℝ≥0} (ht : 0 < t) (x : Zon) (f : C(Zon, ℝ)) :
    |∫ y, f y ∂(fellerKernel sphere_isFeller t x)| ≤ ‖clsC μZ f‖ * Ct t := by
  rw [integral_fellerKernel]
  obtain ⟨G, hG, hn⟩ := smoothing_sup ht (clsC μZ f)
  have e1 : (fellerOp sphere_isFeller t f : Zon → ℝ) =ᵐ[μZ] G := by
    have h1 := fellerOp_ae sphere_isFeller t f
    exact (h1.symm.trans hG)
  have e2 : (fellerOp sphere_isFeller t f : Zon → ℝ) = G :=
    ((fellerOp sphere_isFeller t f).continuous.ae_eq_iff_eq μZ G.continuous).1 e1
  rw [e2]
  calc |G x| = ‖G x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖G‖ := G.norm_coe_le_norm x
    _ ≤ _ := hn

lemma norm_clsC_sq_le {U : Set Zon} (hU : IsOpen U) (f : C(Zon, ℝ)) (h0 : ∀ x, f x ∈ Icc (0 : ℝ) 1)
    (hf : ∀ x, x ∉ U → f x = 0) : ‖clsC μZ f‖ ^ 2 ≤ (μZ U).toReal := by
  have h1 : ‖clsC μZ f‖ ^ 2 = ∫ x, f x * f x ∂μZ := by
    rw [← real_inner_self_eq_norm_sq, L2_inner_eq]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_clsC (μ := μZ) f] with x hx
    rw [hx]
  rw [h1]
  have hint : Integrable (fun x => f x * f x) μZ := (f.continuous.mul f.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  have hle : ∀ x, f x * f x ≤ U.indicator (fun _ => (1 : ℝ)) x := by
    intro x
    by_cases hx : x ∈ U
    · simp only [hx, Set.indicator_of_mem]
      nlinarith [(h0 x).1, (h0 x).2]
    · simp [hx, hf x hx]
  calc ∫ x, f x * f x ∂μZ ≤ ∫ x, U.indicator (fun _ => (1 : ℝ)) x ∂μZ :=
        integral_mono hint ((integrable_const (1 : ℝ)).indicator hU.measurableSet) hle
    _ = (μZ U).toReal := by
        rw [integral_indicator hU.measurableSet]
        simp [Measure.real]

/-- the Feller kernel of the zonal sphere does not charge a `μZ`-null compact set, at every starting point (`t > 0`). -/
theorem sphere_kernel_compact_null {t : ℝ≥0} (ht : 0 < t) (x : Zon) {K : Set Zon} (hK : IsCompact K)
    (h0 : μZ K = 0) : fellerKernel sphere_isFeller t x K = 0 := by
  have hfin : fellerKernel sphere_isFeller t x K ≠ ⊤ := measure_ne_top _ _
  suffices hs : (fellerKernel sphere_isFeller t x K).toReal = 0 by
    exact (ENNReal.toReal_eq_zero_iff _).1 hs |>.resolve_right hfin
  have hCt : 0 ≤ Ct t := tsum_nonneg fun k => by positivity
  refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) ENNReal.toReal_nonneg
  rw [zero_add]
  -- choose an open neighbourhood of small measure
  set δ : ℝ := (ε / (Ct t + 1)) ^ 2 with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨U, hKU, hUo, hUm⟩ : ∃ U, K ⊆ U ∧ IsOpen U ∧ μZ U < ENNReal.ofReal δ := by
    have : μZ K < ENNReal.ofReal δ := by rw [h0]; exact ENNReal.ofReal_pos.2 hδpos
    exact Set.exists_isOpen_lt_of_lt K _ this
  obtain ⟨f, hfK, hfU, hf01⟩ := exists_continuous_one_zero_of_isCompact hK hUo.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.2 hKU)
  have hfU' : ∀ y, y ∉ U → f y = 0 := fun y hy => hfU hy
  have hb := sphere_kernel_bound ht x f
  have hsq := norm_clsC_sq_le hUo f hf01.2 hfU'
  have hUreal : (μZ U).toReal ≤ δ := by
    have := (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hUm.le
    rwa [ENNReal.toReal_ofReal hδpos.le] at this
  have hnorm : ‖clsC μZ f‖ ≤ ε / (Ct t + 1) := by
    have h2 : ‖clsC μZ f‖ ^ 2 ≤ (ε / (Ct t + 1)) ^ 2 := hsq.trans (hUreal.trans (le_of_eq hδ))
    exact le_of_sq_le_sq h2 (by positivity)
  -- κ(K) ≤ ∫ f dκ
  have hKint : (fellerKernel sphere_isFeller t x K).toReal ≤ ∫ y, f y ∂(fellerKernel sphere_isFeller t x) := by
    have hi : Integrable (fun y => f y) (fellerKernel sphere_isFeller t x) :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc (fellerKernel sphere_isFeller t x K).toReal
        = ∫ y, K.indicator (fun _ => (1 : ℝ)) y ∂(fellerKernel sphere_isFeller t x) := by
          rw [integral_indicator hK.measurableSet]; simp [Measure.real]
      _ ≤ _ := integral_mono ((integrable_const (1 : ℝ)).indicator hK.measurableSet) hi (fun y => by
          by_cases hy : y ∈ K
          · simp [hy, hfK hy]
          · simp only [hy, Set.indicator_of_notMem, not_false_eq_true]; exact (hf01.2 y).1)
  calc (fellerKernel sphere_isFeller t x K).toReal ≤ ∫ y, f y ∂(fellerKernel sphere_isFeller t x) := hKint
    _ ≤ |∫ y, f y ∂(fellerKernel sphere_isFeller t x)| := le_abs_self _
    _ ≤ ‖clsC μZ f‖ * Ct t := hb
    _ ≤ (ε / (Ct t + 1)) * Ct t := mul_le_mul_of_nonneg_right hnorm hCt
    _ ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith

/-- **For every `x ∈ [-1,1]` and `t > 0`, `κ_t(x, ·) ≪ μZ`** (the Feller kernels of the zonal sphere do not charge null sets). -/
theorem sphere_kernel_ac {t : ℝ≥0} (ht : 0 < t) (x : Zon) : fellerKernel sphere_isFeller t x ≪ μZ := by
  intro A hA0
  obtain ⟨B, hAB, hBm, hB0⟩ := exists_measurable_superset_of_null hA0
  refine measure_mono_null hAB ?_
  rw [hBm.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  intro K hKB hK
  exact sphere_kernel_compact_null ht x hK (measure_mono_null hKB hB0)

end MarkovTriple.Stochastic.R29
