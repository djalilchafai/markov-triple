import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE2D

/-!
# E2: interior `H²` regularity (Evans §6.3.1 Thm 1, Steps 1–3)

`energy_bound`: the constant of `energy_step` is uniform in `|t| ≤ 1` (all coefficient constants depend only on the cut-off);
`interior_H2`: every `∂ᵢu` has a weak derivative in `L²_loc` in every direction (Step 3, `weakDeriv_of_local_dq`);
`interior_H2_sobolev`: `Sobolev 2 u`.
Statement: `STATEMENTS_R16_E2.md`, E2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

lemma integrable_sum_sq {F : Fin d → Rd d → ℝ} (hF : ∀ j, LocL2 (F j)) {ζ : Rd d → ℝ} (hζ : Continuous ζ)
    (hc : HasCompactSupport ζ) : Integrable (fun x => ∑ j, (ζ x * F j x) ^ 2) :=
  integrable_finsetSum _ fun j _ =>
    (integrable_cs_sq (hF j) (hζ.pow 2) (EllData.hcs_of_factor hc fun x hx => by simp [hx])).congr
      (Eventually.of_forall fun x => by simp only [Pi.pow_apply]; ring)

namespace EllData
variable (E : EllData d)

/-- uniform energy bound (Evans §6.3.1 Step 2): `∫ ζ² Σⱼ |D_t gⱼ|² ≤ C` for all `|t| ≤ 1`. -/
theorem energy_bound {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hh : LocL2 h) (hW : E.VeryWeakSol u h)
    (k : Fin d) {ζ : Rd d → ℝ} (hζ : Sm ζ) (hc : HasCompactSupport ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, |t| ≤ 1 → ∫ x, ∑ j, (ζ x * dq k t (g j) x) ^ 2 ≤ C := by
  classical
  set S : Set (Rd d) := Metric.cthickening 1 (tsupport ζ) with hS
  have hSc : IsCompact S := hc.cthickening
  have hTsub : ∀ x ∈ tsupport ζ, x ∈ S := fun x hx => Metric.self_subset_cthickening _ hx
  have hTS : ∀ t : ℝ, |t| ≤ 1 → ∀ x ∈ tsupport ζ, x + t • (Pi.single k 1 : Rd d) ∈ S := by
    intro t ht x hx
    refine Metric.mem_cthickening_of_dist_le _ x _ _ hx ?_
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_right (abs_nonneg _) (norm_single_le k)).trans ht
  have hSv : ∀ t : ℝ, |t| ≤ 1 → ∀ x, x ∈ Metric.cthickening |t| (tsupport ζ) → x ∈ S :=
    fun t ht x hx => Metric.cthickening_mono ht _ hx
  -- ellipticity, density, upper bounds on `S`
  obtain ⟨lam, hlam0, hlam⟩ := E.local_ellipticity hSc
  obtain ⟨m0, hm0, hm0S⟩ := E.exists_dens_lower hSc
  obtain ⟨Wb, hWb⟩ := hSc.exists_bound_of_continuousOn E.w_smooth.continuous.continuousOn
  obtain ⟨Λ0, hΛ00, hΛ0⟩ := E.local_upper hSc
  have hm : ∀ y ∈ S, E.Z * m0 ≤ E.w y := fun y hy => by
    have h1 := mul_le_mul_of_nonneg_left (hm0S y hy) E.Z_pos.le
    have h2 : E.Z * E.dens y = E.w y := by unfold EllData.dens; field_simp [E.Z_pos.ne']
    linarith
  have hWc : ∀ y ∈ S, E.w y ≤ max Wb 0 := fun y hy =>
    ((le_abs_self _).trans (by simpa using hWb y hy)).trans (le_max_left _ _)
  have hΛ : ∀ y ∈ S, ∀ (v : Rd d), ∑ i, ∑ j, E.a i j y * v i * v j ≤ max Λ0 0 * ∑ i, v i ^ 2 :=
    fun y hy v => (hΛ0 y hy v).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
      (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have hWΛ : 0 ≤ 2 * max Wb 0 * max Λ0 0 :=
    mul_nonneg (mul_nonneg zero_le_two (le_max_right _ _)) (le_max_right _ _)
  -- bounds for `ζ` and `∇ζ`
  obtain ⟨C0, hC0⟩ := hζ.continuous.bounded_above_of_compact_support hc
  have hdζ : ∀ j, ∃ Cj : ℝ, ∀ x, ‖pderiv ζ j x‖ ≤ Cj := fun j =>
    (hζ.pderiv j).continuous.bounded_above_of_compact_support (hc.fderiv_apply ℝ (Pi.single j 1))
  choose Cj hCj using hdζ
  set Bz : ℝ := |C0| + ∑ j, |Cj j| with hBz
  have hBz0 : 0 ≤ Bz := by positivity
  have hzb : ∀ x, |ζ x| ≤ Bz := fun x => by
    have := hC0 x
    rw [Real.norm_eq_abs] at this
    have h2 : 0 ≤ ∑ j, |Cj j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith [le_abs_self C0]
  have hzdb : ∀ j x, |pderiv ζ j x| ≤ Bz := fun j x => by
    have := hCj j x
    rw [Real.norm_eq_abs] at this
    have h2 : |Cj j| ≤ ∑ j, |Cj j| :=
      Finset.single_le_sum (f := fun j => |Cj j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
    linarith [le_abs_self (Cj j), abs_nonneg C0]
  -- the cut-off `χ = 1` on `S`
  obtain ⟨N0, hN0⟩ := exists_ball_of_compact hSc
  set χ : Rd d → ℝ := cut ((N0 : ℝ) + 1) with hχ
  have hχc : Continuous χ := (sm_cut _).continuous
  have hχs : HasCompactSupport χ := hcs_cut (by positivity)
  have hχ1 : ∀ x ∈ S, χ x = 1 := fun x hx =>
    cut_eq_one (by positivity) ((hN0 x hx).trans (by nlinarith [(Nat.cast_nonneg N0 : (0 : ℝ) ≤ N0)]))
  -- `L²` bound of the difference quotient of `u` on `supp χ`
  obtain ⟨C1, hC1, hC1b⟩ := dq_local_bound hu (hgL k) (hg k) hχs
  have hY0 : ∀ t : ℝ, |t| ≤ 1 → ∫ x, χ x ^ 2 * dq k t u x ^ 2 ≤ C1 ^ 2 := by
    intro t ht
    have hYm : MemLp (dq k t u) 2 (volume.restrict (tsupport χ)) := locL2_dq hu k t _ hχs
    have hI : Integrable (fun x => χ x ^ 2 * dq k t u x ^ 2) :=
      integrable_cs_sq (locL2_dq hu k t) (hχc.pow 2) (hcs_of_factor hχs fun x hx => by simp [hx])
    calc ∫ x, χ x ^ 2 * dq k t u x ^ 2 = ∫ x in tsupport χ, χ x ^ 2 * dq k t u x ^ 2 :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            simp [image_eq_zero_of_notMem_tsupport hx]).symm
      _ ≤ ∫ x in tsupport χ, dq k t u x ^ 2 := by
          refine integral_mono hI.integrableOn hYm.integrable_sq fun x => ?_
          have : χ x ^ 2 ≤ 1 := by
            have h0 := cut_nonneg ((N0 : ℝ) + 1) x
            have h1 := cut_le_one ((N0 : ℝ) + 1) x
            nlinarith
          exact mul_le_of_le_one_left (sq_nonneg _) this
      _ ≤ C1 ^ 2 := sq_le_of_eLpNorm hYm hC1 (hC1b t ht)
  -- Lipschitz constant of the coefficients `A = w a` on `S`
  have hÃ : ∀ i j, Sm (χ * (E.w * E.a i j)) := fun i j => (sm_cut _).mul (E.w_smooth.mul (E.a_smooth i j))
  have hÃc : ∀ i j, HasCompactSupport (χ * (E.w * E.a i j)) := fun i j => hχs.mul_right
  choose M hM0 hM using fun i j => abs_dq_le (hÃ i j) (hÃc i j) k
  set B : ℝ := ∑ i, ∑ j, M i j with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hM0 i j
  have hMB : ∀ i j, M i j ≤ B := fun i j =>
    (Finset.single_le_sum (f := fun j => M i j) (fun j _ => hM0 i j) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun i => ∑ j, M i j) (fun i _ => Finset.sum_nonneg fun j _ => hM0 i j)
        (Finset.mem_univ i))
  refine ⟨max (Cbound (lam * (E.Z * m0)) (B * Bz * d) (Bz ^ 2) (∫ x, χ x ^ 2 * ∑ i, g i x ^ 2)
      (∫ x, χ x ^ 2 * (h x * E.w x) ^ 2) (d * Bz ^ 2 * C1 ^ 2) (2 * max Wb 0 * max Λ0 0)) 0,
    le_max_right _ _, fun t ht => ?_⟩
  refine le_trans ?_ (le_max_left _ _)
  refine E.energy_step hu hg hgL hh hW k t hζ hc hSc (hTS t ht) (hSv t ht) hlam0 (mul_pos E.Z_pos hm0)
    hlam hm hWc hΛ hWΛ hB0 hBz0 hzb hzdb ?_ hχc hχs hχ1 (hY0 t ht)
  intro x hx i j
  have hxS := hTsub x hx
  have hxtS := hTS t ht x hx
  have e : dq k t (fun y => E.w y * E.a i j y) x = dq k t (χ * (E.w * E.a i j)) x := by
    simp only [dq, Pi.mul_apply, hχ1 x hxS, hχ1 _ hxtS, one_mul]
  rw [e]
  exact (hM i j t x).trans (hMB i j)

/-- **E2: interior `H²` regularity** (Evans §6.3.1 Thm 1): `u ∈ H¹_loc` a weak solution of `L u = h`, `h ∈ L²_loc`,
then every `∂ᵢu` has a weak derivative in `L²_loc` in every direction. -/
theorem interior_H2 {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hh : LocL2 h) (hW : E.VeryWeakSol u h)
    (i k : Fin d) : ∃ G : Rd d → ℝ, LocL2 G ∧ WeakDeriv (g i) G k := by
  refine weakDeriv_of_local_dq (hgL i) k (h := fun n => 1 / ((n : ℝ) + 1)) (fun n => by positivity)
    tendsto_one_div_add_atTop_nhds_zero_nat fun K hK => ?_
  obtain ⟨N, hN⟩ := exists_ball_of_compact hK
  set ζ : Rd d → ℝ := cut ((N : ℝ) + 1) with hζdef
  have hζ : Sm ζ := sm_cut _
  have hζc : HasCompactSupport ζ := hcs_cut (by positivity)
  have hζ1 : ∀ x ∈ K, ζ x = 1 := fun x hx =>
    cut_eq_one (by positivity) ((hN x hx).trans (by nlinarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]))
  obtain ⟨C, hC0, hC⟩ := E.energy_bound hu hg hgL hh hW k hζ hζc
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, fun n => ?_⟩
  have hn : |(1 : ℝ) / ((n : ℝ) + 1)| ≤ 1 := by
    rw [abs_of_nonneg (by positivity)]
    exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
  set t : ℝ := 1 / ((n : ℝ) + 1) with ht
  have hXm : MemLp (dq k t (g i)) 2 (volume.restrict K) := locL2_dq (hgL i) k t K hK
  refine eLpNorm_le_of_sq hXm (Real.sqrt_nonneg _) ?_
  rw [Real.sq_sqrt hC0]
  have hIS := integrable_sum_sq (fun j => locL2_dq (hgL j) k t) hζ.continuous hζc
  calc ∫ x in K, dq k t (g i) x ^ 2
      ≤ ∫ x in K, ∑ j, (ζ x * dq k t (g j) x) ^ 2 := by
        refine setIntegral_mono_on hXm.integrable_sq hIS.integrableOn hK.measurableSet fun x hx => ?_
        have h0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, (ζ x * dq k t (g j) x) ^ 2 :=
          Finset.sum_nonneg fun j _ => sq_nonneg _
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hζ1 x hx] at *
        simp only [one_mul] at *
        linarith
    _ ≤ ∫ x, ∑ j, (ζ x * dq k t (g j) x) ^ 2 :=
        setIntegral_le_integral hIS (Eventually.of_forall fun x => Finset.sum_nonneg fun j _ => sq_nonneg _)
    _ ≤ C := hC t hn

/-- **E2** in the form `Sobolev 2 u`. -/
theorem interior_H2_sobolev {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hh : LocL2 h) (hW : E.VeryWeakSol u h) :
    Sobolev 2 u := by
  refine ⟨hu, fun i => ⟨g i, hg i, hgL i, fun k => ?_⟩⟩
  obtain ⟨G, hGL, hGw⟩ := E.interior_H2 hu hg hgL hh hW i k
  exact ⟨G, hGw, hGL⟩

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
