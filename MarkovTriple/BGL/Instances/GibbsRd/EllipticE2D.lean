import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticE2C

/-!
# E2, the uniform estimate for one fixed difference step (Evans §6.3.1 Thm 1, Step 2)

`energy_step`: for `|t| ≤ 1` and constants depending only on `ζ` and the coefficients,
`∫ ζ² Σⱼ |D_t gⱼ|² ≤ Cbound` — Evans' estimate `∫ ζ² |D_t Du|² ≤ C` (ellipticity, Young absorption).
Statement: `STATEMENTS_R16_E2.md`, E2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

lemma integrable_cs_sq {F c : Rd d → ℝ} (hF : LocL2 F) (hc : Continuous c) (hs : HasCompactSupport c) :
    Integrable (fun x => c x * F x ^ 2) :=
  (integrable_cs_mul_mul hF hF hc hs).congr (Eventually.of_forall fun x => by simp only; ring)

lemma pderiv_sq_self {ζ : Rd d → ℝ} (hζ : Sm ζ) (j : Fin d) (x : Rd d) :
    pderiv (ζ * ζ) j x = 2 * ζ x * pderiv ζ j x := by
  rw [pderiv_mul hζ hζ]; ring

/-- the explicit bound of `energy_step` -/
noncomputable def Cbound (a K1 K2 Gs H0 N0 WΛ : ℝ) : ℝ :=
  4 / a * (K1 * ((1 / (4 * (a / (8 * (K1 + 1)))) + 1) * Gs + N0) + (a / (16 * (K2 + 1))) * 8 * K2 * N0
      + H0 / (4 * (a / (16 * (K2 + 1)))) + WΛ * N0)

namespace EllData
variable (E : EllData d)

theorem energy_step {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hh : LocL2 h) (hW : E.VeryWeakSol u h)
    (k : Fin d) (t : ℝ) {ζ : Rd d → ℝ} (hζ : Sm ζ) (hc : HasCompactSupport ζ)
    {S : Set (Rd d)} (hSc : IsCompact S) (hTS : ∀ x ∈ tsupport ζ, x + t • (Pi.single k 1 : Rd d) ∈ S)
    (hSv : ∀ x, x ∈ Metric.cthickening |t| (tsupport ζ) → x ∈ S)
    {lam m Wc Λ : ℝ} (hlam0 : 0 < lam) (hm0 : 0 < m)
    (hlam : ∀ y ∈ S, ∀ ξ : Rd d, lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, E.a i j y * ξ i * ξ j)
    (hm : ∀ y ∈ S, m ≤ E.w y) (hWc : ∀ y ∈ S, E.w y ≤ Wc)
    (hΛ : ∀ y ∈ S, ∀ (v : Rd d), ∑ i, ∑ j, E.a i j y * v i * v j ≤ Λ * ∑ i, v i ^ 2)
    (hWΛ : 0 ≤ 2 * Wc * Λ)
    {Bz B : ℝ} (hB0 : 0 ≤ B) (hBz0 : 0 ≤ Bz) (hzb : ∀ x, |ζ x| ≤ Bz) (hzdb : ∀ j x, |pderiv ζ j x| ≤ Bz)
    (hDm : ∀ x ∈ tsupport ζ, ∀ i j, |dq k t (fun y => E.w y * E.a i j y) x| ≤ B)
    {χ : Rd d → ℝ} (hχc : Continuous χ) (hχs : HasCompactSupport χ) (hχ1 : ∀ x ∈ S, χ x = 1)
    {Y0 : ℝ} (hY0 : ∫ x, χ x ^ 2 * dq k t u x ^ 2 ≤ Y0) :
    ∫ x, ∑ j, (ζ x * dq k t (g j) x) ^ 2 ≤
      Cbound (lam * m) (B * Bz * d) (Bz ^ 2) (∫ x, χ x ^ 2 * ∑ i, g i x ^ 2)
        (∫ x, χ x ^ 2 * (h x * E.w x) ^ 2) (d * Bz ^ 2 * Y0) (2 * Wc * Λ) := by
  classical
  set e : Rd d := Pi.single k 1 with he
  have hid := E.dq_identity hu hg hgL hh hW k t hζ hc
  have hψS : Sm (ζ * ζ) := hζ.mul hζ
  have hψc : HasCompactSupport (ζ * ζ) := hc.mul_right
  have hcw : Continuous E.w := E.w_smooth.continuous
  have hζc : Continuous ζ := hζ.continuous
  have hζdc : ∀ j, Continuous (pderiv ζ j) := fun j => (hζ.pderiv j).continuous
  have hζd : ∀ j, HasCompactSupport (pderiv ζ j) := fun j => hc.fderiv_apply ℝ (Pi.single j 1)
  have hYL : LocL2 (dq k t u) := locL2_dq hu k t
  have hXL : ∀ i, LocL2 (dq k t (g i)) := fun i => locL2_dq (hgL i) k t
  have hTsub : ∀ x ∈ tsupport ζ, x ∈ S := fun x hx => hSv x (Metric.self_subset_cthickening _ hx)
  -- the test-function pieces `Φⱼ`
  set Φj : Fin d → Rd d → ℝ := fun j x => (ζ * ζ) x * dq k t (g j) x + pderiv (ζ * ζ) j x * dq k t u x with hΦj
  have hΦjL : ∀ j, LocL2 (Φj j) := fun j =>
    ((hXL j).mul_continuous hψS.continuous).add (hYL.mul_continuous (hψS.pderiv j).continuous)
  have hΦjc : ∀ j, HasCompactSupport (Φj j) := fun j => by
    have h1 : HasCompactSupport (fun x => (ζ * ζ) x * dq k t (g j) x) := hψc.mul_right
    have h2 : HasCompactSupport (fun x => pderiv (ζ * ζ) j x * dq k t u x) :=
      (hψc.fderiv_apply ℝ (Pi.single j 1)).mul_right
    exact h1.add h2
  have hΦjm : ∀ j, MemLp (Φj j) 2 volume := fun j => memLp_of_locL2_cs (hΦjL j) (hΦjc j)
  -- vectors `ξ, η` and the two sums
  set P : ℝ := ∫ x, ∑ j, (ζ x * dq k t (g j) x) ^ 2 with hP
  set N : ℝ := ∫ x, ∑ j, (pderiv ζ j x * dq k t u x) ^ 2 with hN
  have IS : Integrable (fun x => ∑ j, (ζ x * dq k t (g j) x) ^ 2) :=
    integrable_finsetSum _ fun j _ => (integrable_cs_sq (hXL j) (hζc.pow 2) (hcs_of_factor hc fun x hx => by simp [hx])).congr
      (Eventually.of_forall fun x => by simp only [Pi.pow_apply]; ring)
  have IE : Integrable (fun x => ∑ j, (pderiv ζ j x * dq k t u x) ^ 2) :=
    integrable_finsetSum _ fun j _ => (integrable_cs_sq hYL ((hζdc j).pow 2) (hcs_of_factor (hζd j) fun x hx => by simp [hx])).congr
      (Eventually.of_forall fun x => by simp only [Pi.pow_apply]; ring)
  have hP0 : 0 ≤ P := integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hN0 : 0 ≤ N := integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _
  -- (a) bound for `N`
  have hIY : Integrable (fun x => χ x ^ 2 * dq k t u x ^ 2) :=
    integrable_cs_sq hYL (hχc.pow 2) (hcs_of_factor hχs fun x hx => by simp [hx])
  have hNle : N ≤ d * Bz ^ 2 * Y0 := by
    calc N ≤ ∫ x, ((d : ℝ) * Bz ^ 2) * (χ x ^ 2 * dq k t u x ^ 2) := by
          refine integral_mono IE (hIY.const_mul _) fun x => ?_
          by_cases hx : x ∈ tsupport ζ
          · rw [hχ1 x (hTsub x hx)]
            calc ∑ j, (pderiv ζ j x * dq k t u x) ^ 2 ≤ ∑ j : Fin d, Bz ^ 2 * dq k t u x ^ 2 :=
                  Finset.sum_le_sum fun j _ => by
                    rw [mul_pow]
                    exact mul_le_mul_of_nonneg_right (sq_le_sq' (abs_le.1 (hzdb j x)).1 (abs_le.1 (hzdb j x)).2)
                      (sq_nonneg _)
              _ = ((d : ℝ) * Bz ^ 2) * (1 ^ 2 * dq k t u x ^ 2) := by
                  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
          · simp only [pderiv_eq_zero_off hx, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              zero_pow, Finset.sum_const_zero]
            positivity
      _ = ((d : ℝ) * Bz ^ 2) * ∫ x, χ x ^ 2 * dq k t u x ^ 2 := integral_const_mul _ _
      _ ≤ d * Bz ^ 2 * Y0 := mul_le_mul_of_nonneg_left hY0 (by positivity)
  -- pointwise rewriting of the integrands
  have hMpt : ∀ x, ∑ i, ∑ j, (E.w (x + t • e) * E.a i j (x + t • e)) * dq k t (g i) x * Φj j x =
      (∑ i, ∑ j, (E.w (x + t • e) * E.a i j (x + t • e)) * (ζ x * dq k t (g i) x) * (ζ x * dq k t (g j) x)) +
      2 * ∑ i, ∑ j, (E.w (x + t • e) * E.a i j (x + t • e)) * (ζ x * dq k t (g i) x) *
        (pderiv ζ j x * dq k t u x) := by
    intro x
    simp only [hΦj, pderiv_sq_self hζ, Pi.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  -- (c) lower bound for the leading term
  have IM : ∀ i j, Integrable (fun x => (E.w (x + t • e) * E.a i j (x + t • e)) * dq k t (g i) x * Φj j x) :=
    fun i j => by
      have hcA : Continuous (fun x => E.w (x + t • e) * E.a i j (x + t • e)) :=
        (E.w_smooth.continuous.comp (continuous_id.add continuous_const)).mul
          ((E.a_smooth i j).continuous.comp (continuous_id.add continuous_const))
      exact integrable_locL2_mul_cs ((hXL i).mul_continuous hcA) (hΦjm j) (hΦjc j)
  have hLow : (lam * m / 2) * P - 2 * Wc * Λ * N ≤
      ∑ i, ∑ j, ∫ x, (E.w (x + t • e) * E.a i j (x + t • e)) * dq k t (g i) x * Φj j x := by
    have hsum : ∑ i, ∑ j, ∫ x, (E.w (x + t • e) * E.a i j (x + t • e)) * dq k t (g i) x * Φj j x =
        ∫ x, ∑ i, ∑ j, (E.w (x + t • e) * E.a i j (x + t • e)) * dq k t (g i) x * Φj j x := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => IM i j)]
      exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => IM i j).symm
    rw [hsum]
    have hlow : ∫ x, ((lam * m / 2) * ∑ j, (ζ x * dq k t (g j) x) ^ 2 -
        2 * Wc * Λ * ∑ j, (pderiv ζ j x * dq k t u x) ^ 2) = (lam * m / 2) * P - 2 * Wc * Λ * N := by
      rw [integral_sub (IS.const_mul _) (IE.const_mul _), integral_const_mul, integral_const_mul]
    rw [← hlow]
    refine integral_mono ((IS.const_mul _).sub (IE.const_mul _))
      (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => IM i j) fun x => ?_
    have hy : (x + t • e) ∈ S ∨ ((∀ i, ζ x * dq k t (g i) x = 0) ∧ ∀ j, pderiv ζ j x * dq k t u x = 0) := by
      by_cases hx : x ∈ tsupport ζ
      · exact Or.inl (hTS x hx)
      · exact Or.inr ⟨fun i => by simp [image_eq_zero_of_notMem_tsupport hx],
          fun j => by simp [pderiv_eq_zero_off hx]⟩
    have := E.pw_main hlam hm hWc hΛ hlam0.le (x + t • e) (fun i => ζ x * dq k t (g i) x)
      (fun j => pderiv ζ j x * dq k t u x) hy
    beta_reduce at this
    rw [hMpt x]
    simpa only [mul_assoc] using this
  -- (d) commutator term
  have hUp : ∀ ε : ℝ, 0 < ε → |∑ i, ∑ j, ∫ x, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x| ≤
      B * Bz * d * (ε * P + (1 / (4 * ε) + 1) * (∫ x, χ x ^ 2 * ∑ i, g i x ^ 2) + N) := by
    intro ε hε
    have ID : ∀ i j, Integrable (fun x => g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x) := fun i j => by
      have hdA : Continuous (dq k t (fun y => E.w y * E.a i j y)) :=
        (contDiff_dq (E.w_smooth.mul (E.a_smooth i j)) k t).continuous
      have := integrable_locL2_mul_cs ((hgL i).mul_continuous hdA) (hΦjm j) (hΦjc j)
      exact this.congr (Eventually.of_forall fun x => by simp only; ring)
    have hsum : ∑ i, ∑ j, ∫ x, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x =
        ∫ x, ∑ i, ∑ j, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => ID i j)]
      exact Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun j _ => ID i j).symm
    rw [hsum]
    have IG0 : Integrable (fun x => ∑ i, χ x ^ 2 * g i x ^ 2) :=
      integrable_finsetSum _ fun i _ => integrable_cs_sq (hgL i) (hχc.pow 2)
        (hcs_of_factor hχs fun x hx => by simp [hx])
    have IG : Integrable (fun x => χ x ^ 2 * ∑ i, g i x ^ 2) :=
      IG0.congr (Eventually.of_forall fun x => by simp only [Finset.mul_sum])
    have hA : Integrable (fun x => ε * ∑ j, (ζ x * dq k t (g j) x) ^ 2 +
        (1 / (4 * ε) + 1) * (χ x ^ 2 * ∑ i, g i x ^ 2)) := (IS.const_mul ε).add (IG.const_mul _)
    have hbd : Integrable (fun x => B * Bz * d * (ε * ∑ j, (ζ x * dq k t (g j) x) ^ 2 +
        (1 / (4 * ε) + 1) * (χ x ^ 2 * ∑ i, g i x ^ 2) + ∑ j, (pderiv ζ j x * dq k t u x) ^ 2)) :=
      (hA.add IE).const_mul _
    have h1 : ∫ x, (ε * ∑ j, (ζ x * dq k t (g j) x) ^ 2 +
        (1 / (4 * ε) + 1) * (χ x ^ 2 * ∑ i, g i x ^ 2)) =
        ε * P + (1 / (4 * ε) + 1) * (∫ x, χ x ^ 2 * ∑ i, g i x ^ 2) := by
      rw [integral_add (IS.const_mul ε) (IG.const_mul _), integral_const_mul, integral_const_mul]
    have hint : ∫ x, B * Bz * d * (ε * ∑ j, (ζ x * dq k t (g j) x) ^ 2 +
        (1 / (4 * ε) + 1) * (χ x ^ 2 * ∑ i, g i x ^ 2) + ∑ j, (pderiv ζ j x * dq k t u x) ^ 2) =
        B * Bz * d * (ε * P + (1 / (4 * ε) + 1) * (∫ x, χ x ^ 2 * ∑ i, g i x ^ 2) + N) := by
      rw [integral_const_mul, integral_add hA IE, h1]
    rw [← hint]
    have := norm_integral_le_of_norm_le (μ := volume)
      (f := fun x => ∑ i, ∑ j, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x) hbd
      (Eventually.of_forall fun x => ?_)
    · simpa only [Real.norm_eq_abs] using this
    rw [Real.norm_eq_abs]
    by_cases hζx : ζ x = 0
    · have h0 : ∀ i j, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x = 0 := fun i j => by
        simp [hΦj, hζx, pderiv_sq_self hζ]
      simp only [h0, Finset.sum_const_zero, abs_zero]
      positivity
    · have hxT : x ∈ tsupport ζ := subset_tsupport ζ hζx
      have hpw := pw_R2 (fun i => g i x) (fun j => ζ x * dq k t (g j) x) (fun j => pderiv ζ j x * dq k t u x)
        (fun i j => dq k t (fun y => E.w y * E.a i j y) x) (ζ x) B Bz ε hε hB0 hBz0
        (fun _ i j => hDm x hxT i j) (hzb x)
      have e : ∑ i, ∑ j, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x =
          ∑ i, ∑ j, g i x * dq k t (fun y => E.w y * E.a i j y) x *
            (ζ x * (ζ x * dq k t (g j) x) + 2 * ζ x * (pderiv ζ j x * dq k t u x)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [hΦj, pderiv_sq_self hζ, Pi.mul_apply]; ring
      rw [e, hχ1 x (hTsub x hxT)]
      simpa only [one_pow, one_mul] using hpw
  -- (e) right-hand side
  have hR1 : ∀ ε : ℝ, 0 < ε → (∫ x, h x * dq k (-t) (fun y => (ζ * ζ) y * dq k t u y) x * E.w x) ≤
      ε * (2 * Bz ^ 2 * P + 8 * Bz ^ 2 * N) + (∫ x, χ x ^ 2 * (h x * E.w x) ^ 2) / (4 * ε) := by
    intro ε hε
    set Φ : Rd d → ℝ := fun y => (ζ * ζ) y * dq k t u y with hΦ
    have hΦL : LocL2 Φ := hYL.mul_continuous hψS.continuous
    have hΦc : HasCompactSupport Φ := hψc.mul_right
    have hΦm : MemLp Φ 2 volume := memLp_of_locL2_cs hΦL hΦc
    have hΦw : WeakDeriv Φ (Φj k) k := (weakDeriv_dq (hg k) k t).smooth_mul hψS
    have hvm : MemLp (dq k (-t) Φ) 2 volume := memLp_dq hΦm k (-t)
    set F : Rd d → ℝ := S.indicator (fun x => h x * E.w x) with hF
    have hFL : LocL2 (fun x => h x * E.w x) :=
      (hh.mul_continuous hcw).congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    have hFm : MemLp F 2 volume := hFL.memLp_indicator hSc
    have hvS : ∀ x, x ∉ S → dq k (-t) Φ x = 0 := by
      intro x hx
      have hxT : x ∉ tsupport ζ := fun h' => hx (hTsub x h')
      have h0 : Φ x = 0 := by simp [hΦ, image_eq_zero_of_notMem_tsupport hxT]
      have h1 : Φ (x + (-t) • e) = 0 := by
        by_contra hne
        have hz : ζ (x + (-t) • e) ≠ 0 := by
          intro h'; apply hne; simp only [hΦ, Pi.mul_apply, h', mul_zero, zero_mul]
        have hmem : x + (-t) • e ∈ tsupport ζ := subset_tsupport ζ hz
        apply hx; apply hSv
        refine Metric.mem_cthickening_of_dist_le x (x + (-t) • e) |t| _ hmem ?_
        rw [dist_eq_norm, show x - (x + (-t) • e) = t • e by rw [sub_add_cancel_left, neg_smul, neg_neg],
          norm_smul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (norm_single_le k)
      simp only [dq]; rw [h1, h0]; simp
    have hR : ∫ x, h x * dq k (-t) Φ x * E.w x = ∫ x, F x * dq k (-t) Φ x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ S
      · simp only [hF, Set.indicator_of_mem hx]; ring
      · simp [hF, Set.indicator_of_notMem hx, hvS x hx]
    have hCS := abs_integral_mul_le hFm hvm
    have hnorm : (eLpNorm (dq k (-t) Φ) 2 volume).toReal ≤ (eLpNorm (Φj k) 2 volume).toReal :=
      ENNReal.toReal_mono (hΦjm k).eLpNorm_ne_top (eLpNorm_dq_le hΦm (hΦjm k) hΦw (-t))
    set nF := (eLpNorm F 2 volume).toReal with hnF
    set nΦ := (eLpNorm (Φj k) 2 volume).toReal with hnΦ
    have hnF0 : 0 ≤ nF := ENNReal.toReal_nonneg
    have hnΦ0 : 0 ≤ nΦ := ENNReal.toReal_nonneg
    have hIH : Integrable (fun x => χ x ^ 2 * (h x * E.w x) ^ 2) :=
      integrable_cs_sq hFL (hχc.pow 2) (hcs_of_factor hχs fun x hx => by simp [hx])
    have hF2 : nF ^ 2 ≤ ∫ x, χ x ^ 2 * (h x * E.w x) ^ 2 := by
      rw [← sq_integral_eq hFm]
      refine integral_mono hFm.integrable_sq hIH fun x => ?_
      by_cases hx : x ∈ S
      · simp only [hF, Set.indicator_of_mem hx, hχ1 x hx]; simp
      · have h0 : F x = 0 := by simp [hF, Set.indicator_of_notMem hx]
        show F x ^ 2 ≤ χ x ^ 2 * (h x * E.w x) ^ 2
        rw [h0, zero_pow two_ne_zero]
        positivity
    have hΦ2 : nΦ ^ 2 ≤ 2 * Bz ^ 2 * P + 8 * Bz ^ 2 * N := by
      rw [← sq_integral_eq (hΦjm k)]
      have hI : Integrable (fun x => 2 * Bz ^ 2 * ∑ j, (ζ x * dq k t (g j) x) ^ 2 +
          8 * Bz ^ 2 * ∑ j, (pderiv ζ j x * dq k t u x) ^ 2) := (IS.const_mul _).add (IE.const_mul _)
      have hint : ∫ x, (2 * Bz ^ 2 * ∑ j, (ζ x * dq k t (g j) x) ^ 2 +
          8 * Bz ^ 2 * ∑ j, (pderiv ζ j x * dq k t u x) ^ 2) = 2 * Bz ^ 2 * P + 8 * Bz ^ 2 * N := by
        rw [integral_add (IS.const_mul _) (IE.const_mul _), integral_const_mul, integral_const_mul]
      rw [← hint]
      refine integral_mono (hΦjm k).integrable_sq hI fun x => ?_
      have hz2 : ζ x ^ 2 ≤ Bz ^ 2 := sq_le_sq' (abs_le.1 (hzb x)).1 (abs_le.1 (hzb x)).2
      have hk1 : (ζ x * dq k t (g k) x) ^ 2 ≤ ∑ j, (ζ x * dq k t (g j) x) ^ 2 :=
        Finset.single_le_sum (f := fun j => (ζ x * dq k t (g j) x) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k)
      have hk2 : (pderiv ζ k x * dq k t u x) ^ 2 ≤ ∑ j, (pderiv ζ j x * dq k t u x) ^ 2 :=
        Finset.single_le_sum (f := fun j => (pderiv ζ j x * dq k t u x) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k)
      have e : Φj k x = ζ x * (ζ x * dq k t (g k) x) + 2 * (ζ x * (pderiv ζ k x * dq k t u x)) := by
        simp only [hΦj, pderiv_sq_self hζ, Pi.mul_apply]; ring
      rw [e]
      have a1 : (ζ x * (ζ x * dq k t (g k) x)) ^ 2 ≤ Bz ^ 2 * (ζ x * dq k t (g k) x) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right hz2 (sq_nonneg _)
      have a2 : (ζ x * (pderiv ζ k x * dq k t u x)) ^ 2 ≤ Bz ^ 2 * (pderiv ζ k x * dq k t u x) ^ 2 := by
        rw [mul_pow]; exact mul_le_mul_of_nonneg_right hz2 (sq_nonneg _)
      nlinarith [sq_nonneg (ζ x * (ζ x * dq k t (g k) x) - 2 * (ζ x * (pderiv ζ k x * dq k t u x))),
        mul_le_mul_of_nonneg_left hk1 (sq_nonneg Bz), mul_le_mul_of_nonneg_left hk2 (sq_nonneg Bz)]
    have hamgm : nF * nΦ ≤ ε * nΦ ^ 2 + nF ^ 2 / (4 * ε) := by
      rw [← sub_nonneg]
      have : ε * nΦ ^ 2 + nF ^ 2 / (4 * ε) - nF * nΦ = (2 * ε * nΦ - nF) ^ 2 / (4 * ε) := by
        field_simp; ring
      rw [this]; positivity
    rw [hR]
    calc ∫ x, F x * dq k (-t) Φ x ≤ |∫ x, F x * dq k (-t) Φ x| := le_abs_self _
      _ ≤ nF * (eLpNorm (dq k (-t) Φ) 2 volume).toReal := hCS
      _ ≤ nF * nΦ := mul_le_mul_of_nonneg_left hnorm hnF0
      _ ≤ ε * nΦ ^ 2 + nF ^ 2 / (4 * ε) := hamgm
      _ ≤ _ := by
          have h1 : ε * nΦ ^ 2 ≤ ε * (2 * Bz ^ 2 * P + 8 * Bz ^ 2 * N) := mul_le_mul_of_nonneg_left hΦ2 hε.le
          have h2 : nF ^ 2 / (4 * ε) ≤ (∫ x, χ x ^ 2 * (h x * E.w x) ^ 2) / (4 * ε) :=
            div_le_div_of_nonneg_right hF2 (by positivity)
          linarith
  refine final_arith (R1 := ∫ x, h x * dq k (-t) (fun y => (ζ * ζ) y * dq k t u y) x * E.w x)
    (R2 := |∑ i, ∑ j, ∫ x, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x|)
    (mul_pos hlam0 hm0) (by positivity) (by positivity) hWΛ hNle hP0 ?_ hUp hR1
  have := neg_abs_le (∑ i, ∑ j, ∫ x, g i x * dq k t (fun y => E.w y * E.a i j y) x * Φj j x)
  linarith [hLow, hid]

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
