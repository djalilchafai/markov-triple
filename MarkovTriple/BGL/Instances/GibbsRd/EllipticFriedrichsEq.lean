import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsEst

/-!
# The equation satisfied by the mollified function (R16, Friedrichs step)

Statement E1 of `STATEMENTS_R16_Friedrichs.md`: if `∫ u · Pop b a = ∫ F · a` for the admissible test functions `a`, then for
the even mollifier `ρ`, `v = ρ ⋆ u`, `V = ρ ⋆ F` and `φ` smooth with compact support,
`∫ v · Pop b φ − ∫ u · T_ρ φ = ∫ V · φ`, `T_ρ φ = ρ ⋆ Pop b φ − Pop b (ρ ⋆ φ)` (test the equation with `a = ρ ⋆ φ` and use
`∫ u (ρ ⋆ f) = ∫ (ρ ⋆ u) f` for even `ρ`).  Friedrichs 1944; Hörmander ALPDO I proof of Thm 4.4.? / Lemma 17.1.?.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

section
variable {ρ f u : (Fin d → ℝ) → ℝ} {C₁ : ℝ}

/-- `∫ u (ρ ⋆ f) = ∫ (ρ ⋆ u) f` for even `ρ` (Fubini). -/
lemma integral_moll_swap (hk : FrKer ρ C₁) (heven : ∀ x, ρ (-x) = ρ x) (hu : LocallyIntegrable u)
    (hf : Continuous f) {R : ℝ} (hfR : ∀ y, R < ‖y‖ → f y = 0) :
    ∫ x, u x * moll ρ f x = ∫ y, moll ρ u y * f y := by
  have hfcs : HasCompactSupport f := hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R) fun y hy =>
    hfR y (by simpa using hy)
  obtain ⟨M, hM⟩ := hk.sm.continuous.bounded_above_of_compact_support hk.cs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set K : Set (Fin d → ℝ) := Metric.closedBall 0 (R + 1) with hK
  have huK : Integrable (K.indicator u) :=
    (hu.integrableOn_isCompact (isCompact_closedBall (0 : Fin d → ℝ) (R + 1))).integrable_indicator
      measurableSet_closedBall
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfcs
  have hdom : Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => ‖(K.indicator u) z.1‖ * (M * |f z.2|)) (volume.prod volume) :=
    huK.norm.mul_prod (hfi.abs.const_mul M)
  have hmeas : AEStronglyMeasurable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => u z.1 * (ρ (z.1 - z.2) * f z.2))
      (volume.prod volume) := by
    refine (hu.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).mul ?_
    exact ((hk.sm.continuous.comp (continuous_fst.sub continuous_snd)).mul (hf.comp continuous_snd)).aestronglyMeasurable
  have hint : Integrable (fun z : (Fin d → ℝ) × (Fin d → ℝ) => u z.1 * (ρ (z.1 - z.2) * f z.2)) (volume.prod volume) := by
    refine hdom.mono' hmeas (Eventually.of_forall fun z => ?_)
    by_cases h0 : ρ (z.1 - z.2) * f z.2 = 0
    · simp only [h0, mul_zero, norm_zero]; positivity
    · have h1 : ρ (z.1 - z.2) ≠ 0 := fun h => h0 (by simp [h])
      have h2 : f z.2 ≠ 0 := fun h => h0 (by simp [h])
      have hy : ‖z.2‖ ≤ R := by by_contra hlt; exact h2 (hfR _ (not_le.1 hlt))
      have hxy := hk.support _ h1
      have hx : z.1 ∈ K := by
        rw [hK, Metric.mem_closedBall, dist_zero_right]
        calc ‖z.1‖ = ‖(z.1 - z.2) + z.2‖ := by rw [sub_add_cancel]
          _ ≤ ‖z.1 - z.2‖ + ‖z.2‖ := norm_add_le _ _
          _ ≤ R + 1 := by linarith
      rw [Set.indicator_of_mem hx, norm_mul, norm_mul, Real.norm_eq_abs (ρ _), Real.norm_eq_abs (f _)]
      have : |ρ (z.1 - z.2)| ≤ M := by
        have := hM (z.1 - z.2); rwa [Real.norm_eq_abs] at this
      calc ‖u z.1‖ * (|ρ (z.1 - z.2)| * |f z.2|) ≤ ‖u z.1‖ * (M * |f z.2|) := by gcongr
        _ = _ := rfl
  have hswap := integral_integral_swap (μ := (volume : Measure (Fin d → ℝ))) (ν := volume)
    (f := fun x y => u x * (ρ (x - y) * f y)) hint
  have e1 : ∀ x, ∫ y, u x * (ρ (x - y) * f y) = u x * moll ρ f x := fun x => by
    rw [integral_const_mul, moll_eq]
  have e2 : ∀ y, ∫ x, u x * (ρ (x - y) * f y) = moll ρ u y * f y := fun y => by
    rw [moll_eq, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : ρ (y - x) = ρ (x - y) := by rw [← heven (x - y), neg_sub]
    simp only [this]; ring
  simp only [e1, e2] at hswap
  exact hswap


lemma tsupport_sub_of_zero_off {f : (Fin d → ℝ) → ℝ} {R : ℝ} (hf : ∀ y, R < ‖y‖ → f y = 0) :
    tsupport f ⊆ Metric.closedBall 0 R := by
  refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
  by_contra hno
  exact hy (hf y (by simpa using hno))

lemma pderiv_zero_off {f : (Fin d → ℝ) → ℝ} {R : ℝ} (hf : ∀ y, R < ‖y‖ → f y = 0) (i : Fin d) (y : Fin d → ℝ)
    (hy : R < ‖y‖) : pderiv f i y = 0 := by
  by_contra hne
  have h1 : fderiv ℝ f y ≠ 0 := fun h0 => hne (by simp [pderiv, h0])
  have := tsupport_sub_of_zero_off hf (support_fderiv_subset ℝ h1)
  simp at this; linarith

lemma Pop_zero_off {b : Fin d → Fin d → (Fin d → ℝ) → ℝ} {φ : (Fin d → ℝ) → ℝ} {R : ℝ}
    (hφ0 : ∀ y, R < ‖y‖ → φ y = 0) (y : Fin d → ℝ) (hy : R < ‖y‖) : Pop b φ y = 0 := by
  unfold Pop
  refine Finset.sum_eq_zero fun i _ => pderiv_zero_off (fun y' hy' => ?_) i y hy
  exact Finset.sum_eq_zero fun j _ => by simp [pderiv_zero_off hφ0 j y' hy']

lemma moll_zero_off (hk : FrKer ρ C₁) {φ : (Fin d → ℝ) → ℝ} {R : ℝ} (hφ0 : ∀ y, R < ‖y‖ → φ y = 0)
    (x : Fin d → ℝ) (hx : R + 1 < ‖x‖) : moll ρ φ x = 0 := by
  rw [moll_eq]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  by_cases h0 : ρ (x - y) = 0
  · simp [h0]
  · have h1 := hk.support _ h0
    have : φ y = 0 := by
      apply hφ0
      by_contra hy
      push Not at hy
      have : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
        calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      linarith
    simp [this]

variable {b : Fin d → Fin d → (Fin d → ℝ) → ℝ} {F φ : (Fin d → ℝ) → ℝ} {R : ℝ}

/-- **E1**: the equation tested with `ρ ⋆ φ` -/
theorem test_eq (hb : ∀ i j, Sm (b i j)) (hk : FrKer ρ C₁) (heven : ∀ x, ρ (-x) = ρ x) (hu : LocallyIntegrable u)
    (hF : LocallyIntegrable F) (hφ : Sm φ) (hφ0 : ∀ y, R < ‖y‖ → φ y = 0)
    (veq : ∀ a : (Fin d → ℝ) → ℝ, Sm a → (∀ y, R + 1 < ‖y‖ → a y = 0) → ∫ x, u x * Pop b a x = ∫ x, F x * a x) :
    (∫ x, moll ρ u x * Pop b φ x) - ∫ x, u x * Tcomm b ρ φ x = ∫ x, moll ρ F x * φ x := by
  have hPφ : Sm (Pop b φ) := sm_Pop hb hφ
  have hmφ : Sm (moll ρ φ) := moll_contDiff hk.sm hk.cs hφ.continuous.locallyIntegrable
  have hPφ0 : ∀ y, R < ‖y‖ → Pop b φ y = 0 := fun y hy => Pop_zero_off hφ0 y hy
  have hma0 : ∀ y, R + 1 < ‖y‖ → moll ρ φ y = 0 := fun y hy => moll_zero_off hk hφ0 y hy
  have hPa0 : ∀ y, R + 1 < ‖y‖ → Pop b (moll ρ φ) y = 0 := fun y hy => Pop_zero_off hma0 y hy
  have hmP : Sm (moll ρ (Pop b φ)) := moll_contDiff hk.sm hk.cs hPφ.continuous.locallyIntegrable
  have hmP0 : ∀ y, R + 1 < ‖y‖ → moll ρ (Pop b φ) y = 0 := fun y hy => moll_zero_off hk hPφ0 y hy
  have hcsR : ∀ {f : (Fin d → ℝ) → ℝ} {S : ℝ}, (∀ y, S < ‖y‖ → f y = 0) → HasCompactSupport f := fun {f S} h =>
    hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) S) fun y hy => h y (by simpa using hy)
  have key := veq (moll ρ φ) hmφ hma0
  have eP : ∀ x, Pop b (moll ρ φ) x = moll ρ (Pop b φ) x - Tcomm b ρ φ x := fun x => by unfold Tcomm; ring
  have hT : Continuous (Tcomm b ρ φ) := (sm_Tcomm hb hk.sm hk.cs hφ).continuous
  have hT0 : ∀ y, R + 1 < ‖y‖ → Tcomm b ρ φ y = 0 := fun y hy => by
    unfold Tcomm; rw [hmP0 y hy, hPa0 y hy]; ring
  have i1 : Integrable (fun x => u x * moll ρ (Pop b φ) x) := integrable_mul_cs hu hmP.continuous (hcsR hmP0)
  have i2 : Integrable (fun x => u x * Tcomm b ρ φ x) := integrable_mul_cs hu hT (hcsR hT0)
  have s1 := integral_moll_swap hk heven hu hPφ.continuous hPφ0
  have s2 := integral_moll_swap hk heven hF hφ.continuous hφ0
  simp only [eP] at key
  simp_rw [mul_sub] at key
  rw [integral_sub i1 i2, s1, s2] at key
  exact key

end

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
