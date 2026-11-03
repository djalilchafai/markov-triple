import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticLocal

/-!
# Mollifiers (R16, elliptic half; Evans §5.3.1 / §C.5, Gilbarg–Trudinger §7.2)

Statements M0–M4 of `STATEMENTS_R16_Elliptic.md` (continuation, batch 3).
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff Convolution

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- the mollification `ρ * f` -/
noncomputable def moll (ρ f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := ∫ t, ρ t * f (x - t)

lemma moll_eq (ρ f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : moll ρ f x = ∫ y, ρ (x - y) * f y := by
  unfold moll
  have := integral_sub_left_eq_self (μ := (volume : Measure (Fin d → ℝ)))
    (fun y => ρ (x - y) * f y) x
  simpa using this

/-- **M0** a mollifier sequence -/
lemma exists_mollifier (d : ℕ) : ∃ ρ : ℕ → (Fin d → ℝ) → ℝ, (∀ n, Sm (ρ n)) ∧ (∀ n, HasCompactSupport (ρ n)) ∧
    (∀ n x, 0 ≤ ρ n x) ∧ (∀ n, ∫ x, ρ n x = 1) ∧ (∀ n x, ρ n x ≠ 0 → ‖x‖ < 1 / ((n : ℝ) + 1)) := by
  let b : ∀ n : ℕ, ContDiffBump (0 : Fin d → ℝ) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]; nlinarith⟩
  refine ⟨fun n => (b n).normed volume, fun n => (b n).contDiff_normed, fun n => (b n).hasCompactSupport_normed,
    fun n x => (b n).nonneg_normed x, fun n => (b n).integral_normed, fun n x hx => ?_⟩
  have : x ∈ Function.support ((b n).normed volume) := hx
  rw [(b n).support_normed_eq] at this
  exact (by simpa using this : ‖x‖ < (b n).rOut)

section
variable {ρ f g : (Fin d → ℝ) → ℝ}

/-- **M1** smoothness -/
lemma moll_contDiff (hρ : Sm ρ) (hρc : HasCompactSupport ρ) (hf : LocallyIntegrable f) : Sm (moll ρ f) := by
  have := hρc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) (n := (⊤ : ℕ∞)) hρ hf
  exact this

lemma moll_hasCompactSupport (hρc : HasCompactSupport ρ) (hfc : HasCompactSupport f) :
    HasCompactSupport (moll ρ f) :=
  hρc.convolution (ContinuousLinearMap.mul ℝ ℝ) hfc

/-- **M2** mollification commutes with weak derivatives -/
lemma pderiv_moll (hρ : Sm ρ) (hρc : HasCompactSupport ρ) {j : Fin d} (h : WeakDeriv f g j) (x : Fin d → ℝ) :
    pderiv (moll ρ f) j x = moll ρ g x := by
  have hd := hρc.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) (hρ.of_le (by simp)) h.1 x
  have hfd : fderiv ℝ (moll ρ f) x = _ := hd.fderiv
  have hcont : Continuous (fun y => fderiv ℝ ρ y) := hρ.continuous_fderiv (by simp)
  have hcs : HasCompactSupport (fderiv ℝ ρ) := hρc.fderiv (𝕜 := ℝ)
  have hint := (hcs.convolutionExists_left (ContinuousLinearMap.precompL (Fin d → ℝ) (ContinuousLinearMap.mul ℝ ℝ)) hcont h.1 x)
  have hconv := ContinuousLinearMap.integral_apply hint (Pi.single j 1)
  unfold pderiv
  rw [hfd]
  show (∫ t, ((ContinuousLinearMap.mul ℝ ℝ).precompL (Fin d → ℝ) (fderiv ℝ ρ t)) (f (x - t))) (Pi.single j 1) = _
  rw [hconv]
  -- weak derivative with test function `y ↦ ρ (x - y)`
  have hψ : Sm (fun y => ρ (x - y)) := hρ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun y => ρ (x - y)) := by
    convert hρc.comp_homeomorph ((Homeomorph.neg (Fin d → ℝ)).trans (Homeomorph.addLeft x)) using 1
    funext y; simp [sub_eq_add_neg]
  have hw := h.2.2 _ hψ hψc
  have hfdψ : ∀ y, fderiv ℝ (fun y => ρ (x - y)) y (Pi.single j 1) = -(fderiv ℝ ρ (x - y) (Pi.single j 1)) := by
    intro y
    have h1 : HasFDerivAt ρ (fderiv ℝ ρ (x - y)) (x - y) := (hρ.differentiableAt _).hasFDerivAt
    have h2 : HasFDerivAt (fun y : Fin d → ℝ => x - y) (-(ContinuousLinearMap.id ℝ _)) y :=
      (hasFDerivAt_id y).const_sub x
    have := (h1.comp y h2).fderiv
    have e : (fun y : Fin d → ℝ => ρ (x - y)) = ρ ∘ (fun y => x - y) := rfl
    rw [e, this]
    simp
  simp only [hfdψ] at hw
  have e1 : ∫ t, fderiv ℝ ρ t (Pi.single j 1) * f (x - t) = ∫ y, f y * fderiv ℝ ρ (x - y) (Pi.single j 1) := by
    have := integral_sub_left_eq_self (μ := (volume : Measure (Fin d → ℝ)))
      (fun y => f y * fderiv ℝ ρ (x - y) (Pi.single j 1)) x
    simp only [sub_sub_cancel] at this
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun t => by simp [mul_comm])
  have e0 : ∫ t, (((ContinuousLinearMap.precompL (Fin d → ℝ) (ContinuousLinearMap.mul ℝ ℝ)) (fderiv ℝ ρ t))
      (f (x - t))) (Pi.single j 1) = ∫ t, fderiv ℝ ρ t (Pi.single j 1) * f (x - t) :=
    integral_congr_ae (Eventually.of_forall fun t => by simp [mul_comm])
  rw [e0, e1, moll_eq]
  have e2 : ∫ y, f y * -(fderiv ℝ ρ (x - y) (Pi.single j 1)) = -∫ y, f y * fderiv ℝ ρ (x - y) (Pi.single j 1) := by
    rw [← integral_neg]; exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  rw [e2] at hw
  have e3 : ∫ y, g y * ρ (x - y) = ∫ y, ρ (x - y) * g y :=
    integral_congr_ae (Eventually.of_forall fun y => by ring)
  linarith

/-- `L²` norm (real-valued) -/
noncomputable def N2 (g : (Fin d → ℝ) → ℝ) : ℝ := (eLpNorm g 2 volume).toReal

lemma N2_sq {g : (Fin d → ℝ) → ℝ} (hg : MemLp g 2 volume) : N2 g ^ 2 = ∫ x, g x * g x := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  rw [← inner_toLp hg hg, real_inner_self_eq_norm_sq, Lp.norm_toLp]
  rfl

lemma N2_nonneg (g : (Fin d → ℝ) → ℝ) : 0 ≤ N2 g := ENNReal.toReal_nonneg

lemma N2_add_le {g h : (Fin d → ℝ) → ℝ} (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    N2 (fun x => g x + h x) ≤ N2 g + N2 h := by
  unfold N2
  rw [← ENNReal.toReal_add hg.eLpNorm_ne_top hh.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hg.eLpNorm_ne_top, hh.eLpNorm_ne_top⟩)
    (eLpNorm_add_le (by norm_num))

/-- `∫ ρ (a − m)² ≥ 0` gives Jensen's inequality for a probability density. -/
lemma sq_integral_le {ρ a : (Fin d → ℝ) → ℝ} (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (h1 : Integrable ρ) (h2 : Integrable (fun t => ρ t * a t)) (h3 : Integrable (fun t => ρ t * a t ^ 2)) :
    (∫ t, ρ t * a t) ^ 2 ≤ ∫ t, ρ t * a t ^ 2 := by
  set m := ∫ t, ρ t * a t with hm
  have h4 : Integrable (fun t => ρ t * (a t - m) ^ 2) := by
    have : (fun t => ρ t * (a t - m) ^ 2) = fun t => ρ t * a t ^ 2 - 2 * m * (ρ t * a t) + m ^ 2 * ρ t := by
      funext t; ring
    rw [this]
    exact (h3.sub (h2.const_mul _)).add (h1.const_mul _)
  have h5 : 0 ≤ ∫ t, ρ t * (a t - m) ^ 2 :=
    integral_nonneg fun t => mul_nonneg (hρ0 t) (sq_nonneg _)
  have h6 : ∫ t, ρ t * (a t - m) ^ 2 = (∫ t, ρ t * a t ^ 2) - 2 * m * m + m ^ 2 * 1 := by
    have : (fun t => ρ t * (a t - m) ^ 2) = fun t => ρ t * a t ^ 2 - 2 * m * (ρ t * a t) + m ^ 2 * ρ t := by
      funext t; ring
    have k1 : ∫ t, (ρ t * a t ^ 2 - 2 * m * (ρ t * a t)) =
        (∫ t, ρ t * a t ^ 2) - ∫ t, 2 * m * (ρ t * a t) := integral_sub h3 (h2.const_mul _)
    have k2 : ∫ t, (ρ t * a t ^ 2 - 2 * m * (ρ t * a t) + m ^ 2 * ρ t) =
        (∫ t, (ρ t * a t ^ 2 - 2 * m * (ρ t * a t))) + ∫ t, m ^ 2 * ρ t :=
      integral_add (h3.sub (h2.const_mul _)) (h1.const_mul _)
    rw [this, k2, k1, integral_const_mul, integral_const_mul, ← hm, hρ1]
  nlinarith

end

section
variable {ρ f : (Fin d → ℝ) → ℝ}

/-- **M3a** pointwise Jensen -/
lemma moll_sq_le (hρ : Sm ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (hf : MemLp f 2 volume) (x : Fin d → ℝ) :
    moll ρ f x ^ 2 ≤ moll ρ (fun y => f y ^ 2) x := by
  have hfl : LocallyIntegrable f := hf.locallyIntegrable (by norm_num)
  have hsq : Integrable (fun y => f y ^ 2) := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hint := hρc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hρ.continuous hfl x
  have hint2 := hρc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hρ.continuous hsq.locallyIntegrable x
  have i1 : Integrable (fun t => ρ t * f (x - t)) := hint
  have i2 : Integrable (fun t => ρ t * f (x - t) ^ 2) := hint2
  exact sq_integral_le (a := fun t => f (x - t)) hρ0 hρ1 (hρ.continuous.integrable_of_hasCompactSupport hρc) i1 i2

/-- **M3a** the mollification of an `L²` function is `L²` and does not increase the norm. -/
lemma moll_memLp_norm_le (hρ : Sm ρ) (hρc : HasCompactSupport ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ1 : ∫ x, ρ x = 1)
    (hf : MemLp f 2 volume) : MemLp (moll ρ f) 2 volume ∧ N2 (moll ρ f) ≤ N2 f := by
  have hsq : Integrable (fun y => f y ^ 2) := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).1 hf
  have hρi : Integrable ρ := hρ.continuous.integrable_of_hasCompactSupport hρc
  have hconv : Integrable (fun x => moll ρ (fun y => f y ^ 2) x) :=
    hρi.integrable_convolution (ContinuousLinearMap.mul ℝ ℝ) hsq
  have hcont : Continuous (moll ρ f) := (moll_contDiff hρ hρc (hf.locallyIntegrable (by norm_num))).continuous
  have hint : Integrable (fun x => moll ρ f x ^ 2) := by
    refine hconv.mono' (hcont.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact moll_sq_le hρ hρc hρ0 hρ1 hf x
  have hmem : MemLp (moll ρ f) 2 volume := (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 hint
  refine ⟨hmem, ?_⟩
  have hI : ∫ x, moll ρ (fun y => f y ^ 2) x = ∫ x, f x ^ 2 := by
    have := integral_convolution (ContinuousLinearMap.mul ℝ ℝ) (μ := (volume : Measure (Fin d → ℝ)))
      (ν := volume) hρi hsq
    simp only [ContinuousLinearMap.mul_apply', hρ1, one_mul] at this
    exact this
  have hle : ∫ x, moll ρ f x ^ 2 ≤ ∫ x, f x ^ 2 := by
    rw [← hI]
    exact integral_mono hint hconv fun x => moll_sq_le hρ hρc hρ0 hρ1 hf x
  have e1 := N2_sq hmem
  have e2 := N2_sq hf
  have : N2 (moll ρ f) ^ 2 ≤ N2 f ^ 2 := by
    rw [e1, e2]; simpa [sq] using hle
  nlinarith [N2_nonneg (moll ρ f), N2_nonneg f]

/-- linearity of mollification on `L²` -/
lemma moll_sub (hρ : Sm ρ) (hρc : HasCompactSupport ρ) {f φ : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume)
    (hφ : MemLp φ 2 volume) (x : Fin d → ℝ) :
    moll ρ (fun y => f y - φ y) x = moll ρ f x - moll ρ φ x := by
  have h1 := hρc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hρ.continuous
    (hf.locallyIntegrable (by norm_num)) x
  have h2 := hρc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hρ.continuous
    (hφ.locallyIntegrable (by norm_num)) x
  have i1 : Integrable (fun t => ρ t * f (x - t)) := h1
  have i2 : Integrable (fun t => ρ t * φ (x - t)) := h2
  unfold moll
  rw [← integral_sub i1 i2]
  exact integral_congr_ae (Eventually.of_forall fun t => by ring)

end

structure IsMollSeq (ρ : ℕ → (Fin d → ℝ) → ℝ) : Prop where
  smooth : ∀ n, Sm (ρ n)
  cs : ∀ n, HasCompactSupport (ρ n)
  nonneg : ∀ n x, 0 ≤ ρ n x
  integral : ∀ n, ∫ x, ρ n x = 1
  support : ∀ n x, ρ n x ≠ 0 → ‖x‖ < 1 / ((n : ℝ) + 1)

lemma exists_mollSeq (d : ℕ) : ∃ ρ : ℕ → (Fin d → ℝ) → ℝ, IsMollSeq ρ := by
  obtain ⟨ρ, h1, h2, h3, h4, h5⟩ := exists_mollifier d
  exact ⟨ρ, ⟨h1, h2, h3, h4, h5⟩⟩

section
variable {ρ : ℕ → (Fin d → ℝ) → ℝ}

/-- **M3b'** uniform convergence for continuous compactly supported functions -/
lemma moll_tendsto_cs (hρ : IsMollSeq ρ) {φ : (Fin d → ℝ) → ℝ} (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    Tendsto (fun n => N2 (fun x => moll (ρ n) φ x - φ x)) atTop (𝓝 0) := by
  set S : Set (Fin d → ℝ) := Metric.cthickening 1 (tsupport φ) with hS
  have hSc : IsCompact S := hs.cthickening
  have hSfin : volume S < ⊤ := hSc.measure_lt_top
  set c : ℝ≥0∞ := volume S ^ (2 : ℝ≥0∞).toReal⁻¹ with hc
  have hcfin : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hSfin.ne
  have hunif := hs.uniformContinuous_of_continuous hφ
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
  set ε' : ℝ := ε / (2 * (c.toReal + 1)) with hε'
  have hε'pos : 0 < ε' := by positivity
  obtain ⟨δ, hδ, hδε⟩ := Metric.uniformContinuous_iff.1 hunif ε' hε'pos
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : 1 / ((n : ℝ) + 1) < δ := by
    have h1 : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h2 : 1 / δ < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ (by positivity)] at h2 ⊢
    nlinarith
  have hρi : Integrable (ρ n) := (hρ.smooth n).continuous.integrable_of_hasCompactSupport (hρ.cs n)
  -- pointwise bound
  have hpt : ∀ x, |moll (ρ n) φ x - φ x| ≤ ε' := by
    intro x
    have hφl : LocallyIntegrable φ := hφ.locallyIntegrable
    have h1 := (hρ.cs n).convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) (hρ.smooth n).continuous hφl x
    have i1 : Integrable (fun t => ρ n t * φ (x - t)) := h1
    have i2 : Integrable (fun t => ρ n t * φ x) := hρi.mul_const _
    have e : moll (ρ n) φ x - φ x = ∫ t, ρ n t * (φ (x - t) - φ x) := by
      unfold moll
      have : ∫ t, ρ n t * (φ (x - t) - φ x) = (∫ t, ρ n t * φ (x - t)) - ∫ t, ρ n t * φ x := by
        rw [← integral_sub i1 i2]; exact integral_congr_ae (Eventually.of_forall fun t => by ring)
      rw [this, integral_mul_const, hρ.integral n, one_mul]
    rw [e]
    have hb : ∀ t, ‖ρ n t * (φ (x - t) - φ x)‖ ≤ ε' * ρ n t := by
      intro t
      by_cases ht : ρ n t = 0
      · simp [ht]
      · have hlt := hρ.support n t ht
        have := hδε (a := x - t) (b := x) (by rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; exact lt_trans hlt hn1)
        rw [norm_mul, Real.norm_of_nonneg (hρ.nonneg n t), mul_comm]
        exact mul_le_mul_of_nonneg_right (by rw [Real.dist_eq] at this; exact this.le) (hρ.nonneg n t)
    calc |∫ t, ρ n t * (φ (x - t) - φ x)| ≤ ∫ t, ‖ρ n t * (φ (x - t) - φ x)‖ := by
          simpa using norm_integral_le_integral_norm (μ := (volume : Measure (Fin d → ℝ))) (fun t => ρ n t * (φ (x - t) - φ x))
      _ ≤ ∫ t, ε' * ρ n t := integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _)
            (hρi.const_mul _) (Eventually.of_forall hb)
      _ = ε' := by rw [integral_const_mul, hρ.integral n, mul_one]
  -- vanishing outside S
  have hout : ∀ x, x ∉ S → moll (ρ n) φ x - φ x = 0 := by
    intro x hx
    have h1 : φ x = 0 := by
      by_contra hne; exact hx (Metric.self_subset_cthickening _ (subset_tsupport _ hne))
    have h2 : moll (ρ n) φ x = 0 := by
      unfold moll
      have : ∀ t, ρ n t * φ (x - t) = 0 := by
        intro t
        by_cases ht : ρ n t = 0
        · simp [ht]
        · have hlt := hρ.support n t ht
          have : φ (x - t) = 0 := by
            by_contra hne
            refine hx (Metric.mem_cthickening_of_dist_le x (x - t) 1 (tsupport φ) (subset_tsupport _ hne) ?_)
            rw [dist_eq_norm, sub_sub_cancel]
            refine hlt.le.trans ?_
            rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
          simp [this]
      simp [this]
    rw [h1, h2]; simp
  have hcontg : Continuous (fun x => moll (ρ n) φ x - φ x) :=
    (moll_contDiff (hρ.smooth n) (hρ.cs n) hφ.locallyIntegrable).continuous.sub hφ
  have heq : (fun x => moll (ρ n) φ x - φ x) = S.indicator (fun x => moll (ρ n) φ x - φ x) := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx, hout x hx]
  have hnorm : eLpNorm (fun x => moll (ρ n) φ x - φ x) 2 volume ≤ c * ENNReal.ofReal ε' := by
    rw [heq, eLpNorm_indicator_eq_eLpNorm_restrict hSc.measurableSet]
    have := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict S) (f := fun x => moll (ρ n) φ x - φ x)
      hcontg.aestronglyMeasurable (C := ε') (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hpt x)
    simpa [Measure.restrict_apply_univ, hc] using this
  have hN2 : N2 (fun x => moll (ρ n) φ x - φ x) ≤ c.toReal * ε' := by
    unfold N2
    have h := ENNReal.toReal_mono (ENNReal.mul_ne_top hcfin ENNReal.ofReal_ne_top) hnorm
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε'pos.le] at h
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (N2_nonneg _)]
  calc N2 _ ≤ c.toReal * ε' := hN2
    _ < ε := by
        rw [hε']
        have : c.toReal * (ε / (2 * (c.toReal + 1))) = ε * (c.toReal / (2 * (c.toReal + 1))) := by ring
        rw [this]
        have h2 : c.toReal / (2 * (c.toReal + 1)) < 1 := by
          rw [div_lt_one (by positivity)]; linarith
        nlinarith

/-- **M3b** `ρₙ * f → f` in `L²` (Evans §C.5 Thm 7). -/
theorem moll_tendsto (hρ : IsMollSeq ρ) {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun n => N2 (fun x => moll (ρ n) f x - f x)) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨φ, hφc, hφn, hφcont, hφm⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le (p := 2) (by simp)
    (ε := ENNReal.ofReal (ε / 4)) (by simpa using hε4)
  have hfφ : MemLp (fun x => f x - φ x) 2 volume := hf.sub hφm
  have hN : N2 (fun x => f x - φ x) ≤ ε / 4 := by
    unfold N2
    exact ENNReal.toReal_le_of_le_ofReal hε4.le hφn
  obtain ⟨N0, hN0⟩ := Metric.tendsto_atTop.1 (moll_tendsto_cs hρ hφcont hφc) (ε / 4) hε4
  refine ⟨N0, fun n hn => ?_⟩
  have h0 := hN0 n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (N2_nonneg _)] at h0
  have hm1 := (moll_memLp_norm_le (hρ.smooth n) (hρ.cs n) (hρ.nonneg n) (hρ.integral n) hfφ)
  have hm2 := (moll_memLp_norm_le (hρ.smooth n) (hρ.cs n) (hρ.nonneg n) (hρ.integral n) hφm)
  have hdecomp : (fun x => moll (ρ n) f x - f x) =
      fun x => (moll (ρ n) (fun y => f y - φ y) x + (moll (ρ n) φ x - φ x)) + (φ x - f x) := by
    funext x
    rw [moll_sub (hρ.smooth n) (hρ.cs n) hf hφm x]; ring
  have hsw : N2 (fun x => φ x - f x) = N2 (fun x => f x - φ x) := by
    unfold N2
    have : (fun x => φ x - f x) = -(fun x => f x - φ x) := by funext x; simp
    rw [this, eLpNorm_neg]
  have hA : MemLp (fun x => moll (ρ n) (fun y => f y - φ y) x + (moll (ρ n) φ x - φ x)) 2 volume :=
    hm1.1.add (hm2.1.sub hφm)
  have hB : MemLp (fun x => φ x - f x) 2 volume := hφm.sub hf
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (N2_nonneg _), hdecomp]
  calc N2 _ ≤ N2 (fun x => moll (ρ n) (fun y => f y - φ y) x + (moll (ρ n) φ x - φ x)) + N2 (fun x => φ x - f x) :=
        N2_add_le hA hB
    _ ≤ (N2 (moll (ρ n) fun y => f y - φ y) + N2 (fun x => moll (ρ n) φ x - φ x)) + N2 (fun x => φ x - f x) := by
        gcongr
        exact N2_add_le hm1.1 (hm2.1.sub hφm)
    _ ≤ (ε / 4 + ε / 4) + ε / 4 := by
        exact add_le_add (add_le_add (hm1.2.trans hN) h0.le) (by rw [hsw]; exact hN)
    _ < ε := by linarith

/-- **M4** `L²` convergence gives convergence of pairings -/
theorem tendsto_integral_mul {k v : (Fin d → ℝ) → ℝ} {a : ℕ → (Fin d → ℝ) → ℝ} (hk : MemLp k 2 volume)
    (hv : MemLp v 2 volume) (ha : ∀ n, MemLp (a n) 2 volume)
    (hconv : Tendsto (fun n => N2 (fun x => a n x - v x)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, k x * a n x) atTop (𝓝 (∫ x, k x * v x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : ∀ n, ‖(∫ x, k x * a n x) - ∫ x, k x * v x‖ ≤ N2 k * N2 (fun x => a n x - v x) := by
    intro n
    have hd := (ha n).sub hv
    have i1 : Integrable (fun x => k x * a n x) := by
      have := (hk.integrable_mul (ha n)); exact this
    have i2 : Integrable (fun x => k x * v x) := hk.integrable_mul hv
    rw [← integral_sub i1 i2, Real.norm_eq_abs]
    have := abs_integral_mul_le hk hd
    refine le_trans (le_of_eq ?_) this
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  refine squeeze_zero (fun n => norm_nonneg _) hb ?_
  simpa using hconv.const_mul (N2 k)

/-- a function that is `L²_loc` and cut to a compact set is `L²` -/
lemma LocL2.memLp_indicator {f : (Fin d → ℝ) → ℝ} (hf : LocL2 f) {S : Set (Fin d → ℝ)} (hS : IsCompact S) :
    MemLp (S.indicator f) 2 volume :=
  (memLp_indicator_iff_restrict hS.measurableSet).2 (hf S hS)

/-- the weak derivative of a function vanishing outside `T := tsupport v` vanishes a.e. outside `T` -/
lemma weakDeriv_zero_off {v g : (Fin d → ℝ) → ℝ} {j : Fin d} (h : WeakDeriv v g j) :
    ∀ᵐ x, x ∉ tsupport v → g x = 0 := by
  have hU : IsOpen (tsupport v)ᶜ := (isClosed_tsupport v).isOpen_compl
  have := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (f := g) (μ := (volume : Measure (Fin d → ℝ)))
    (h.2.1.locallyIntegrableOn _) (fun φ hφ hs hsub => by
      have e := h.2.2 φ hφ hs
      have h0 : ∫ x, v x * fderiv ℝ φ x (Pi.single j 1) = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ tsupport φ
        · simp [image_eq_zero_of_notMem_tsupport (show x ∉ tsupport v from hsub hx)]
        · have : fderiv ℝ φ x = 0 := by
            by_contra hne; exact hx (support_fderiv_subset ℝ hne)
          simp [this]
      have : ∫ x, g x * φ x = 0 := by linarith
      simpa [smul_eq_mul, mul_comm] using this)
  filter_upwards [this] with x hx hxT using hx hxT

section
variable {ρ : ℕ → (Fin d → ℝ) → ℝ}

/-- support of a mollification -/
lemma moll_eq_zero_off (hρ : IsMollSeq ρ) (n : ℕ) {f : (Fin d → ℝ) → ℝ} {T : Set (Fin d → ℝ)}
    (hf : ∀ᵐ y, y ∉ T → f y = 0) {x : Fin d → ℝ} (hx : x ∉ Metric.cthickening 1 T) :
    moll (ρ n) f x = 0 := by
  unfold moll
  refine integral_eq_zero_of_ae ?_
  have hae : ∀ᵐ t : Fin d → ℝ, (x - t) ∉ T → f (x - t) = 0 :=
    (Measure.measurePreserving_sub_left (volume : Measure (Fin d → ℝ)) x).quasiMeasurePreserving.ae hf
  filter_upwards [hae] with t ht
  by_cases hρt : ρ n t = 0
  · simp [hρt]
  · have hlt := hρ.support n t hρt
    have hmem : x - t ∉ T := by
      intro hT
      refine hx (Metric.mem_cthickening_of_dist_le x (x - t) 1 T hT ?_)
      rw [dist_eq_norm, sub_sub_cancel]
      refine hlt.le.trans ?_
      rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]
    simp [ht hmem]

end

end

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
