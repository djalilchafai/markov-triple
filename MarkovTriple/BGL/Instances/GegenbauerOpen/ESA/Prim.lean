import Mathlib
import MarkovTriple.BGL.Instances.GegenbauerOpen.Diffusion

/-!
# Weak derivatives on `(-1,1)`: primitives, du Bois-Reymond, kernel trick

Ingredients for the regularity step (`Regularity.lean`) of the proof of F10 for `goDiff` (`STATEMENTS_R23_G1.md`):
local integrability, integration by parts against an absolutely continuous primitive, primitives of mean-zero test
functions, and du Bois-Reymond type lemmas on test functions `goA₀ = C_c^∞((-1,1))`.
-/

open MeasureTheory Filter Topology Set intervalIntegral

namespace MarkovTriple.BGL.Instances.GegenbauerOpen.ESA

/-- local integrability on `(-1,1)`: integrable on every `[-r,r]`, `r < 1`. -/
def LocInt (f : ℝ → ℝ) : Prop := ∀ r : ℝ, 0 ≤ r → r < 1 → IntegrableOn f (Icc (-r) r)

lemma LocInt.add {f g : ℝ → ℝ} (hf : LocInt f) (hg : LocInt g) : LocInt (fun x => f x + g x) :=
  fun r h0 h1 => (hf r h0 h1).add (hg r h0 h1)

lemma LocInt.sub {f g : ℝ → ℝ} (hf : LocInt f) (hg : LocInt g) : LocInt (fun x => f x - g x) :=
  fun r h0 h1 => (hf r h0 h1).sub (hg r h0 h1)

lemma LocInt.mul_cont {f g : ℝ → ℝ} (hf : LocInt f) (hg : Continuous g) :
    LocInt (fun x => f x * g x) :=
  fun r h0 h1 => (hf r h0 h1).mul_continuousOn hg.continuousOn isCompact_Icc

lemma LocInt.cont_mul {f g : ℝ → ℝ} (hf : LocInt f) (hg : Continuous g) :
    LocInt (fun x => g x * f x) := by
  simpa [mul_comm] using hf.mul_cont hg

lemma LocInt.of_continuousOn {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo (-1:ℝ) 1)) : LocInt f :=
  fun r h0 h1 => (hf.mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)).integrableOn_Icc

lemma LocInt.const (c : ℝ) : LocInt (fun _ => c) := LocInt.of_continuousOn continuousOn_const

lemma LocInt.intervalIntegrable {f : ℝ → ℝ} (hf : LocInt f) {a b : ℝ} (ha : a ∈ Ioo (-1:ℝ) 1)
    (hb : b ∈ Ioo (-1:ℝ) 1) : IntervalIntegrable f volume a b := by
  have : uIcc a b ⊆ Icc (-(max |a| |b|)) (max |a| |b|) := by
    intro x hx
    have h1 : |x| ≤ max |a| |b| := by
      rw [abs_le]
      rcases mem_uIcc.1 hx with ⟨h2, h3⟩ | ⟨h2, h3⟩
      · constructor
        · linarith [neg_abs_le a, le_max_left |a| |b|]
        · linarith [le_abs_self b, le_max_right |a| |b|]
      · constructor
        · linarith [neg_abs_le b, le_max_right |a| |b|]
        · linarith [le_abs_self a, le_max_left |a| |b|]
    exact abs_le.1 h1
  have h0 : 0 ≤ max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
  have h1 : max |a| |b| < 1 := max_lt (abs_lt.2 ⟨ha.1, ha.2⟩) (abs_lt.2 ⟨hb.1, hb.2⟩)
  exact ((hf _ h0 h1).mono_set this).intervalIntegrable

/-- the primitive of a locally integrable function is continuous on `(-1,1)`. -/
lemma LocInt.continuousOn_primitive {f : ℝ → ℝ} (hf : LocInt f) :
    ContinuousOn (fun x => ∫ t in (0:ℝ)..x, f t) (Ioo (-1:ℝ) 1) := by
  intro x hx
  have hr : 0 ≤ (|x| + 1) / 2 := by positivity
  have hr1 : (|x| + 1) / 2 < 1 := by
    have := abs_lt.2 ⟨hx.1, hx.2⟩; linarith
  have hint : IntervalIntegrable f volume (-((|x| + 1) / 2)) ((|x| + 1) / 2) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).2 (hf _ hr hr1)
  have h0 : (0:ℝ) ∈ uIcc (-((|x| + 1) / 2)) ((|x| + 1) / 2) := by
    rw [uIcc_of_le (by linarith)]; exact ⟨by linarith, by linarith⟩
  have hc := continuousOn_primitive_interval' hint h0
  have hxm : x ∈ Ioo (-((|x| + 1) / 2)) ((|x| + 1) / 2) := by
    have hlt : |x| < (|x| + 1) / 2 := by
      have := abs_lt.2 ⟨hx.1, hx.2⟩; linarith
    exact abs_lt.1 hlt
  have hnhds : uIcc (-((|x| + 1) / 2)) ((|x| + 1) / 2) ∈ 𝓝 x := by
    rw [uIcc_of_le (by linarith)]; exact Icc_mem_nhds hxm.1 hxm.2
  exact (hc.continuousAt hnhds).continuousWithinAt


/-! ### test functions -/

lemma exists_Icc {ψ : ℝ → ℝ} (hψ : ψ ∈ goA₀) : ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ ∀ x, r < |x| → ψ x = 0 := by
  have hc : IsCompact (tsupport ψ) := goA₀_cs hψ
  rcases (tsupport ψ).eq_empty_or_nonempty with h | h
  · exact ⟨0, le_rfl, one_pos, fun x _ => image_eq_zero_of_notMem_tsupport (by simp [h])⟩
  · obtain ⟨x₀, hx₀, hmax⟩ := hc.exists_isMaxOn h continuous_abs.continuousOn
    refine ⟨|x₀|, abs_nonneg _, abs_lt.2 ⟨(hψ.2 hx₀).1, (hψ.2 hx₀).2⟩, fun x hx => ?_⟩
    refine image_eq_zero_of_notMem_tsupport fun hxs => ?_
    exact absurd (hmax hxs) (not_le.2 hx)

lemma integrableOn_mul_test {A φ : ℝ → ℝ} (hA : LocInt A) (hφ : φ ∈ goA₀) :
    IntegrableOn (fun x => A x * φ x) (Ioo (-1:ℝ) 1) := by
  obtain ⟨r, h0, h1, hr⟩ := exists_Icc hφ
  have h2 : IntegrableOn (fun x => A x * φ x) (Icc (-r) r) :=
    (hA r h0 h1).mul_continuousOn (hφ.1.continuous.continuousOn) isCompact_Icc
  refine h2.of_forall_sdiff_eq_zero measurableSet_Ioo ?_
  intro x hx
  have : r < |x| := by
    by_contra hh
    exact hx.2 (abs_le.1 (not_lt.1 hh))
  simp [hr x this]

lemma integral_Ioo_eq {g : ℝ → ℝ} {r : ℝ} (h0 : 0 ≤ r) (h1 : r < 1) (hg : ∀ x, r < |x| → g x = 0) :
    ∫ x in Ioo (-1:ℝ) 1, g x = ∫ x in (-r)..r, g x := by
  rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
    (fun x (hx : x ∈ Icc (-r) r) => (⟨by linarith [hx.1], by linarith [hx.2]⟩ : x ∈ Ioo (-1:ℝ) 1)) ?_
  intro x hx
  have : r < |x| := by
    by_contra hh
    exact hx.2 (abs_le.1 (not_lt.1 hh))
  exact hg x this


lemma exists_bump : ∃ ρ ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, ρ x = 1 := by
  let f : ContDiffBump (0:ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hmem : f.normed volume ∈ goA₀ := by
    refine ⟨f.contDiff_normed, ?_⟩
    rw [f.tsupport_normed_eq]
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hx
    have : |x| ≤ 1 / 2 := hx
    exact abs_lt.1 (lt_of_le_of_lt this (by norm_num))
  refine ⟨f.normed volume, hmem, ?_⟩
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ hx => zero_off_go hmem hx)]
  exact f.integral_normed

lemma integral_I_eq_integral {g : ℝ → ℝ} (hg : g ∈ goA₀) :
    ∫ x in Ioo (-1:ℝ) 1, g x = ∫ x, g x :=
  setIntegral_eq_integral_of_forall_compl_eq_zero (fun _ hx => zero_off_go hg hx)

lemma integrableOn_test {g : ℝ → ℝ} (hg : g ∈ goA₀) : IntegrableOn g (Ioo (-1:ℝ) 1) :=
  (Lebesgue.integrable_of (goA₀_le hg)).integrableOn

lemma meanzero {χ ρ : ℝ → ℝ} (hχ : χ ∈ goA₀) (hρ : ρ ∈ goA₀) (h1 : ∫ x in Ioo (-1:ℝ) 1, ρ x = 1) :
    (fun x => χ x - (∫ y in Ioo (-1:ℝ) 1, χ y) * ρ x) ∈ goA₀ ∧
      ∫ x in Ioo (-1:ℝ) 1, (χ x - (∫ y in Ioo (-1:ℝ) 1, χ y) * ρ x) = 0 := by
  set s := ∫ y in Ioo (-1:ℝ) 1, χ y with hs
  refine ⟨sub_mem hχ (SMulMemClass.smul_mem s hρ), ?_⟩
  rw [integral_sub (integrableOn_test hχ) ((integrableOn_test hρ).const_mul s),
    MeasureTheory.integral_const_mul, h1]
  simp [hs]

lemma primitive_mem {ψ : ℝ → ℝ} (hψ : ψ ∈ goA₀) (h0 : ∫ x in Ioo (-1:ℝ) 1, ψ x = 0) :
    (fun x => ∫ t in (-1:ℝ)..x, ψ t) ∈ goA₀ ∧
      deriv (fun x => ∫ t in (-1:ℝ)..x, ψ t) = ψ := by
  set f : ℝ → ℝ := fun x => ∫ t in (-1:ℝ)..x, ψ t with hf
  have hd : ∀ x, HasDerivAt f (ψ x) x := fun x =>
    (hψ.1.continuous.integral_hasStrictDerivAt (-1) x).hasDerivAt
  have hdf : deriv f = ψ := funext fun x => (hd x).deriv
  have hsm : Lebesgue.Sm f := by
    refine contDiff_infty_iff_deriv.2 ⟨fun x => (hd x).differentiableAt, ?_⟩
    rw [hdf]; exact hψ.1
  refine ⟨?_, hdf⟩
  obtain ⟨r, hr0, hr1, hr⟩ := exists_Icc hψ
  set R : ℝ := (r + 1) / 2 with hR
  have hrR : r < R := by rw [hR]; linarith
  have hR1 : R < 1 := by rw [hR]; linarith
  have hR0 : 0 ≤ R := hr0.trans hrR.le
  have hz : ∀ a b : ℝ, (∀ t ∈ uIcc a b, R ≤ |t|) → ∫ t in a..b, ψ t = 0 := by
    intro a b h
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) (fun t ht => hr t (lt_of_lt_of_le hrR (h t ht)))]
    simp
  have hIR : ∫ t in (-R)..R, ψ t = 0 := by
    rw [← integral_Ioo_eq hR0 hR1 (fun x hx => hr x (hrR.trans hx)), h0]
  have hint : ∀ a b : ℝ, IntervalIntegrable ψ volume a b := fun a b =>
    hψ.1.continuous.intervalIntegrable a b
  have hzero : ∀ x, R < |x| → f x = 0 := by
    intro x hx
    rcases lt_abs.1 hx with h | h
    · have e1 := intervalIntegral.integral_add_adjacent_intervals (hint (-1) (-R)) (hint (-R) R)
      have e2 := intervalIntegral.integral_add_adjacent_intervals (hint (-1) R) (hint R x)
      have z1 : ∫ t in (-1:ℝ)..(-R), ψ t = 0 := by
        refine hz _ _ fun t ht => ?_
        rw [mem_uIcc] at ht
        have : -t ≥ R := by rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
        exact this.trans (neg_le_abs t)
      have z2 : ∫ t in R..x, ψ t = 0 := by
        refine hz _ _ fun t ht => ?_
        rw [mem_uIcc] at ht
        rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h1.trans (le_abs_self t)
        · linarith
      show ∫ t in (-1:ℝ)..x, ψ t = 0
      rw [← e2, ← e1, z1, hIR, z2]; simp
    · have z : ∫ t in (-1:ℝ)..x, ψ t = 0 := by
        refine hz _ _ fun t ht => ?_
        rw [mem_uIcc] at ht
        have : -t ≥ R := by rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith
        exact this.trans (neg_le_abs t)
      exact z
  refine ⟨hsm, ?_⟩
  have hsupp : Function.support f ⊆ Icc (-R) R := fun x hx => by
    by_contra hh
    apply hx
    exact hzero x (by
      by_contra h2
      exact hh (abs_le.1 (not_lt.1 h2)))
  exact (closure_minimal hsupp isClosed_Icc).trans fun x hx =>
    ⟨by linarith [hx.1], by linarith [hx.2]⟩

lemma ibp_primitive {k ψ : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hc : c ∈ Icc a b)
    (hk : IntervalIntegrable k volume a b) (hψ : ContDiff ℝ 1 ψ) (ha : ψ a = 0) (hb : ψ b = 0) :
    ∫ x in a..b, (∫ t in c..x, k t) * deriv ψ x = - ∫ x in a..b, k x * ψ x := by
  have hc' : c ∈ uIcc a b := by rw [uIcc_of_le hab]; exact hc
  have hK : AbsolutelyContinuousOnInterval (fun x => ∫ t in c..x, k t) a b :=
    hk.absolutelyContinuousOnInterval_intervalIntegral hc'
  have hψ' : AbsolutelyContinuousOnInterval ψ a b := hψ.contDiffOn.absolutelyContinuousOnInterval
  have h := AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul hK hψ'
  rw [h, ha, hb]
  have : ∫ x in a..b, deriv (fun x => ∫ t in c..x, k t) x * ψ x = ∫ x in a..b, k x * ψ x := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hk.ae_hasDerivAt_integral] with x hx hxI
    rw [(hx (uIoc_subset_uIcc hxI) c hc').deriv]
  rw [this]; ring


lemma kernel_trick {A B : ℝ → ℝ} (hA : LocInt A) (hB : LocInt B)
    (h : ∀ ψ ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, ψ x = 0 →
      ∫ x in Ioo (-1:ℝ) 1, (A x * ψ x + B x * deriv ψ x) = 0) :
    ∃ c : ℝ, ∀ φ ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, (A x * φ x + B x * deriv φ x) =
      c * ∫ x in Ioo (-1:ℝ) 1, φ x := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_bump
  have hint : ∀ φ ∈ goA₀, IntegrableOn (fun x => A x * φ x + B x * deriv φ x) (Ioo (-1:ℝ) 1) :=
    fun φ hφ => (integrableOn_mul_test hA hφ).add (integrableOn_mul_test hB (deriv_mem_goA₀ hφ))
  refine ⟨∫ x in Ioo (-1:ℝ) 1, (A x * ρ x + B x * deriv ρ x), fun φ hφ => ?_⟩
  obtain ⟨hmem, hzero⟩ := meanzero hφ hρ hρ1
  have := h _ hmem hzero
  set s := ∫ y in Ioo (-1:ℝ) 1, φ y with hs
  have hder : ∀ x, deriv (fun x => φ x - s * ρ x) x = deriv φ x - s * deriv ρ x := fun x =>
    ((hφ.1.hasDerivAt x).sub ((hρ.1.hasDerivAt x).const_mul s)).deriv
  have e : ∀ x, A x * (φ x - s * ρ x) + B x * deriv (fun x => φ x - s * ρ x) x =
      (A x * φ x + B x * deriv φ x) - s * (A x * ρ x + B x * deriv ρ x) := by
    intro x; rw [hder]; ring
  simp_rw [e] at this
  rw [integral_sub (hint φ hφ) ((hint ρ hρ).const_mul s), MeasureTheory.integral_const_mul] at this
  linarith

lemma exists_r_of_compact {K : Set ℝ} (hK : IsCompact K) (hKs : K ⊆ Ioo (-1:ℝ) 1) :
    ∃ r : ℝ, 0 ≤ r ∧ r < 1 ∧ K ⊆ Icc (-r) r := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨0, le_rfl, one_pos, by simp [h]⟩
  · obtain ⟨x₀, hx₀, hmax⟩ := hK.exists_isMaxOn h continuous_abs.continuousOn
    refine ⟨|x₀|, abs_nonneg _, abs_lt.2 ⟨(hKs hx₀).1, (hKs hx₀).2⟩, fun x hx => ?_⟩
    exact abs_le.1 (hmax hx)

lemma LocInt.locallyIntegrableOn {f : ℝ → ℝ} (hf : LocInt f) :
    LocallyIntegrableOn f (Ioo (-1:ℝ) 1) volume := by
  rw [locallyIntegrableOn_iff isOpen_Ioo.isLocallyClosed]
  intro K hKs hK
  obtain ⟨r, h0, h1, hr⟩ := exists_r_of_compact hK hKs
  exact (hf r h0 h1).mono_set hr

/-- du Bois-Reymond: `∫ q φ' = 0` for all test functions forces `q` to be a.e. constant on `(-1,1)`. -/
lemma dbr1 {q : ℝ → ℝ} (hq : LocInt q)
    (h : ∀ φ ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, q x * deriv φ x = 0) :
    ∃ c : ℝ, ∀ᵐ x, x ∈ Ioo (-1:ℝ) 1 → q x = c := by
  obtain ⟨ρ, hρ, hρ1⟩ := exists_bump
  set c := ∫ x in Ioo (-1:ℝ) 1, q x * ρ x with hc
  refine ⟨c, ?_⟩
  have key : ∀ χ ∈ goA₀, ∫ x in Ioo (-1:ℝ) 1, q x * χ x = c * ∫ x in Ioo (-1:ℝ) 1, χ x := by
    intro χ hχ
    obtain ⟨hmem, hzero⟩ := meanzero hχ hρ hρ1
    obtain ⟨hpm, hpd⟩ := primitive_mem hmem hzero
    have := h _ hpm
    rw [hpd] at this
    set s := ∫ y in Ioo (-1:ℝ) 1, χ y with hs
    have e : ∀ x, q x * (χ x - s * ρ x) = q x * χ x - s * (q x * ρ x) := fun x => by ring
    simp_rw [e] at this
    rw [integral_sub (integrableOn_mul_test hq hχ) ((integrableOn_mul_test hq hρ).const_mul s),
      MeasureTheory.integral_const_mul] at this
    rw [← hc] at this
    linarith
  have hz := isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
    (f := fun x => q x - c) (hq.sub (LocInt.const c)).locallyIntegrableOn (by
      intro g hg hgc hgs
      have hgm : g ∈ goA₀ := ⟨hg, hgs⟩
      have e1 : ∫ x, g x • (q x - c) = ∫ x in Ioo (-1:ℝ) 1, (q x * g x - c * g x) := by
        rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Ioo (-1:ℝ) 1)
          (fun x hx => by simp [zero_off_go hgm hx])]
        refine setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_
        simp only [smul_eq_mul]; ring
      rw [e1, integral_sub (integrableOn_mul_test hq hgm)
        ((integrableOn_test hgm).const_mul c), MeasureTheory.integral_const_mul, key g hgm]
      ring)
  filter_upwards [hz] with x hx hxI
  have := hx hxI
  linarith

end MarkovTriple.BGL.Instances.GegenbauerOpen.ESA
