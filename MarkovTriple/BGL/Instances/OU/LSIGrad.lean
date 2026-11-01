import Mathlib
import MarkovTriple.BGL.Instances.OU.LSIMehler
import MarkovTriple.BGL.Theory.GradientBound

/-!
# OU log-Sobolev / gradient bound (Part 3): `ouFull.GradientInterpolation` (G1)

For `f, h ∈ C_c^∞`, with `k_s = P_s h`, `g_s = P_{t-s} f` (explicit Mehler functions), `Φ(s) = ∫ k_s Γ(g_s)`
is continuous on `[0,t]` and, for `0 < s < t`, has derivative `2 ∫ k_s Γ₂(g_s)`.  The `s`-derivative
of the integrand is `∂_s k = L k`, `∂_s Γ(g_s) = -2 g' (L g)'`; the two Gaussian integrations by parts
needed to identify `Φ'` with `2∫ k Γ₂(g)` are instances of `ibpγ` (all functions are bounded with
bounded `x`-derivatives).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

lemma integrable_of_bd {F : ℝ → ℝ} (hc : Continuous F) (hb : ∃ C, ∀ x, |F x| ≤ C) :
    Integrable F γ := by
  obtain ⟨C, hC⟩ := hb
  refine integrable_lin hc.aestronglyMeasurable (C := |C|) fun x => ?_
  calc |F x| ≤ C := hC x
    _ ≤ |C| * 1 := by simpa using le_abs_self C
    _ ≤ |C| * (1 + |x|) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith [abs_nonneg x]

variable {S : Set ℝ} {w : ℝ → ℝ → ℝ}

lemma Bd.at {s : ℝ} (hw : Bd S w) (hs : s ∈ S) : ∃ C, ∀ x, |w s x| ≤ C := by
  obtain ⟨C, hC⟩ := hw
  exact ⟨C, hC s hs⟩

lemma Bd.rev {t : ℝ} (hw : Bd (Ici 0) w) (hS : ∀ s ∈ S, s ≤ t) :
    Bd S (fun s x => w (t - s) x) := by
  obtain ⟨C, hC⟩ := hw
  exact ⟨C, fun s hs x => hC (t - s) (sub_nonneg.2 (hS s hs)) x⟩

lemma Lin.at {s : ℝ} (hw : Lin S w) (hs : s ∈ S) : ∃ C, ∀ x, |w s x| ≤ C * (1 + |x|) := by
  obtain ⟨C, hC⟩ := hw
  exact ⟨C, hC s hs⟩

/-- the interpolation function in explicit form -/
noncomputable def gPhi (h f : ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ x, m0 h s x * (m1 f (t - s) x * m1 f (t - s) x) ∂γ

lemma gradPhi_eq (f h : ouFull.A₀) (t : ℝ≥0) {s : ℝ} (hs : s ∈ Icc 0 (t : ℝ)) :
    ouFull.gradPhi f h t s = gPhi h.1 f.1 t s := by
  have h0 : 0 ≤ s := hs.1
  have h1 : 0 ≤ (t : ℝ) - s := sub_nonneg.2 hs.2
  unfold FullTriple.gradPhi gPhi
  rw [Pt_eq_m0 h h0, Pt_eq_m0 f h1]
  have hΓ : ouFull.toDiffusionTriple.ΓA (m0 f.1 (t - s)) (m0 f.1 (t - s)) =
      fun x => m1 f.1 (t - s) x * m1 f.1 (t - s) x :=
    ΓA_eq_of_hasDeriv (sm_m0 f.2 _) (d0x f.2 _)
  rw [hΓ]
  rfl

theorem gPhi_continuousOn {h f : ℝ → ℝ} (hh : h ∈ OA₀) (hf : f ∈ OA₀) (t : ℝ) :
    ContinuousOn (gPhi h f t) (Icc 0 t) := by
  obtain ⟨C0, hC0⟩ := m0_bd hh (Icc 0 t)
  obtain ⟨C1, hC1⟩ := (m1_bd hf (S := Ici 0) subset_rfl)
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0 (by simp) 0)
  unfold gPhi
  refine continuousOn_of_dominated (bound := fun _ => C0 * (C1 * C1)) (fun s hs => ?_)
    (fun s hs => ae_of_all _ fun x => ?_) (integrable_const _) (ae_of_all _ fun x => ?_)
  · exact ((m0_cont hh s).mul ((m1_cont hf _).mul (m1_cont hf _))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_mul]
    have hr : (t - s) ∈ Ici (0 : ℝ) := sub_nonneg.2 hs.2
    exact mul_le_mul (hC0 s hs x) (mul_le_mul (hC1 _ hr x) (hC1 _ hr x) (abs_nonneg _) hC10)
      (by positivity) ((abs_nonneg _).trans (hC0 s hs x))
  · exact (m0_cont_s hh x).continuousOn.mul
      (((m1_cont_s hf x).comp (continuous_const.sub continuous_id)).continuousOn.mul
        ((m1_cont_s hf x).comp (continuous_const.sub continuous_id)).continuousOn)

/-- `s`-derivative of the integrand of `gPhi` -/
noncomputable def gH' (h f : ℝ → ℝ) (t s x : ℝ) : ℝ :=
  (m2 h s x - x * m1 h s x) * (m1 f (t - s) x * m1 f (t - s) x) +
    m0 h s x * (2 * m1 f (t - s) x *
      (-(m3 f (t - s) x - x * m2 f (t - s) x - m1 f (t - s) x)))

theorem gPhi_hasDerivAt {h f : ℝ → ℝ} (hh : h ∈ OA₀) (hf : f ∈ OA₀) {t s : ℝ}
    (hs : s ∈ Ioo 0 t) :
    Integrable (fun x => m0 h s x * (m1 f (t - s) x * m1 f (t - s) x)) γ ∧
    Integrable (fun x => m0 h s x * (m2 f (t - s) x ^ 2 + m1 f (t - s) x ^ 2)) γ ∧
    HasDerivAt (gPhi h f t)
      (2 * ∫ x, m0 h s x * (m2 f (t - s) x ^ 2 + m1 f (t - s) x ^ 2) ∂γ) s := by
  set S : Set ℝ := Ioo 0 t with hSdef
  have hS : S ∈ 𝓝 s := Ioo_mem_nhds hs.1 hs.2
  have hS0 : S ⊆ Ici 0 := fun s' hs' => (hs'.1.le : (0:ℝ) ≤ s')
  have hSt : ∀ s' ∈ S, s' ≤ t := fun s' hs' => hs'.2.le
  have b0 := m0_bd hh S
  have b1h := m1_bd hh hS0
  have b2h := m2_bd hh hS0
  have bw : Bd S (fun s x => m1 f (t - s) x) := (m1_bd hf (S := Ici 0) subset_rfl).rev hSt
  have bw1 : Bd S (fun s x => m2 f (t - s) x) := (m2_bd hf (S := Ici 0) subset_rfl).rev hSt
  have bw2 : Bd S (fun s x => m3 f (t - s) x) := (m3_bd hf (S := Ici 0) subset_rfl).rev hSt
  have hr : 0 < t - s := sub_pos.2 hs.2
  -- derivative in `s`
  have hd : ∀ x, ∀ s' ∈ S, HasDerivAt (fun s => m0 h s x * (m1 f (t - s) x * m1 f (t - s) x))
      (gH' h f t s' x) s' := by
    intro x s' hs'
    have hr' : 0 < t - s' := sub_pos.2 hs'.2
    have hw := (hasDerivAt_m1_s hf hr' x).comp s' ((hasDerivAt_id s').const_sub t)
    have hww := hw.mul hw
    have := (hasDerivAt_m0_s hh hs'.1 x).mul hww
    refine (show HasDerivAt (fun s => m0 h s x * (m1 f (t - s) x * m1 f (t - s) x)) _ s' from
      this).congr_deriv ?_
    simp only [gH', Function.comp_apply, Pi.mul_apply]; ring
  have hc : ∀ s' ∈ S, Continuous (fun x => m0 h s' x * (m1 f (t - s') x * m1 f (t - s') x)) :=
    fun s' _ => (m0_cont hh s').mul ((m1_cont hf _).mul (m1_cont hf _))
  have hc' : Continuous (gH' h f t s) := by
    unfold gH'
    have := m0_cont hh s; have := m1_cont hh s; have := m2_cont hh s
    have := m1_cont hf (t - s); have := m2_cont hf (t - s); have := m3_cont hf (t - s)
    fun_prop
  have hb : Lin S (gH' h f t) := by
    unfold gH'
    refine Lin.add (Lin.mul_bd (Lin.sub (Lin.of_bd b2h) b1h.xmul) (bw.mul bw)) ?_
    exact Lin.bd_mul b0 (Lin.bd_mul ((bd_const 2).mul bw) (Lin.neg
      (Lin.sub (Lin.sub (Lin.of_bd bw2) bw1.xmul) (Lin.of_bd bw))))
  obtain ⟨hi', hd'⟩ := hasDerivAt_integral_γ (H := fun s x => m0 h s x * (m1 f (t - s) x *
    m1 f (t - s) x)) hS hc (((Lin.of_bd (b0.mul (bw.mul bw))).at hs)) hc' hd hb
  have hbdK : Bd S (fun s x => m0 h s x * (m2 f (t - s) x ^ 2 + m1 f (t - s) x ^ 2)) := by
    simp only [sq]
    exact b0.mul ((bw1.mul bw1).add (bw.mul bw))
  have hKc : Continuous (fun x => m0 h s x * (m2 f (t - s) x ^ 2 + m1 f (t - s) x ^ 2)) := by
    have := m0_cont hh s; have := m1_cont hf (t - s); have := m2_cont hf (t - s)
    fun_prop
  have hKi : Integrable (fun x => m0 h s x * (m2 f (t - s) x ^ 2 + m1 f (t - s) x ^ 2)) γ :=
    integrable_of_bd hKc (hbdK.at hs)
  refine ⟨integrable_of_bd (by
      have := m0_cont hh s; have := m1_cont hf (t - s); fun_prop) ((b0.mul (bw.mul bw)).at hs),
    hKi, ?_⟩
  refine (show HasDerivAt (gPhi h f t) _ s from hd'.congr_deriv ?_)
  -- identification of the derivative by two Gaussian integrations by parts
  set G₁ : ℝ → ℝ := fun x => m1 h s x * (m1 f (t - s) x * m1 f (t - s) x) with hG₁
  set G₁' : ℝ → ℝ := fun x => m2 h s x * (m1 f (t - s) x * m1 f (t - s) x) +
    m1 h s x * (m2 f (t - s) x * m1 f (t - s) x + m1 f (t - s) x * m2 f (t - s) x) with hG₁'
  set G₂ : ℝ → ℝ := fun x => m0 h s x * (m1 f (t - s) x * m2 f (t - s) x) with hG₂
  set G₂' : ℝ → ℝ := fun x => m1 h s x * (m1 f (t - s) x * m2 f (t - s) x) +
    m0 h s x * (m2 f (t - s) x * m2 f (t - s) x + m1 f (t - s) x * m3 f (t - s) x) with hG₂'
  have hd1 : ∀ x, HasDerivAt G₁ (G₁' x) x := fun x =>
    (d1x hh s x).mul ((d1x hf (t - s) x).mul (d1x hf (t - s) x))
  have hd2 : ∀ x, HasDerivAt G₂ (G₂' x) x := fun x =>
    (d0x hh s x).mul ((d1x hf (t - s) x).mul (d2x hf (t - s) x))
  have bG₁ : ∃ C, ∀ x, |G₁ x| ≤ C := (b1h.mul (bw.mul bw)).at hs
  have bG₁' : ∃ C, ∀ x, |G₁' x| ≤ C :=
    ((b2h.mul (bw.mul bw)).add (b1h.mul ((bw1.mul bw).add (bw.mul bw1)))).at hs
  have bG₂ : ∃ C, ∀ x, |G₂ x| ≤ C := (b0.mul (bw.mul bw1)).at hs
  have bG₂' : ∃ C, ∀ x, |G₂' x| ≤ C :=
    ((b1h.mul (bw.mul bw1)).add (b0.mul ((bw1.mul bw1).add (bw.mul bw2)))).at hs
  obtain ⟨i1, z1⟩ := ibpγ hd1 bG₁ bG₁'
  obtain ⟨i2, z2⟩ := ibpγ hd2 bG₂ bG₂'
  have e : gH' h f t s = fun x => ((G₁' x - x * G₁ x) - 2 * (G₂' x - x * G₂ x)) +
      2 * (m0 h s x * (m2 f (t - s) x ^ 2 + m1 f (t - s) x ^ 2)) := by
    funext x
    simp only [gH', hG₁, hG₁', hG₂, hG₂']
    ring
  have i2' : Integrable (fun x => 2 * (G₂' x - x * G₂ x)) γ := i2.const_mul 2
  have h12 : Integrable (fun x => (G₁' x - x * G₁ x) - 2 * (G₂' x - x * G₂ x)) γ := i1.sub i2'
  have h3 : Integrable (fun x => 2 * (m0 h s x * (m2 f (t - s) x ^ 2 + m1 f (t - s) x ^ 2))) γ :=
    hKi.const_mul 2
  rw [e, integral_add h12 h3, integral_sub i1 i2', integral_const_mul, integral_const_mul, z1, z2]
  ring

/-- **G1 for the OU triple**: the gradient interpolation hypothesis is a theorem. -/
theorem ouFull_GradientInterpolation : ouFull.GradientInterpolation where
  continuousOn := fun f h _ t =>
    (gPhi_continuousOn h.2 f.2 (t : ℝ)).congr fun s hs => gradPhi_eq f h t hs
  hasDerivAt := fun f h _ t s hs => by
    obtain ⟨i1, i2, hd⟩ := gPhi_hasDerivAt h.2 f.2 hs
    have hP : ouFull.Pt s.toNNReal h = m0 h.1 s := Pt_eq_m0 h hs.1.le
    have hr : 0 ≤ (t : ℝ) - s := sub_nonneg.2 hs.2.le
    have hQ : ouFull.Pt ((t : ℝ) - s).toNNReal f = m0 f.1 ((t : ℝ) - s) := Pt_eq_m0 f hr
    have hΓ : ouFull.toDiffusionTriple.ΓA (m0 f.1 (t - s)) (m0 f.1 (t - s)) =
        fun x => m1 f.1 (t - s) x * m1 f.1 (t - s) x :=
      ΓA_eq_of_hasDeriv (sm_m0 f.2 _) (d0x f.2 _)
    have hΓ₂ : ∀ x, ouFull.toDiffusionTriple.Γ₂ (m0 f.1 (t - s)) (m0 f.1 (t - s)) x =
        m2 f.1 (t - s) x ^ 2 + m1 f.1 (t - s) x ^ 2 := fun x =>
      Γ₂_eq_of_hasDeriv (sm_m0 f.2 _) (d0x f.2 _) (d1x f.2 _) x
    rw [hP, hQ, hΓ]
    simp only [hΓ₂]
    refine ⟨i1, i2, ?_⟩
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs' using
      gradPhi_eq f h t ⟨hs'.1.le, hs'.2.le⟩

end MarkovTriple.BGL.Instances.OU
