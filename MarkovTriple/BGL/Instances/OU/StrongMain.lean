import Mathlib
import MarkovTriple.BGL.Instances.OU.StrongBase

/-!
# OU strong gradient bound (Part 2): `ouFull.StrongInterpolation` and BGL Thm 3.3.18 for OU

For `f, h ∈ C_c^∞`, `k_s = P_s h = m₀(h)(s)`, `g_s = P_{t-s} f` (Mehler functions), `q_s = (∂_x g_s)²`,
`Φ_ε(s) = ∫ k_s ψ_ε(q_s) dγ` is continuous on `[0,t]` and, for `0<s<t`, differentiable with derivative
`∫ k_s [2ψ_ε'(q)(g''² + g'²) + ψ_ε''(q)(2g'g'')²]`, which is `∫ k_s (L(ψ_ε∘Γg) − 2ψ_ε'(Γg)Γ(g,Lg))`
(two Gaussian integrations by parts, `ibp_L`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

variable {ε : ℝ}

/-- the interpolation function in explicit form -/
noncomputable def sPhi (ε : ℝ) (h f : ℝ → ℝ) (t s : ℝ) : ℝ :=
  ∫ x, m0 h s x * psiS ε (m1 f (t - s) x * m1 f (t - s) x) ∂γ

/-- the explicit derivative integrand factor `2ψ'(q)(g''²+g'²) + ψ''(q)(2g'g'')²`. -/
noncomputable def sD (ε : ℝ) (f : ℝ → ℝ) (τ x : ℝ) : ℝ :=
  2 * deriv (psiS ε) (m1 f τ x * m1 f τ x) * (m2 f τ x ^ 2 + m1 f τ x ^ 2) +
    deriv (deriv (psiS ε)) (m1 f τ x * m1 f τ x) * (2 * m1 f τ x * m2 f τ x) ^ 2

lemma psi_q_bd (hε : 0 < ε) {f : ℝ → ℝ} (hf : f ∈ OA₀) : ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ, 0 ≤ τ → ∀ x,
    |psiS ε (m1 f τ x * m1 f τ x)| ≤ B ∧ |deriv (psiS ε) (m1 f τ x * m1 f τ x)| ≤ B ∧
      |deriv (deriv (psiS ε)) (m1 f τ x * m1 f τ x)| ≤ B := by
  obtain ⟨C1, hC1⟩ := m1_bd hf (S := Ici 0) subset_rfl
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0 (by simp) 0)
  obtain ⟨B, hB0, hB⟩ := psiS_bounds hε (C1 * C1)
  refine ⟨B, hB0, fun τ hτ x => hB _ ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hC1 τ hτ x) (hC1 τ hτ x) (abs_nonneg _) hC10

lemma strongPhi_eq (hε : 0 < ε) (f h : ouFull.A₀) (t : ℝ≥0) {s : ℝ} (hs : s ∈ Icc 0 (t : ℝ)) :
    ouFull.strongPhi ε f h t s = sPhi ε h.1 f.1 t s := by
  have h0 : 0 ≤ s := hs.1
  have h1 : 0 ≤ (t : ℝ) - s := sub_nonneg.2 hs.2
  unfold FullTriple.strongPhi sPhi
  rw [Pt_eq_m0 h h0, Pt_eq_m0 f h1]
  have hΓ : ouFull.toDiffusionTriple.ΓA (m0 f.1 (t - s)) (m0 f.1 (t - s)) =
      fun x => m1 f.1 (t - s) x * m1 f.1 (t - s) x :=
    ΓA_eq_of_hasDeriv (sm_m0 f.2 _) (d0x f.2 _)
  show ∫ x, m0 h.1 s x * psiS ε (ouFull.toDiffusionTriple.ΓA (m0 f.1 (t - s)) (m0 f.1 (t - s)) x) ∂γ = _
  rw [hΓ]

theorem sPhi_continuousOn (hε : 0 < ε) {h f : ℝ → ℝ} (hh : h ∈ OA₀) (hf : f ∈ OA₀) (t : ℝ) :
    ContinuousOn (sPhi ε h f t) (Icc 0 t) := by
  obtain ⟨C0, hC0'⟩ := m0_bd hh (Ici 0)
  have hC0 : ∀ s ∈ Icc 0 t, ∀ x, |m0 h s x| ≤ C0 := fun s hs x => hC0' s hs.1 x
  obtain ⟨B, hB0, hB⟩ := psi_q_bd hε hf
  have hC00 : 0 ≤ C0 := (abs_nonneg _).trans (hC0' 0 (by simp) 0)
  unfold sPhi
  have hψc : Continuous (psiS ε) := (psiS_smooth hε).continuous
  refine continuousOn_of_dominated (bound := fun _ => C0 * B) (fun s hs => ?_)
    (fun s hs => ae_of_all _ fun x => ?_) (integrable_const _) (ae_of_all _ fun x => ?_)
  · exact ((m0_cont hh s).mul (hψc.comp ((m1_cont hf _).mul (m1_cont hf _)))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul]
    have hr : 0 ≤ t - s := sub_nonneg.2 hs.2
    exact mul_le_mul (hC0 s hs x) (hB _ hr x).1 (abs_nonneg _) hC00
  · exact (m0_cont_s hh x).continuousOn.mul
      (hψc.comp_continuousOn (((m1_cont_s hf x).comp (continuous_const.sub continuous_id)).continuousOn.mul
        ((m1_cont_s hf x).comp (continuous_const.sub continuous_id)).continuousOn))

/-- the `s`-derivative of the integrand -/
noncomputable def sH' (ε : ℝ) (h f : ℝ → ℝ) (t s x : ℝ) : ℝ :=
  (m2 h s x - x * m1 h s x) * psiS ε (m1 f (t - s) x * m1 f (t - s) x) +
    m0 h s x * (deriv (psiS ε) (m1 f (t - s) x * m1 f (t - s) x) *
      ((-(m3 f (t - s) x - x * m2 f (t - s) x - m1 f (t - s) x)) * m1 f (t - s) x +
        m1 f (t - s) x * (-(m3 f (t - s) x - x * m2 f (t - s) x - m1 f (t - s) x))))

theorem sPhi_hasDerivAt (hε : 0 < ε) {h f : ℝ → ℝ} (hh : h ∈ OA₀) (hf : f ∈ OA₀) {t s : ℝ}
    (hs : s ∈ Ioo 0 t) :
    Integrable (fun x => m0 h s x * psiS ε (m1 f (t - s) x * m1 f (t - s) x)) γ ∧
    Integrable (fun x => m0 h s x * sD ε f (t - s) x) γ ∧
    HasDerivAt (sPhi ε h f t) (∫ x, m0 h s x * sD ε f (t - s) x ∂γ) s := by
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
  obtain ⟨B, hB0, hB⟩ := psi_q_bd hε hf
  have bψ : Bd S (fun s x => psiS ε (m1 f (t - s) x * m1 f (t - s) x)) :=
    ⟨B, fun s' hs' x => (hB (t - s') (sub_nonneg.2 (hSt s' hs')) x).1⟩
  have bψ1 : Bd S (fun s x => deriv (psiS ε) (m1 f (t - s) x * m1 f (t - s) x)) :=
    ⟨B, fun s' hs' x => (hB (t - s') (sub_nonneg.2 (hSt s' hs')) x).2.1⟩
  have bψ2 : Bd S (fun s x => deriv (deriv (psiS ε)) (m1 f (t - s) x * m1 f (t - s) x)) :=
    ⟨B, fun s' hs' x => (hB (t - s') (sub_nonneg.2 (hSt s' hs')) x).2.2⟩
  have hψd : Differentiable ℝ (psiS ε) := (psiS_smooth hε).differentiable (by simp)
  have hψc : Continuous (psiS ε) := (psiS_smooth hε).continuous
  have hψ1c : Continuous (deriv (psiS ε)) := (contDiff_deriv_psiS hε).continuous
  have hψ2c : Continuous (deriv (deriv (psiS ε))) := (contDiff_deriv2_psiS hε).continuous
  -- derivative in `s`
  have hd : ∀ x, ∀ s' ∈ S, HasDerivAt
      (fun s => m0 h s x * psiS ε (m1 f (t - s) x * m1 f (t - s) x)) (sH' ε h f t s' x) s' := by
    intro x s' hs'
    have hr' : 0 < t - s' := sub_pos.2 hs'.2
    have hw := (hasDerivAt_m1_s hf hr' x).comp s' ((hasDerivAt_id s').const_sub t)
    have hww := hw.mul hw
    have hψ := (hψd (m1 f (t - s') x * m1 f (t - s') x)).hasDerivAt.comp s' hww
    have := (hasDerivAt_m0_s hh hs'.1 x).mul hψ
    refine (show HasDerivAt (fun s => m0 h s x * psiS ε (m1 f (t - s) x * m1 f (t - s) x)) _ s'
      from this).congr_deriv ?_
    simp only [sH', Function.comp_apply, Pi.mul_apply]; ring
  have hc : ∀ s' ∈ S, Continuous (fun x => m0 h s' x * psiS ε (m1 f (t - s') x * m1 f (t - s') x)) :=
    fun s' _ => (m0_cont hh s').mul (hψc.comp ((m1_cont hf _).mul (m1_cont hf _)))
  have hc' : Continuous (sH' ε h f t s) := by
    unfold sH'
    have := m0_cont hh s; have := m1_cont hh s; have := m2_cont hh s
    have := m1_cont hf (t - s); have := m2_cont hf (t - s); have := m3_cont hf (t - s)
    have c1 : Continuous fun x => m1 f (t - s) x * m1 f (t - s) x := by fun_prop
    have c2 := hψc.comp c1
    have c3 := hψ1c.comp c1
    fun_prop
  have hb : Lin S (sH' ε h f t) := by
    unfold sH'
    refine Lin.add (Lin.mul_bd (Lin.sub (Lin.of_bd b2h) b1h.xmul) bψ) ?_
    exact Lin.bd_mul b0 (Lin.bd_mul bψ1 (Lin.add
      (Lin.mul_bd (Lin.neg (Lin.sub (Lin.sub (Lin.of_bd bw2) bw1.xmul) (Lin.of_bd bw))) bw)
      (Lin.bd_mul bw (Lin.neg (Lin.sub (Lin.sub (Lin.of_bd bw2) bw1.xmul) (Lin.of_bd bw))))))
  obtain ⟨hi', hd'⟩ := hasDerivAt_integral_γ (H := fun s x => m0 h s x *
    psiS ε (m1 f (t - s) x * m1 f (t - s) x)) hS hc ((Lin.of_bd (b0.mul bψ)).at hs) hc' hd hb
  -- the explicit integrand `sD`
  have bsD : ∃ C, ∀ x, |sD ε f (t - s) x| ≤ C := by
    have this : Bd S (fun s x => 2 * deriv (psiS ε) (m1 f (t - s) x * m1 f (t - s) x) *
        (m2 f (t - s) x * m2 f (t - s) x + m1 f (t - s) x * m1 f (t - s) x) +
        deriv (deriv (psiS ε)) (m1 f (t - s) x * m1 f (t - s) x) *
        (2 * m1 f (t - s) x * m2 f (t - s) x * (2 * m1 f (t - s) x * m2 f (t - s) x))) :=
      ((bd_const 2).mul bψ1 |>.mul (bw1.mul bw1 |>.add (bw.mul bw))).add
        (bψ2.mul (((bd_const 2).mul bw).mul bw1 |>.mul (((bd_const 2).mul bw).mul bw1)))
    obtain ⟨C, hC⟩ := this.at hs
    refine ⟨C, fun x => ?_⟩
    have e : sD ε f (t - s) x = 2 * deriv (psiS ε) (m1 f (t - s) x * m1 f (t - s) x) *
        (m2 f (t - s) x * m2 f (t - s) x + m1 f (t - s) x * m1 f (t - s) x) +
        deriv (deriv (psiS ε)) (m1 f (t - s) x * m1 f (t - s) x) *
        (2 * m1 f (t - s) x * m2 f (t - s) x * (2 * m1 f (t - s) x * m2 f (t - s) x)) := by
      unfold sD; ring
    rw [e]; exact hC x
  have hsDc : Continuous (sD ε f (t - s)) := by
    unfold sD
    have := m1_cont hf (t - s); have := m2_cont hf (t - s)
    have c1 : Continuous fun x => m1 f (t - s) x * m1 f (t - s) x := by fun_prop
    have c3 := hψ1c.comp c1
    have c4 := hψ2c.comp c1
    fun_prop
  have hsDi : Integrable (fun x => m0 h s x * sD ε f (t - s) x) γ :=
    integrable_of_bd ((m0_cont hh s).mul hsDc) ((b0.at hs).elim fun C0 hC0 => bsD.elim fun C1 hC1 =>
      ⟨C0 * C1, fun x => by
        rw [abs_mul]
        exact mul_le_mul (hC0 x) (hC1 x) (abs_nonneg _) ((abs_nonneg _).trans (hC0 x))⟩)
  refine ⟨integrable_of_bd (by
      have := m0_cont hh s; have := m1_cont hf (t - s)
      have c1 : Continuous fun x => m1 f (t - s) x * m1 f (t - s) x := by fun_prop
      exact (m0_cont hh s).mul (hψc.comp c1)) ((b0.mul bψ).at hs), hsDi, ?_⟩
  refine (show HasDerivAt (sPhi ε h f t) _ s from hd'.congr_deriv ?_)
  -- identification of the derivative by Gaussian integrations by parts
  have hτ : 0 < t - s := sub_pos.2 hs.2
  set Q : ℝ → ℝ := fun x => m1 f (t - s) x * m1 f (t - s) x with hQ
  set Q1 : ℝ → ℝ := fun x => m2 f (t - s) x * m1 f (t - s) x + m1 f (t - s) x * m2 f (t - s) x
    with hQ1
  set Q2 : ℝ → ℝ := fun x => (m3 f (t - s) x * m1 f (t - s) x + m2 f (t - s) x * m2 f (t - s) x) +
    (m2 f (t - s) x * m2 f (t - s) x + m1 f (t - s) x * m3 f (t - s) x) with hQ2
  have hdQ : ∀ x, HasDerivAt Q (Q1 x) x := fun x => (d1x hf (t - s) x).mul (d1x hf (t - s) x)
  have hdQ1 : ∀ x, HasDerivAt Q1 (Q2 x) x := fun x =>
    ((d2x hf (t - s) x).mul (d1x hf (t - s) x)).add ((d1x hf (t - s) x).mul (d2x hf (t - s) x))
  set G : ℝ → ℝ := fun x => psiS ε (Q x) with hG
  set G1 : ℝ → ℝ := fun x => deriv (psiS ε) (Q x) * Q1 x with hG1
  set G2 : ℝ → ℝ := fun x => deriv (deriv (psiS ε)) (Q x) * Q1 x * Q1 x +
    deriv (psiS ε) (Q x) * Q2 x with hG2
  have hdG : ∀ x, HasDerivAt G (G1 x) x := fun x =>
    (hψd (Q x)).hasDerivAt.comp x (hdQ x)
  have hdG1 : ∀ x, HasDerivAt G1 (G2 x) x := fun x => by
    have h1 : HasDerivAt (deriv (psiS ε)) (deriv (deriv (psiS ε)) (Q x)) (Q x) :=
      (((contDiff_deriv_psiS hε).differentiable (by simp)) (Q x)).hasDerivAt
    have := (h1.comp x (hdQ x)).mul (hdQ1 x)
    refine (show HasDerivAt G1 _ x from this).congr_deriv ?_
    simp only [hG2, Function.comp_apply]
  have bG : ∃ C, ∀ x, |G x| ≤ C := (bψ.at hs)
  have bQ1 : ∃ C, ∀ x, |Q1 x| ≤ C := ((bw1.mul bw).add (bw.mul bw1)).at hs
  have bQ2 : ∃ C, ∀ x, |Q2 x| ≤ C :=
    (((bw2.mul bw).add (bw1.mul bw1)).add ((bw1.mul bw1).add (bw.mul bw2))).at hs
  have bG1 : ∃ C, ∀ x, |G1 x| ≤ C := (bψ1.mul ((bw1.mul bw).add (bw.mul bw1))).at hs
  have bG2 : ∃ C, ∀ x, |G2 x| ≤ C :=
    (((bψ2.mul ((bw1.mul bw).add (bw.mul bw1))).mul ((bw1.mul bw).add (bw.mul bw1))).add
      (bψ1.mul (((bw2.mul bw).add (bw1.mul bw1)).add ((bw1.mul bw1).add (bw.mul bw2))))).at hs
  obtain ⟨j1, j2, jeq⟩ := ibp_L (a0 := m0 h s) (a1 := m1 h s) (a2 := m2 h s)
    (d0x hh s) (d1x hh s) hdG hdG1 (b0.at hs) (b1h.at hs) (b2h.at hs) bG bG1 bG2
  -- decomposition of the derivative integrand
  have hP : ∀ x, sH' ε h f t s x =
      (m2 h s x - x * m1 h s x) * G x + (m0 h s x * sD ε f (t - s) x -
        m0 h s x * (G2 x - x * G1 x)) := by
    intro x
    simp only [sH', sD, hG, hG1, hG2, hQ, hQ1, hQ2]
    ring
  have hsub : Integrable (fun x => m0 h s x * sD ε f (t - s) x - m0 h s x * (G2 x - x * G1 x)) γ :=
    hsDi.sub j2
  have e : (fun x => sH' ε h f t s x) = fun x =>
      (m2 h s x - x * m1 h s x) * G x + (m0 h s x * sD ε f (t - s) x -
        m0 h s x * (G2 x - x * G1 x)) := funext hP
  show ∫ x, sH' ε h f t s x ∂γ = _
  rw [e, integral_add j1 hsub, integral_sub hsDi j2, jeq]
  simp

end MarkovTriple.BGL.Instances.OU
