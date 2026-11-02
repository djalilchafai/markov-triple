import Mathlib
import MarkovTriple.BGL.Instances.OU.LSIGrad
import MarkovTriple.BGL.Theory.LogSobolev

/-!
# OU log-Sobolev / gradient bound (Part 4): `ouFull.EntropyInterpolation` (G3), entropy and Fisher parts

With `g_s = ε + P_s φ` (`ε ≤ g_s ≤ ε + M` everywhere), `e(s) = ∫ g log g`, `I(s) = ∫ g'²/g`:
continuity on `[0,∞)`, `e' = -I` on `(0,∞)` (one Gaussian IBP with `G = g'(log g + 1)`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal Real
open MarkovTriple.Sanity.OU hiding A₀

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.OU

lemma nonneg_of_ae {f : ℝ → ℝ} (hf : Continuous f) (h : 0 ≤ᵐ[γ] f) : ∀ x, 0 ≤ f x := by
  have h1 : (fun x => min (f x) 0) =ᵐ[γ] fun _ => (0 : ℝ) :=
    h.mono fun x hx => min_eq_right hx
  have := (Continuous.ae_eq_iff_eq γ (hf.min continuous_const) continuous_const).1 h1
  intro x
  have := congrFun this x
  simpa using this

noncomputable def eE (φ : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  ∫ x, (ε + m0 φ s x) * Real.log (ε + m0 φ s x) ∂γ

noncomputable def eI (φ : ℝ → ℝ) (ε s : ℝ) : ℝ :=
  ∫ x, m1 φ s x * m1 φ s x / (ε + m0 φ s x) ∂γ

section range

variable {φ : ℝ → ℝ} {ε M : ℝ} {S : Set ℝ}

lemma m0_nonneg (h0 : ∀ x, 0 ≤ φ x) (s x : ℝ) : 0 ≤ m0 φ s x :=
  integral_nonneg fun _y => h0 _

lemma m0_le (h0 : ∀ x, 0 ≤ φ x) (hM : ∀ x, φ x ≤ M) (s x : ℝ) : m0 φ s x ≤ M := by
  have := Uf_bound (φ := φ) (B := M) (fun y => by rw [abs_of_nonneg (h0 y)]; exact hM y) s x
  exact (le_abs_self _).trans this

lemma g_range (h0 : ∀ x, 0 ≤ φ x) (hM : ∀ x, φ x ≤ M) (_hε : 0 < ε) (s x : ℝ) :
    ε + m0 φ s x ∈ Icc ε (ε + M) :=
  ⟨by linarith [m0_nonneg h0 s x], by linarith [m0_le h0 hM s x]⟩

lemma g_pos (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) (s x : ℝ) : 0 < ε + m0 φ s x := by
  linarith [m0_nonneg h0 s x]

lemma g_bd (hφ : φ ∈ OA₀) (ε : ℝ) (S : Set ℝ) : Bd S (fun s x => ε + m0 φ s x) :=
  (bd_const ε).add (m0_bd hφ S)

lemma ginv_bd (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) (S : Set ℝ) :
    Bd S (fun s x => (ε + m0 φ s x)⁻¹) := by
  refine ⟨ε⁻¹, fun s _ x => ?_⟩
  rw [abs_of_pos (inv_pos.2 (g_pos h0 hε s x))]
  exact inv_anti₀ hε (by linarith [m0_nonneg h0 s x])

lemma log_bd (h0 : ∀ x, 0 ≤ φ x) (hM : ∀ x, φ x ≤ M) (hε : 0 < ε) (S : Set ℝ) :
    Bd S (fun s x => Real.log (ε + m0 φ s x)) := by
  refine ⟨|Real.log ε| + |Real.log (ε + M)|, fun s _ x => ?_⟩
  have hr := g_range h0 hM hε s x
  have hg := g_pos h0 hε s x
  have h1 : Real.log ε ≤ Real.log (ε + m0 φ s x) := Real.log_le_log hε hr.1
  have h2 : Real.log (ε + m0 φ s x) ≤ Real.log (ε + M) := Real.log_le_log hg hr.2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log ε), abs_nonneg (Real.log (ε + M))]
  · linarith [le_abs_self (Real.log (ε + M)), abs_nonneg (Real.log ε)]

lemma log_cont (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) (s : ℝ) :
    Continuous (fun x => Real.log (ε + m0 φ s x)) :=
  ((continuous_const.add (m0_cont hφ s))).log fun x => (g_pos h0 hε s x).ne'

end range

section E

variable {φ : ℝ → ℝ} {ε M : ℝ}

theorem eE_continuousOn (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hM : ∀ x, φ x ≤ M) (hε : 0 < ε) :
    ContinuousOn (eE φ ε) (Ici 0) := by
  obtain ⟨C, hC⟩ := ((g_bd hφ ε (Ici 0)).mul (log_bd h0 hM hε (Ici 0)))
  unfold eE
  refine continuousOn_of_dominated (bound := fun _ => C) (fun s hs => ?_)
    (fun s hs => ae_of_all _ fun x => ?_) (integrable_const _) (ae_of_all _ fun x => ?_)
  · exact ((continuous_const.add (m0_cont hφ s)).mul (log_cont hφ h0 hε s)).aestronglyMeasurable
  · simpa using hC s hs x
  · exact ((continuous_const.add (m0_cont_s hφ x)).mul
      ((continuous_const.add (m0_cont_s hφ x)).log fun s => (g_pos h0 hε s x).ne')).continuousOn

theorem eI_continuousOn (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) :
    ContinuousOn (eI φ ε) (Ici 0) := by
  obtain ⟨C, hC⟩ := (((m1_bd hφ (S := Ici 0) subset_rfl).mul (m1_bd hφ (S := Ici 0) subset_rfl)).mul
    (ginv_bd (φ := φ) h0 hε (Ici 0)))
  unfold eI
  refine continuousOn_of_dominated (bound := fun _ => C) (fun s hs => ?_)
    (fun s hs => ae_of_all _ fun x => ?_) (integrable_const _) (ae_of_all _ fun x => ?_)
  · exact (((m1_cont hφ s).mul (m1_cont hφ s)).div (continuous_const.add (m0_cont hφ s))
      fun x => (g_pos h0 hε s x).ne').aestronglyMeasurable
  · simpa [div_eq_mul_inv] using hC s hs x
  · exact (((m1_cont_s hφ x).mul (m1_cont_s hφ x)).div (continuous_const.add (m0_cont_s hφ x))
      fun s => (g_pos h0 hε s x).ne').continuousOn

theorem eE_hasDerivAt (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hM : ∀ x, φ x ≤ M) (hε : 0 < ε)
    {s : ℝ} (hs : 0 < s) : HasDerivAt (eE φ ε) (-eI φ ε s) s := by
  set S : Set ℝ := Ioi 0 with hSdef
  have hS : S ∈ 𝓝 s := Ioi_mem_nhds hs
  have hS0 : S ⊆ Ici 0 := fun s' hs' => (le_of_lt hs' : (0:ℝ) ≤ s')
  have b1 := m1_bd hφ hS0
  have b2 := m2_bd hφ hS0
  have bl := log_bd h0 hM hε S
  have bg := g_bd hφ ε S
  set H' : ℝ → ℝ → ℝ := fun s x => (m2 φ s x - x * m1 φ s x) * (Real.log (ε + m0 φ s x) + 1)
    with hH'
  have hd : ∀ x, ∀ s' ∈ S, HasDerivAt (fun s => (ε + m0 φ s x) * Real.log (ε + m0 φ s x))
      (H' s' x) s' := by
    intro x s' hs'
    have hg := (hasDerivAt_m0_s hφ hs' x).const_add ε
    have hne : ε + m0 φ s' x ≠ 0 := (g_pos h0 hε s' x).ne'
    have := hg.mul (hg.log hne)
    refine this.congr_deriv ?_
    simp only [hH']
    field_simp
  have hc' : Continuous (H' s) := by
    simp only [hH']
    have := m1_cont hφ s; have := m2_cont hφ s; have := log_cont hφ h0 hε s
    fun_prop
  obtain ⟨hi', hd'⟩ := hasDerivAt_integral_γ (H := fun s x => (ε + m0 φ s x) *
    Real.log (ε + m0 φ s x)) hS
    (fun s' _ => (continuous_const.add (m0_cont hφ s')).mul (log_cont hφ h0 hε s'))
    ((Lin.of_bd (bg.mul bl)).at hs)
    hc' hd (by
      simp only [hH']
      exact Lin.mul_bd (Lin.sub (Lin.of_bd b2) b1.xmul) (bl.add (bd_const 1)))
  refine (show HasDerivAt (eE φ ε) _ s from hd'.congr_deriv ?_)
  -- IBP with `G = g' (log g + 1)`
  set G : ℝ → ℝ := fun x => m1 φ s x * (Real.log (ε + m0 φ s x) + 1) with hG
  set G' : ℝ → ℝ := fun x => m2 φ s x * (Real.log (ε + m0 φ s x) + 1) +
    m1 φ s x * (m1 φ s x * (ε + m0 φ s x)⁻¹) with hG'
  have hdG : ∀ x, HasDerivAt G (G' x) x := by
    intro x
    have hne : ε + m0 φ s x ≠ 0 := (g_pos h0 hε s x).ne'
    have := (d1x hφ s x).mul ((((d0x hφ s x).const_add ε).log hne).add_const 1)
    refine this.congr_deriv ?_
    simp only [hG', div_eq_mul_inv]
  have bGG : ∃ C, ∀ x, |G x| ≤ C := (b1.mul (bl.add (bd_const 1))).at hs
  have bGG' : ∃ C, ∀ x, |G' x| ≤ C :=
    ((b2.mul (bl.add (bd_const 1))).add (b1.mul (b1.mul (ginv_bd h0 hε S)))).at hs
  obtain ⟨i1, z1⟩ := ibpγ hdG bGG bGG'
  have hi2 : Integrable (fun x => m1 φ s x * m1 φ s x / (ε + m0 φ s x)) γ := by
    refine integrable_of_bd ?_ (by
      obtain ⟨C, hC⟩ := ((b1.mul b1).mul (ginv_bd (φ := φ) h0 hε S)).at hs
      exact ⟨C, fun x => by simpa [div_eq_mul_inv] using hC x⟩)
    exact ((m1_cont hφ s).mul (m1_cont hφ s)).div (continuous_const.add (m0_cont hφ s))
      fun x => (g_pos h0 hε s x).ne'
  have e : H' s = fun x => (G' x - x * G x) - m1 φ s x * m1 φ s x / (ε + m0 φ s x) := by
    funext x
    have hne : ε + m0 φ s x ≠ 0 := (g_pos h0 hε s x).ne'
    simp only [hH', hG, hG']
    field_simp
    ring
  rw [e, integral_sub i1 hi2, z1]
  simp [eI]

end E

section I

variable {φ : ℝ → ℝ} {ε M : ℝ}

/-- `F' = (log g)'` -/
noncomputable def F1 (φ : ℝ → ℝ) (ε s x : ℝ) : ℝ := m1 φ s x * (ε + m0 φ s x)⁻¹

/-- `F'' = (log g)''` -/
noncomputable def F2 (φ : ℝ → ℝ) (ε s x : ℝ) : ℝ :=
  (m2 φ s x * (ε + m0 φ s x) - m1 φ s x * m1 φ s x) *
    ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹)

/-- the integrand of `J = ∫ g Γ₂(log g)` -/
noncomputable def Kj (φ : ℝ → ℝ) (ε s x : ℝ) : ℝ :=
  (ε + m0 φ s x) * (F2 φ ε s x ^ 2 + F1 φ ε s x ^ 2)

noncomputable def eJ (φ : ℝ → ℝ) (ε s : ℝ) : ℝ := ∫ x, Kj φ ε s x ∂γ

lemma hasDerivAt_ginv (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) (s x : ℝ) :
    HasDerivAt (fun x => (ε + m0 φ s x)⁻¹)
      (-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹)) x := by
  have hne : ε + m0 φ s x ≠ 0 := (g_pos h0 hε s x).ne'
  have := ((d0x hφ s x).const_add ε).inv hne
  refine this.congr_deriv ?_
  field_simp

lemma hasDerivAt_log_g (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) (s x : ℝ) :
    HasDerivAt (fun x => Real.log (ε + m0 φ s x)) (F1 φ ε s x) x := by
  have hne : ε + m0 φ s x ≠ 0 := (g_pos h0 hε s x).ne'
  have := ((d0x hφ s x).const_add ε).log hne
  refine this.congr_deriv ?_
  simp [F1, div_eq_mul_inv]

lemma hasDerivAt_F1 (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) (s x : ℝ) :
    HasDerivAt (F1 φ ε s) (F2 φ ε s x) x := by
  have hne : ε + m0 φ s x ≠ 0 := (g_pos h0 hε s x).ne'
  have := (d1x hφ s x).mul (hasDerivAt_ginv hφ h0 hε s x)
  refine (show HasDerivAt (F1 φ ε s) _ x from this).congr_deriv ?_
  simp only [F2]
  field_simp
  ring

lemma F1_bd (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) {S : Set ℝ} (hS : S ⊆ Ici 0) :
    Bd S (F1 φ ε) := (m1_bd hφ hS).mul (ginv_bd h0 hε S)

lemma F2_bd (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) {S : Set ℝ} (hS : S ⊆ Ici 0) :
    Bd S (F2 φ ε) :=
  (((m2_bd hφ hS).mul (g_bd hφ ε S)).sub ((m1_bd hφ hS).mul (m1_bd hφ hS))).mul
    ((ginv_bd h0 hε S).mul (ginv_bd h0 hε S))

lemma F1_cont (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) (s : ℝ) : Continuous (F1 φ ε s) := by
  unfold F1
  have hg : Continuous (fun x => (ε + m0 φ s x)⁻¹) :=
    ((continuous_const.add (m0_cont hφ s))).inv₀ fun x => (g_pos h0 hε s x).ne'
  exact (m1_cont hφ s).mul hg

lemma F2_cont (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε) (s : ℝ) : Continuous (F2 φ ε s) := by
  unfold F2
  have hg : Continuous (fun x => (ε + m0 φ s x)⁻¹) :=
    ((continuous_const.add (m0_cont hφ s))).inv₀ fun x => (g_pos h0 hε s x).ne'
  exact (((m2_cont hφ s).mul (continuous_const.add (m0_cont hφ s))).sub
    ((m1_cont hφ s).mul (m1_cont hφ s))).mul (hg.mul hg)

end I

section I2

variable {φ : ℝ → ℝ} {ε M : ℝ}

theorem eI_hasDerivAt (hφ : φ ∈ OA₀) (h0 : ∀ x, 0 ≤ φ x) (hε : 0 < ε)
    {s : ℝ} (hs : 0 < s) :
    Integrable (Kj φ ε s) γ ∧ HasDerivAt (eI φ ε) (-2 * eJ φ ε s) s := by
  set S : Set ℝ := Ioi 0 with hSdef
  have hS : S ∈ 𝓝 s := Ioi_mem_nhds hs
  have hS0 : S ⊆ Ici 0 := fun s' hs' => (le_of_lt hs' : (0:ℝ) ≤ s')
  have b0 := m0_bd hφ S
  have b1 := m1_bd hφ hS0
  have b2 := m2_bd hφ hS0
  have b3 := m3_bd hφ hS0
  have bg := g_bd hφ ε S
  have bgi := ginv_bd (φ := φ) h0 hε S
  have hgi : Continuous (fun x => (ε + m0 φ s x)⁻¹) :=
    ((continuous_const.add (m0_cont hφ s))).inv₀ fun x => (g_pos h0 hε s x).ne'
  set N : ℝ → ℝ → ℝ := fun s x => (((m3 φ s x - x * m2 φ s x - m1 φ s x) * m1 φ s x +
    m1 φ s x * (m3 φ s x - x * m2 φ s x - m1 φ s x)) * (ε + m0 φ s x)) -
    (m1 φ s x * m1 φ s x) * (m2 φ s x - x * m1 φ s x) with hN
  set H' : ℝ → ℝ → ℝ := fun s x => N s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹) with hH'
  have hd : ∀ x, ∀ s' ∈ S, HasDerivAt (fun s => m1 φ s x * m1 φ s x / (ε + m0 φ s x))
      (H' s' x) s' := by
    intro x s' hs'
    have hne : ε + m0 φ s' x ≠ 0 := (g_pos h0 hε s' x).ne'
    have hm := hasDerivAt_m1_s hφ hs' x
    have hg := (hasDerivAt_m0_s hφ hs' x).const_add ε
    have := (hm.mul hm).div hg hne
    refine this.congr_deriv ?_
    simp only [hH', hN, Pi.mul_apply]
    field_simp
  have hc' : Continuous (H' s) := by
    simp only [hH', hN]
    have := m1_cont hφ s; have := m2_cont hφ s; have := m3_cont hφ s; have := m0_cont hφ s
    fun_prop
  have hms : Lin S (fun s x => m3 φ s x - x * m2 φ s x - m1 φ s x) :=
    ((Lin.of_bd b3).sub b2.xmul).sub (Lin.of_bd b1)
  have hNlin : Lin S N := by
    simp only [hN]
    exact Lin.sub (Lin.mul_bd (Lin.add (Lin.mul_bd hms b1) (Lin.bd_mul b1 hms)) bg)
      (Lin.bd_mul (b1.mul b1) (Lin.sub (Lin.of_bd b2) b1.xmul))
  have hH'lin : Lin S H' := by
    simp only [hH']
    exact Lin.mul_bd hNlin (bgi.mul bgi)
  have hKb : Bd S (Kj φ ε) := by
    have h1 := F1_bd hφ h0 hε hS0
    have h2 := F2_bd hφ h0 hε hS0
    unfold Kj
    simp only [sq]
    exact bg.mul ((h2.mul h2).add (h1.mul h1))
  have hKc : Continuous (Kj φ ε s) := by
    unfold Kj
    exact (continuous_const.add (m0_cont hφ s)).mul (((F2_cont hφ h0 hε s).pow 2).add
      ((F1_cont hφ h0 hε s).pow 2))
  have hKi : Integrable (Kj φ ε s) γ := integrable_of_bd hKc (hKb.at hs)
  have hint0 : Continuous (fun x => m1 φ s x * m1 φ s x / (ε + m0 φ s x)) :=
    ((m1_cont hφ s).mul (m1_cont hφ s)).div (continuous_const.add (m0_cont hφ s))
      fun x => (g_pos h0 hε s x).ne'
  obtain ⟨hi', hd'⟩ := hasDerivAt_integral_γ (H := fun s x => m1 φ s x * m1 φ s x /
    (ε + m0 φ s x)) hS (fun s' _ => ((m1_cont hφ s').mul (m1_cont hφ s')).div
      (continuous_const.add (m0_cont hφ s')) fun x => (g_pos h0 hε s' x).ne')
    (by
      obtain ⟨C, hC⟩ := ((b1.mul b1).mul bgi).at hs
      exact ⟨|C|, fun x => by
        have := hC x
        simp only [div_eq_mul_inv]
        calc _ ≤ C := this
          _ ≤ |C| * 1 := by simpa using le_abs_self C
          _ ≤ |C| * (1 + |x|) := by
              apply mul_le_mul_of_nonneg_left _ (abs_nonneg _); linarith [abs_nonneg x]⟩)
    hc' hd hH'lin
  refine ⟨hKi, ?_⟩
  refine (show HasDerivAt (eI φ ε) _ s from hd'.congr_deriv ?_)
  -- two Gaussian integrations by parts
  set G₁ : ℝ → ℝ := fun x => m1 φ s x * (m1 φ s x * m1 φ s x) *
    ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹) with hG₁
  set G₁' : ℝ → ℝ := fun x => (m2 φ s x * (m1 φ s x * m1 φ s x) +
      m1 φ s x * (m2 φ s x * m1 φ s x + m1 φ s x * m2 φ s x)) *
        ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹) +
      (m1 φ s x * (m1 φ s x * m1 φ s x)) *
        ((-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹)) * (ε + m0 φ s x)⁻¹ +
          (ε + m0 φ s x)⁻¹ * (-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹))) with hG₁'
  have hd1 : ∀ x, HasDerivAt G₁ (G₁' x) x := fun x =>
    ((d1x hφ s x).mul ((d1x hφ s x).mul (d1x hφ s x))).mul
      ((hasDerivAt_ginv hφ h0 hε s x).mul (hasDerivAt_ginv hφ h0 hε s x))
  set G₂ : ℝ → ℝ := fun x => m1 φ s x * m2 φ s x * (ε + m0 φ s x)⁻¹ - G₁ x with hG₂
  set G₂' : ℝ → ℝ := fun x => ((m2 φ s x * m2 φ s x + m1 φ s x * m3 φ s x) *
      (ε + m0 φ s x)⁻¹ + (m1 φ s x * m2 φ s x) *
        (-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹))) - G₁' x with hG₂'
  have hd2 : ∀ x, HasDerivAt G₂ (G₂' x) x := fun x =>
    (((d1x hφ s x).mul (d2x hφ s x)).mul (hasDerivAt_ginv hφ h0 hε s x)).sub (hd1 x)
  have bG₁ : Bd S (fun s x => m1 φ s x * (m1 φ s x * m1 φ s x) *
      ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹)) := (b1.mul (b1.mul b1)).mul (bgi.mul bgi)
  have bG₁' : Bd S (fun s x => (m2 φ s x * (m1 φ s x * m1 φ s x) +
      m1 φ s x * (m2 φ s x * m1 φ s x + m1 φ s x * m2 φ s x)) *
        ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹) +
      (m1 φ s x * (m1 φ s x * m1 φ s x)) *
        ((-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹)) * (ε + m0 φ s x)⁻¹ +
          (ε + m0 φ s x)⁻¹ * (-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹)))) :=
    (((b2.mul (b1.mul b1)).add (b1.mul ((b2.mul b1).add (b1.mul b2)))).mul (bgi.mul bgi)).add
      ((b1.mul (b1.mul b1)).mul (((b1.neg.mul (bgi.mul bgi)).mul bgi).add
        (bgi.mul (b1.neg.mul (bgi.mul bgi)))))
  have bG₂ : Bd S (fun s x => m1 φ s x * m2 φ s x * (ε + m0 φ s x)⁻¹ -
      m1 φ s x * (m1 φ s x * m1 φ s x) * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹)) :=
    ((b1.mul b2).mul bgi).sub bG₁
  have bG₂' : Bd S (fun s x => ((m2 φ s x * m2 φ s x + m1 φ s x * m3 φ s x) *
      (ε + m0 φ s x)⁻¹ + (m1 φ s x * m2 φ s x) *
        (-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹))) -
      ((m2 φ s x * (m1 φ s x * m1 φ s x) +
      m1 φ s x * (m2 φ s x * m1 φ s x + m1 φ s x * m2 φ s x)) *
        ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹) +
      (m1 φ s x * (m1 φ s x * m1 φ s x)) *
        ((-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹)) * (ε + m0 φ s x)⁻¹ +
          (ε + m0 φ s x)⁻¹ * (-m1 φ s x * ((ε + m0 φ s x)⁻¹ * (ε + m0 φ s x)⁻¹))))) :=
    ((((b2.mul b2).add (b1.mul b3)).mul bgi).add ((b1.mul b2).mul (b1.neg.mul (bgi.mul bgi)))).sub bG₁'
  obtain ⟨i1, z1⟩ := ibpγ hd1 (bG₁.at hs) (bG₁'.at hs)
  obtain ⟨i2, z2⟩ := ibpγ hd2 (bG₂.at hs) (bG₂'.at hs)
  have e : H' s = fun x => ((G₁' x - x * G₁ x) + 2 * (G₂' x - x * G₂ x)) - 2 * Kj φ ε s x := by
    funext x
    have hne : ε + m0 φ s x ≠ 0 := (g_pos h0 hε s x).ne'
    simp only [hH', hN, hG₁, hG₁', hG₂, hG₂', Kj, F1, F2]
    field_simp
    ring
  have i2' : Integrable (fun x => 2 * (G₂' x - x * G₂ x)) γ := i2.const_mul 2
  have h12 : Integrable (fun x => (G₁' x - x * G₁ x) + 2 * (G₂' x - x * G₂ x)) γ := i1.add i2'
  have h3 : Integrable (fun x => 2 * Kj φ ε s x) γ := hKi.const_mul 2
  rw [e, integral_sub h12 h3, integral_add i1 i2', integral_const_mul, integral_const_mul, z1, z2]
  simp [eJ]

end I2

end MarkovTriple.BGL.Instances.OU
