import Mathlib
import MarkovTriple.BGL.Analysis.Hilbert.Generator

/-!
# Spectral gap `⇔` exponential decay of the semigroup

Let `S : FormData H`, `E` its Friedrichs form on `Q`, `R` its Friedrichs resolvent and
`P_t = S.semigroup t`.  The fixed space `N = {n | R n = n}` equals `ker G` (the kernel of the
generator).  For `λ ≥ 0` the following are equivalent:

* `HasSpectralGap S λ`: `λ ‖u‖² ≤ E(u,u)` for `u ∈ Q` orthogonal to `N`;
* `HasExpDecay S λ`: `‖P_t u‖ ≤ e^{-λ t} ‖u‖` for `u ⟂ N` and `t ≥ 0`.

(`FormData.hasSpectralGap_iff_hasExpDecay`.)  Both directions go through the resolvents
`R_μ` and the implicit Euler scheme `((n+1)/t · R_{(n+1)/t})^{n+1} → P_t` (no differentiation of
the semigroup in `t` is needed).
-/

open Filter Topology Set
open scoped NNReal InnerProductSpace

set_option linter.unusedSectionVars false

namespace MarkovTriple.Hilbert

open Cx

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {R : H →L[ℝ] H}

namespace Cx

/-- Operator inequality `1 - B^k ≤ k (1 - B)` for `B = g(R)`, `0 ≤ g ≤ 1`. -/
lemma UnitOp.inner_one_sub_pow_le (hR : UnitOp R) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc 0 1)) (h0 : ∀ x ∈ Icc (0 : ℝ) 1, 0 ≤ g x)
    (_h1 : ∀ x ∈ Icc (0 : ℝ) 1, g x ≤ 1) (k : ℕ) (u : H) :
    inner ℝ (u - (rcfc g R ^ k) u) u ≤ k * inner ℝ (u - rcfc g R u) u := by
  have hc1 : ContinuousOn (fun x => (1 : ℝ) - g x) (Icc 0 1) := continuousOn_const.sub hg
  have hc2 : ContinuousOn (fun x => (1 : ℝ) - g x ^ k) (Icc 0 1) :=
    continuousOn_const.sub (hg.pow k)
  have hnn := hR.rcfc_inner_nonneg (f := fun x => (k : ℝ) * (1 - g x) - (1 - g x ^ k))
    (fun x hx => by
      have hb := one_add_mul_le_pow (a := g x - 1) (by linarith [h0 x hx]) k
      have : (1 + (g x - 1)) = g x := by ring
      rw [this] at hb
      nlinarith [hb]) u
  have e1 : rcfc (fun x => (1 : ℝ) - g x) R = 1 - rcfc g R := by
    rw [hR.rcfc_sub continuousOn_const hg, hR.rcfc_one]
  have e2 : rcfc (fun x => (1 : ℝ) - g x ^ k) R = 1 - rcfc g R ^ k := by
    rw [hR.rcfc_sub (f := fun _ => (1 : ℝ)) (g := fun x => g x ^ k) continuousOn_const (hg.pow k),
      hR.rcfc_one, hR.rcfc_pow hg]
  rw [hR.rcfc_sub (hc1.const_smul (k : ℝ) |>.congr (fun x _ => by simp)) hc2, hR.rcfc_smul _ hc1,
    e1, e2] at hnn
  simp only [sub_apply, smul_apply,
    one_apply_eq_self, inner_sub_left, inner_smul_left, RCLike.conj_to_real] at hnn ⊢
  linarith

end Cx

end Abstract

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- `u` is orthogonal to the fixed space `N = {n | R n = n} = ker G`. -/
def OrthFixed (u : H) : Prop := ∀ n, S.R n = n → inner ℝ u n = 0

/-- **Spectral gap** `λ`: `λ ‖u‖² ≤ E(u,u)` for `u ∈ Q` orthogonal to `ker G`. -/
def HasSpectralGap (lam : ℝ) : Prop :=
  ∀ u : S.Q, S.OrthFixed (u : H) → lam * ‖(u : H)‖ ^ 2 ≤ S.E u u

/-- **`L²` exponential decay** at rate `λ` on `(ker G)^⊥`. -/
def HasExpDecay (lam : ℝ) : Prop :=
  ∀ u : H, S.OrthFixed u → ∀ t : ℝ≥0, ‖S.semigroup t u‖ ≤ Real.exp (-lam * t) * ‖u‖

lemma resolvent_fixed {n : H} (hn : S.R n = n) {mu : ℝ} (hmu : 0 < mu) :
    S.resolvent mu n = mu⁻¹ • n := by
  have h := resolventLam_apply_eigen S.R_unitOp hmu (a := 1) one_pos le_rfl (u := n)
    (by rw [one_smul]; exact hn)
  have e : (1 : ℝ) / (1 + (mu - 1) * 1) = mu⁻¹ := by
    rw [one_div]; congr 1; ring
  rw [e] at h
  exact h

lemma OrthFixed.resolvent {u : H} (hu : S.OrthFixed u) {mu : ℝ} (hmu : 0 < mu) :
    S.OrthFixed (S.resolvent mu u) := by
  intro n hn
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (S.resolvent_isSelfAdjoint mu)
  have := hs u n
  change inner ℝ (S.resolvent mu u) n = inner ℝ u (S.resolvent mu n) at this
  rw [this, S.resolvent_fixed hn hmu, inner_smul_right, hu n hn, mul_zero]

/-- The Euler step contracts at rate `μ/(λ+μ)` on `(ker G)^⊥` under a gap. -/
lemma norm_resolvent_orth_le {lam : ℝ} (_hlam : 0 ≤ lam) (hgap : S.HasSpectralGap lam)
    {mu : ℝ} (hmu : 0 < mu) {u : H} (hu : S.OrthFixed u) :
    (lam + mu) * ‖S.resolvent mu u‖ ≤ ‖u‖ := by
  set w := S.resolvent mu u with hw
  have hwQ : w ∈ S.Q := S.resolvent_mem_Q hmu u
  have hweak := S.E_resolvent hmu u ⟨w, hwQ⟩
  have hgapw := hgap ⟨w, hwQ⟩ (hu.resolvent S hmu)
  simp only at hweak hgapw
  rw [real_inner_self_eq_norm_sq] at hweak
  have hcs : inner ℝ u w ≤ ‖u‖ * ‖w‖ := real_inner_le_norm u w
  by_cases hw0 : ‖w‖ = 0
  · rw [hw0, mul_zero]; exact norm_nonneg _
  have hwp : 0 < ‖w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hw0)
  have : (lam + mu) * ‖w‖ ^ 2 ≤ ‖u‖ * ‖w‖ := by nlinarith
  nlinarith

/-- **Spectral gap ⟹ exponential decay.** -/
theorem hasExpDecay_of_hasSpectralGap {lam : ℝ} (hlam : 0 ≤ lam) (hgap : S.HasSpectralGap lam) :
    S.HasExpDecay lam := by
  intro u hu t
  by_cases ht : t = 0
  · subst ht; simp [S.semigroup_zero]
  have htp : (0 : ℝ) < t := by positivity
  -- one Euler step contracts
  have key : ∀ n : ℕ, ‖eulerOp S.R (t : ℝ) n u‖ ≤
      ((1 + lam * t / ((n : ℝ) + 1)) ^ (n + 1))⁻¹ * ‖u‖ := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hmu : (0 : ℝ) < ((n : ℝ) + 1) / t := by positivity
    set mu : ℝ := ((n : ℝ) + 1) / t with hmudef
    set q : ℝ := (1 + lam * t / ((n : ℝ) + 1))⁻¹ with hq
    have hqpos : 0 < q := by positivity
    have hstep : ∀ v : H, S.OrthFixed v → S.OrthFixed ((mu • S.resolvent mu) v) ∧
        ‖(mu • S.resolvent mu) v‖ ≤ q * ‖v‖ := by
      intro v hv
      refine ⟨?_, ?_⟩
      · have := hv.resolvent S hmu
        intro m hm
        simp only [smul_apply, inner_smul_left, RCLike.conj_to_real]
        rw [this m hm, mul_zero]
      · have h1 := S.norm_resolvent_orth_le hlam hgap hmu hv
        simp only [smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos hmu]
        have hq' : mu / (lam + mu) = q := by
          rw [hq, hmudef]
          have h2 : (lam + ((n : ℝ) + 1) / t) ≠ 0 := by positivity
          have h3 : (1 + lam * t / ((n : ℝ) + 1)) ≠ 0 := by positivity
          field_simp
          ring
        have hlm : 0 < lam + mu := by positivity
        have : mu * ‖S.resolvent mu v‖ ≤ mu / (lam + mu) * ‖v‖ := by
          calc mu * ‖S.resolvent mu v‖ = (mu / (lam + mu)) * ((lam + mu) * ‖S.resolvent mu v‖) := by
                field_simp
            _ ≤ (mu / (lam + mu)) * ‖v‖ := mul_le_mul_of_nonneg_left h1 (by positivity)
        rw [hq'] at this
        exact this
    have hpow : ∀ k : ℕ, S.OrthFixed (((mu • S.resolvent mu) ^ k) u) ∧
        ‖((mu • S.resolvent mu) ^ k) u‖ ≤ q ^ k * ‖u‖ := by
      intro k
      induction k with
      | zero => simpa using hu
      | succ k ih =>
        obtain ⟨h1, h2⟩ := ih
        obtain ⟨h3, h4⟩ := hstep _ h1
        refine ⟨?_, ?_⟩
        · rw [pow_succ', mul_apply_eq_comp]; exact h3
        · rw [pow_succ', mul_apply_eq_comp]
          calc _ ≤ q * ‖((mu • S.resolvent mu) ^ k) u‖ := h4
            _ ≤ q * (q ^ k * ‖u‖) := mul_le_mul_of_nonneg_left h2 hqpos.le
            _ = q ^ (k + 1) * ‖u‖ := by ring
    have := (hpow (n + 1)).2
    unfold eulerOp
    rw [hq, inv_pow] at this
    exact this
  -- pass to the limit
  have hlim1 : Tendsto (fun n : ℕ => ‖eulerOp S.R (t : ℝ) n u‖) atTop (𝓝 ‖S.semigroup t u‖) :=
    (((ContinuousLinearMap.apply ℝ H u).continuous.tendsto _).comp
      (tendsto_eulerOp S.R_unitOp t ht)).norm
  have hlim2 : Tendsto (fun n : ℕ => ((1 + lam * t / ((n : ℝ) + 1)) ^ (n + 1))⁻¹ * ‖u‖) atTop
      (𝓝 (Real.exp (-lam * t) * ‖u‖)) := by
    have h1 := Real.tendsto_one_add_div_pow_exp (lam * t)
    have h2 : Tendsto (fun n : ℕ => (1 + lam * t / ((n + 1 : ℕ) : ℝ)) ^ (n + 1)) atTop
        (𝓝 (Real.exp (lam * t))) := h1.comp (tendsto_add_atTop_nat 1)
    have h3 := h2.inv₀ (Real.exp_pos _).ne'
    have e : Real.exp (-lam * t) = (Real.exp (lam * t))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [e]
    refine (h3.mul_const ‖u‖).congr (fun n => ?_)
    push_cast
    rfl
  exact le_of_tendsto_of_tendsto hlim1 hlim2 (Eventually.of_forall key)

/-- Algebra of the form: `E(x - c y, x - c y) = E(x,x) - 2c E(x,y) + c² E(y,y)`. -/
lemma E_sub_smul_self (x y : S.Q) (c : ℝ) :
    S.E (x - c • y) (x - c • y) = S.E x x - 2 * c * S.E x y + c ^ 2 * S.E y y := by
  have h1 := real_inner_comm (S.qEquiv.symm x) (S.qEquiv.symm y)
  have h2 := real_inner_comm (x : H) (y : H)
  simp only [FormData.E, FormData.E1, map_sub, map_smul, Submodule.coe_sub, Submodule.coe_smul,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  linear_combination (-c) * h1 + c * h2

/-- **Yosida bound**: `μ ⟪u - μ R_μ u, u⟫ ≤ E(u,u)` for `u ∈ Q`. -/
lemma yosida_le {mu : ℝ} (hmu : 0 < mu) (u : S.Q) :
    mu * inner ℝ ((u : H) - mu • S.resolvent mu u) (u : H) ≤ S.E u u := by
  set w : H := S.resolvent mu u with hw
  have hwQ : w ∈ S.Q := S.resolvent_mem_Q hmu u
  set w' : S.Q := ⟨w, hwQ⟩ with hw'
  set v : H := (u : H) - mu • w with hv
  have hweak : ∀ φ : S.Q, S.E w' φ = inner ℝ v φ := by
    intro φ
    have := S.E_resolvent hmu (u : H) φ
    simp only [hv, inner_sub_left, inner_smul_left, RCLike.conj_to_real]
    change S.E w' φ + mu * inner ℝ w (φ : H) = inner ℝ (u : H) (φ : H) at this
    linarith
  have h1 : S.E w' u = inner ℝ v (u : H) := hweak u
  have h2 : S.E w' w' = inner ℝ v w := hweak w'
  have hnn : 0 ≤ S.E u u - 2 * mu * S.E u w' + mu ^ 2 * S.E w' w' := by
    have := S.E_nonneg (u - mu • w')
    rwa [S.E_sub_smul_self u w' mu] at this
  have hcomm : S.E u w' = S.E w' u := by
    simp only [FormData.E, FormData.E1]; rw [real_inner_comm (S.qEquiv.symm u), real_inner_comm (u : H)]
  rw [hcomm, h1, h2] at hnn
  -- `mu * w = u - v`
  have hmw : mu • w = (u : H) - v := by rw [hv]; abel
  have e : mu ^ 2 * inner ℝ v w = mu * inner ℝ v (u : H) - mu * ‖v‖ ^ 2 := by
    have : mu ^ 2 * inner ℝ v w = mu * inner ℝ v (mu • w) := by
      rw [inner_smul_right]; ring
    rw [this, hmw, inner_sub_right, real_inner_self_eq_norm_sq]; ring
  rw [e] at hnn
  have hvu : inner ℝ v (u : H) = inner ℝ ((u : H) - mu • S.resolvent mu u) (u : H) := rfl
  nlinarith [mul_nonneg hmu.le (sq_nonneg ‖v‖)]

/-- **Exponential decay ⟹ spectral gap.** -/
theorem hasSpectralGap_of_hasExpDecay {lam : ℝ} (hlam : 0 ≤ lam) (hdec : S.HasExpDecay lam) :
    S.HasSpectralGap lam := by
  intro u hu
  set x : H := (u : H) with hx
  -- for each `t > 0`: `⟪x - P_t x, x⟫ ≤ t E(u,u)`
  have hmain : ∀ t : ℝ≥0, t ≠ 0 → inner ℝ (x - S.semigroup t x) x ≤ t * S.E u u := by
    intro t ht
    have htp : (0 : ℝ) < t := by positivity
    have hn : ∀ n : ℕ, inner ℝ (x - eulerOp S.R (t : ℝ) n x) x ≤ t * S.E u u := by
      intro n
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hmu : (0 : ℝ) < ((n : ℝ) + 1) / t := by positivity
      set mu : ℝ := ((n : ℝ) + 1) / t with hmudef
      have hcont : ContinuousOn (fun r => mu * resFun mu r) (Icc 0 1) :=
        continuousOn_const.mul (continuousOn_resFun hmu)
      have hB : rcfc (fun r => mu * resFun mu r) S.R = mu • S.resolvent mu := by
        rw [S.R_unitOp.rcfc_smul mu (continuousOn_resFun hmu)]; rfl
      have hg0 : ∀ r ∈ Icc (0 : ℝ) 1, 0 ≤ mu * resFun mu r := fun r hr =>
        mul_nonneg hmu.le (div_nonneg hr.1 (den_pos hmu hr).le)
      have hg1 : ∀ r ∈ Icc (0 : ℝ) 1, mu * resFun mu r ≤ 1 := fun r hr => by
        have hd := den_pos hmu hr
        rw [resFun, ← mul_div_assoc, div_le_one hd]
        nlinarith [hr.2, hr.1]
      have hop := S.R_unitOp.inner_one_sub_pow_le hcont hg0 hg1 (n + 1) x
      rw [hB] at hop
      have hyo := S.yosida_le hmu u
      have heul : eulerOp S.R (t : ℝ) n = (mu • S.resolvent mu) ^ (n + 1) := rfl
      rw [heul]
      refine hop.trans ?_
      have hk : ((n + 1 : ℕ) : ℝ) = mu * t := by
        rw [hmudef]; push_cast; field_simp
      rw [hk]
      have hsm : inner ℝ (x - (mu • S.resolvent mu) x) x = inner ℝ (x - mu • S.resolvent mu x) x := rfl
      rw [hsm]
      have h2 : mu * inner ℝ (x - mu • S.resolvent mu x) x ≤ S.E u u := hyo
      calc (mu * t) * inner ℝ (x - mu • S.resolvent mu x) x
          = t * (mu * inner ℝ (x - mu • S.resolvent mu x) x) := by ring
        _ ≤ t * S.E u u := mul_le_mul_of_nonneg_left h2 htp.le
    have hlim : Tendsto (fun n : ℕ => inner ℝ (x - eulerOp S.R (t : ℝ) n x) x) atTop
        (𝓝 (inner ℝ (x - S.semigroup t x) x)) := by
      have h1 : Tendsto (fun n : ℕ => eulerOp S.R (t : ℝ) n x) atTop (𝓝 (S.semigroup t x)) :=
        ((ContinuousLinearMap.apply ℝ H x).continuous.tendsto _).comp
          (tendsto_eulerOp S.R_unitOp t ht)
      exact ((tendsto_const_nhds.sub h1).inner tendsto_const_nhds)
    exact le_of_tendsto hlim (Eventually.of_forall hn)
  -- decay bound on `⟪P_t x, x⟫`
  have hdecay : ∀ t : ℝ≥0, inner ℝ (S.semigroup t x) x ≤ Real.exp (-lam * t) * ‖x‖ ^ 2 := by
    intro t
    calc inner ℝ (S.semigroup t x) x ≤ ‖S.semigroup t x‖ * ‖x‖ := real_inner_le_norm _ _
      _ ≤ (Real.exp (-lam * t) * ‖x‖) * ‖x‖ :=
          mul_le_mul_of_nonneg_right (hdec x hu t) (norm_nonneg _)
      _ = Real.exp (-lam * t) * ‖x‖ ^ 2 := by ring
  -- combine: `λ ‖x‖² / (1 + λ t) ≤ E(u,u)` for `t > 0`
  have hfin : ∀ t : ℝ, 0 < t → lam * ‖x‖ ^ 2 / (1 + lam * t) ≤ S.E u u := by
    intro t htp
    set s : ℝ≥0 := ⟨t, htp.le⟩ with hs
    have hst : (s : ℝ) = t := rfl
    have hs0 : s ≠ 0 := fun h => by
      have h' : (s : ℝ) = 0 := by rw [h]; rfl
      linarith
    have h1 := hmain s hs0
    have h2 := hdecay s
    simp only [inner_sub_left, real_inner_self_eq_norm_sq] at h1
    have h3 : Real.exp (-lam * t) ≤ (1 + lam * t)⁻¹ := by
      have : 1 + lam * t ≤ Real.exp (lam * t) := by linarith [Real.add_one_le_exp (lam * t)]
      rw [show Real.exp (-lam * t) = (Real.exp (lam * t))⁻¹ by
        rw [← Real.exp_neg]; congr 1; ring]
      exact inv_anti₀ (by positivity) this
    rw [hst] at h1 h2
    have h4 : ‖x‖ ^ 2 - (1 + lam * t)⁻¹ * ‖x‖ ^ 2 ≤ t * S.E u u := by
      have : Real.exp (-lam * t) * ‖x‖ ^ 2 ≤ (1 + lam * t)⁻¹ * ‖x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
      linarith
    have hpos : 0 < 1 + lam * t := by positivity
    have h5 : ‖x‖ ^ 2 - (1 + lam * t)⁻¹ * ‖x‖ ^ 2 = t * (lam * ‖x‖ ^ 2 / (1 + lam * t)) := by
      field_simp; ring
    rw [h5] at h4
    exact le_of_mul_le_mul_left h4 htp
  have hcont : Tendsto (fun t : ℝ => lam * ‖x‖ ^ 2 / (1 + lam * t)) (𝓝[>] 0)
      (𝓝 (lam * ‖x‖ ^ 2)) := by
    have : ContinuousAt (fun t : ℝ => lam * ‖x‖ ^ 2 / (1 + lam * t)) 0 := by
      apply ContinuousAt.div continuousAt_const (by fun_prop)
      simp
    have h := this.tendsto
    simp only [mul_zero, add_zero, div_one] at h
    exact h.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hcont (by
    filter_upwards [self_mem_nhdsWithin] with t ht using hfin t ht)

/-- **Spectral gap `⇔` exponential decay in `L²`.** -/
theorem hasSpectralGap_iff_hasExpDecay {lam : ℝ} (hlam : 0 ≤ lam) :
    S.HasSpectralGap lam ↔ S.HasExpDecay lam :=
  ⟨S.hasExpDecay_of_hasSpectralGap hlam, S.hasSpectralGap_of_hasExpDecay hlam⟩

end FormData

end MarkovTriple.Hilbert
