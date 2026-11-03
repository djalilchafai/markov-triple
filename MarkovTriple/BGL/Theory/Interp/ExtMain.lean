import Mathlib
import MarkovTriple.BGL.Theory.Interp.ExtChain
import MarkovTriple.BGL.Theory.LogSobolevDim
import MarkovTriple.BGL.Theory.Interp.EntropyApplications

/-!
# BGL (5.7.11)-(5.7.12) for bounded `g ∈ 𝒜`, the field `ext` of `FiniteDimInterpolation`, and the unconditional
finite-`n` logarithmic Sobolev inequality (BGL Thm 5.7.4, p. 270-272)

Statements: `Theory/Interp/STATEMENTS_R16_Ext.md` (E5-E7).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E} [IsFiniteMeasure T.μ] {g : E → ℝ} {ρ : ℝ} {n : ℝ≥0∞}

/-- **BGL (5.7.10)-(5.7.11)** for bounded `g ∈ 𝒜` (E5). -/
theorem integral_exp_Γ₂_ge_bdd (hCD : T.CD ρ n) (hn1 : 1 < n) (hn : n ≠ ⊤) (hb : Bdd T g) :
    ρ * (n.toReal / (n.toReal - 1)) * ∫ x, Real.exp (g x) * G T g g x ∂T.μ +
      (4 * n.toReal - 1) / (4 * (n.toReal + 2) ^ 2) *
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ ≤
      ∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ := by
  have hgA := hb.memA
  have hm1 : 1 < n.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hn).2 hn1
    simpa using this
  have hn' : (n⁻¹).toReal = (n.toReal)⁻¹ := ENNReal.toReal_inv n
  generalize hm : n.toReal = m at hm1 hn' ⊢
  have hMc := M_comb' hCD hb
  have hibp := (integral_exp_L_Γ_bdd hCD hb).2
  have hW := integral_exp_sq_L_bdd hCD hb
  have hmpos : 0 < m := by linarith
  -- the parameter a
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 3 / (2 * (m + 2)) := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha_def]; positivity
  have ha : a * (m + 2) = 3 / 2 := by rw [ha_def]; field_simp
  -- pointwise curvature inequality for e^{ag}
  have hfA : Pw g 1 a ∈ T.A := Pw_mem hgA 1 a
  have q0 := hCD.2 _ hfA
  have q1 := ΓA_comp_comp T (contDiff_kexp 1 a) hgA
  have q2 := L_Pw hgA 1 a
  have q3 := Γ₂_Pw hgA a
  have hpt : ∀ᵐ x ∂T.μ, Real.exp (g x) * (0 * T.toDiffusionTriple.Γ₂ g g x +
        0 * G T g (G T g g) x + a ^ 2 * (G T g g x) ^ 2 + 1 * (T.L g x) ^ 2 +
        (2 * a) * (T.L g x * G T g g x) + (m * ρ) * G T g g x) ≤
      Real.exp (g x) * (m * T.toDiffusionTriple.Γ₂ g g x +
        (m * a) * G T g (G T g g) x + (m * a ^ 2) * (G T g g x) ^ 2 + 0 * (T.L g x) ^ 2 +
        0 * (T.L g x * G T g g x) + 0 * G T g g x) := by
    filter_upwards [q0, q1, q2, q3] with x h0 h1 h2 h3
    have h1' : G T (Pw g 1 a) (Pw g 1 a) x = (1 * a * Real.exp (a * g x)) ^ 2 * G T g g x := by
      have := h1
      simp only [deriv_kexp] at this
      exact this
    have hΓ : T.toDiffusionTriple.ΓA (Pw g 1 a) (Pw g 1 a) x =
        (1 * a * Real.exp (a * g x)) ^ 2 * G T g g x := h1'
    rw [hΓ, hn', h2, h3] at h0
    have hex : Real.exp (2 * a * g x) = Real.exp (a * g x) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hex] at h0
    have hK : 0 < a ^ 2 * Real.exp (a * g x) ^ 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_left h0 hmpos.le
    have h5 : m * (ρ * ((1 * a * Real.exp (a * g x)) ^ 2 * G T g g x) + m⁻¹ *
        (1 * a * Real.exp (a * g x) * T.L g x +
          1 * a * a * Real.exp (a * g x) * T.toDiffusionTriple.ΓA g g x) ^ 2) =
        a ^ 2 * Real.exp (a * g x) ^ 2 * (m * ρ * G T g g x +
          (T.L g x + a * G T g g x) ^ 2) := by
      have : m * m⁻¹ = 1 := mul_inv_cancel₀ hmpos.ne'
      calc _ = m * ρ * ((1 * a * Real.exp (a * g x)) ^ 2 * G T g g x) +
            (m * m⁻¹) * (1 * a * Real.exp (a * g x) * T.L g x +
          1 * a * a * Real.exp (a * g x) * G T g g x) ^ 2 := by
              show m * (ρ * _ + m⁻¹ * (_ + _ * G T g g x) ^ 2) = _; ring
        _ = _ := by rw [this]; ring
    have h6 : m * (a ^ 2 * Real.exp (a * g x) ^ 2 * (T.toDiffusionTriple.Γ₂ g g x +
        a * G T g (G T g g) x + a ^ 2 * (G T g g x) ^ 2)) =
        a ^ 2 * Real.exp (a * g x) ^ 2 * (m * T.toDiffusionTriple.Γ₂ g g x +
        (m * a) * G T g (G T g g) x + (m * a ^ 2) * (G T g g x) ^ 2) := by ring
    rw [h5, h6] at h4
    have h7 : m * ρ * G T g g x + (T.L g x + a * G T g g x) ^ 2 ≤
        m * T.toDiffusionTriple.Γ₂ g g x + (m * a) * G T g (G T g g) x +
          (m * a ^ 2) * (G T g g x) ^ 2 := le_of_mul_le_mul_left h4 hK
    have h8 := mul_le_mul_of_nonneg_left h7 (Real.exp_pos (g x)).le
    refine le_trans (le_of_eq ?_) (le_trans h8 (le_of_eq ?_)) <;> ring
  have hint := integral_mono_ae (int_comb' hCD hb 0 0 (a ^ 2) 1 (2 * a) (m * ρ))
    (int_comb' hCD hb m (m * a) (m * a ^ 2) 0 0 0) hpt
  rw [hMc, hMc] at hint
  -- algebra
  have t1 : (3 / 2 - (m + 2) * a) * (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) = 0 := by
    rw [show 3 / 2 - (m + 2) * a = 0 by linarith, zero_mul]
  have t2 : a * (∫ x, Real.exp (g x) * (T.L g x * G T g g x) ∂T.μ) =
      a * (-(∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) -
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ) := by rw [hibp]
  have key : (m - 1) * (∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) ≥
      m * ρ * (∫ x, Real.exp (g x) * G T g g x ∂T.μ) +
        ((1 - a) ^ 2 - m * a ^ 2) * ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
    nlinarith [hint, t1, t2, hW, hibp]
  have hm1pos : 0 < m - 1 := by linarith
  have hZc : (4 * m - 1) / (4 * (m + 2) ^ 2) * (m - 1) = (1 - a) ^ 2 - m * a ^ 2 := by
    rw [ha_def]; field_simp; ring
  rw [← mul_le_mul_iff_right₀ hm1pos]
  have e : (m - 1) * (ρ * (m / (m - 1)) * (∫ x, Real.exp (g x) * G T g g x ∂T.μ) +
      (4 * m - 1) / (4 * (m + 2) ^ 2) * ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ) =
      m * ρ * (∫ x, Real.exp (g x) * G T g g x ∂T.μ) +
        ((4 * m - 1) / (4 * (m + 2) ^ 2) * (m - 1)) *
          ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
    field_simp
  rw [e, hZc]
  linarith [key]

/-- **BGL (5.7.12)** (p. 272) for bounded `g ∈ 𝒜`: `ρ n/(n-1) ∫ e^g Γ(g) ≤ ∫ e^g Γ₂(g)`. -/
theorem integral_exp_Γ₂_ge_bdd' (hCD : T.CD ρ n) (hn1 : 1 < n) (hn : n ≠ ⊤) (hb : Bdd T g) :
    ρ * (n.toReal / (n.toReal - 1)) * ∫ x, Real.exp (g x) * G T g g x ∂T.μ ≤
      ∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ := by
  have h := integral_exp_Γ₂_ge_bdd hCD hn1 hn hb
  have hm1 : 1 < n.toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hn).2 hn1
    simpa using this
  have hZ : 0 ≤ (4 * n.toReal - 1) / (4 * (n.toReal + 2) ^ 2) *
      ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
    refine mul_nonneg (div_nonneg (by linarith) (by positivity)) ?_
    exact integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  linarith

/-- **The field `ext` of `FiniteDimInterpolation`** (E6; BGL p. 272: (5.7.12) extends to bounded `f ∈ 𝒜` with
`Γ(f)`, `Lf` bounded), for every finite-measure `FullTriple` with `CD(ρ,n)`, `1 < n < ∞`.  The two integrability
hypotheses of the frozen field are not used. -/
theorem finiteDimExt (hCD : T.CD ρ n) (hn1 : 1 < n) (hn : n ≠ ⊤) :
    ∀ (ε M : ℝ), 0 < ε → 0 < M → ∀ f ∈ T.A, (∀ᵐ x ∂T.μ, f x ∈ Icc ε (ε + M)) →
    ∀ B : ℝ, (∀ᵐ x ∂T.μ, T.toDiffusionTriple.ΓA f f x ≤ B) → (∀ᵐ x ∂T.μ, |T.L f x| ≤ B) →
    ∀ C : BE.Cut ε M,
    Integrable (fun x => f x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x) T.μ →
    Integrable (fun x => f x * T.toDiffusionTriple.ΓA (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x) T.μ →
    (ρ * (n.toReal / (n.toReal - 1))) *
        ∫ x, f x * T.toDiffusionTriple.ΓA (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x ∂T.μ ≤
      ∫ x, f x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x ∂T.μ := by
  intro ε M hε hM f hf hrange B hΓ hL Cut _ _
  have hbf : Bdd T f := by
    refine ⟨hf, ε + M, B, ?_, hΓ, hL⟩
    filter_upwards [hrange] with x hx
    exact abs_le.2 ⟨by linarith [hx.1], hx.2⟩
  have hb : Bdd T (fun y => Cut.Λ (f y)) := Bdd.comp Cut.hΛ hbf
  have h := integral_exp_Γ₂_ge_bdd' hCD hn1 hn hb
  have hexp : ∀ᵐ x ∂T.μ, Real.exp (Cut.Λ (f x)) = f x := by
    filter_upwards [hrange] with x hx
    rw [Cut.Λ_eq hx]
    exact Real.exp_log (lt_of_lt_of_le hε hx.1)
  have e1 : ∫ x, Real.exp (Cut.Λ (f x)) * G T (fun y => Cut.Λ (f y)) (fun y => Cut.Λ (f y)) x ∂T.μ =
      ∫ x, f x * T.toDiffusionTriple.ΓA (fun y => Cut.Λ (f y)) (fun y => Cut.Λ (f y)) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [hexp] with x hx
    rw [hx]
  have e2 : ∫ x, Real.exp (Cut.Λ (f x)) * T.toDiffusionTriple.Γ₂ (fun y => Cut.Λ (f y))
      (fun y => Cut.Λ (f y)) x ∂T.μ =
      ∫ x, f x * T.toDiffusionTriple.Γ₂ (fun y => Cut.Λ (f y)) (fun y => Cut.Λ (f y)) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [hexp] with x hx
    rw [hx]
  rw [e2, e1] at h
  exact h

/-- **`FiniteDimInterpolation T (ρ n/(n-1))` for every finite-measure `FullTriple`** with `CD(ρ,n)`,
`ρ ≥ 0`, `1 < n < ∞`. -/
theorem finiteDimInterpolation_of_CD (hCD : T.CD ρ n) (hρ : 0 ≤ ρ) (hn1 : 1 < n) (hn : n ≠ ⊤) :
    T.FiniteDimInterpolation (ρ * (n.toReal / (n.toReal - 1))) :=
  finiteDimInterpolation_of_ext T hCD hρ (finiteDimExt hCD hn1 hn)

/-- **BGL Thm 5.7.4, unconditional** for every `FullTriple` with probability measure (no compactness):
`CD(ρ,n)`, `ρ > 0`, `1 < n < ∞` ⇒ `LS((n-1)/(ρ n), 0)`. -/
theorem logSobolev_dim_unconditional [IsProbabilityMeasure T.μ] (hρ : 0 < ρ) (hn1 : 1 < n)
    (hn : n ≠ ⊤) (hCD : T.CD ρ n) : T.toDiffusionTriple.LS (dimLSConst ρ n) 0 :=
  logSobolev_dim_of_ext T hρ hn1 hn hCD (finiteDimExt hCD hn1 hn)

end FullTriple

end MarkovTriple.BGL
