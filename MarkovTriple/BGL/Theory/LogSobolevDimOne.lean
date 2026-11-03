import Mathlib
import MarkovTriple.BGL.Theory.LogSobolevDim
import MarkovTriple.BGL.Theory.LogSobolevDimChain
import MarkovTriple.BGL.Theory.Convergence
import MarkovTriple.BGL.Theory.LSToPI

/-!
# Logarithmic Sobolev inequality in the case `n = 1` (BGL p. 272-273, after Thm 5.7.4)

Source: Bakry-Gentil-Ledoux, p. 272-273, the paragraph following the proof of Thm 5.7.4:
"The case `n = 1` corresponding to the one-dimensional torus, for which `ρ = 0`, may easily be integrated into the picture.
Indeed, by Proposition 4.5.5, p. 199, the Poincaré inequality `P(1)` holds in this case, and by the dual formulation of
Proposition 4.8.3, p. 214, for every `f` in `𝒟(L)`, `∫ Γ₂(f) dμ ≥ ∫ Γ(f) dμ`.  This inequality applied to `f = e^{g/2}`
(for `g ∈ 𝒜₀`) yields by (5.7.6) that `∫ e^g [Γ₂(g) + ½ Γ(g,Γ(g)) + ¼ Γ(g)²] dμ ≥ ∫ e^g Γ(g) dμ` (5.7.13).
Now, under `CD(0,1)`, (5.7.9) with `a = 1/3` shows `∫ e^g Γ₂(g) ≥ ∫ e^g [(Lg)² - Γ(g,Γ(g)) - ⅔ Γ(g)²]`.  Comparing with (5.7.8)
with `a = 1/2` indicates `∫ e^g Γ(g,Γ(g)) + ⅔ ∫ e^g Γ(g)² ≤ 0`.  Therefore, by (5.7.13), `∫ e^g Γ₂(g) ≥ ∫ e^g Γ(g)`, that is (5.7.12)
with the convention `ρn/(n-1) = 1`.  The logarithmic Sobolev inequality with constant 1 (equal to the Poincaré constant) follows
similarly.  [...]  The constant is optimal since it is already optimal for the Poincaré inequality."

Formalization (scale-free: Poincaré constant `c > 0`; the book's torus has `c = 1`):
* `FullTriple.integral_Γ_le_of_PI`: the dual form of Prop. 4.8.3 on `𝒜₀`: `P(c) ⟹ ∫ Γ(f) ≤ c ∫ Γ₂(f)`;
* `FullTriple.integral_exp_Γ₂_ge_one`: the displayed chain above, (5.7.13) and its consequence: `(1/c) ∫ e^g Γ(g) ≤ ∫ e^g Γ₂(g)`;
* `tendsto_entE_of_PI`, `ent_le_fisher_of_PI`, `logSobolev_of_PI_finiteDim`: the argument of Prop. 5.7.1 / Thm 5.7.4 with the
  Poincaré inequality as the input for the limit `e(s) → m log m` (the case `ρ = 0` has no `CD(ρ,·)`, `ρ > 0`);
* `CompactTriple.finiteDimInterpolation_one`, `compact_logSobolev_one`: `CD(0,1)` and `P(c)` on a compact triple give `LS(c)`.

The constant is "optimal" in the book's sense: `LS(c) ⟹ P(c)` (`DiffusionTriple.PI_of_LS`, `Theory/LSToPI.lean`), so `LS(c) ⟺ P(c)`
(`compact_LS_iff_PI_of_CD_zero_one`).  No "constant" `dimLSConst ρ 1` is defined (`(1 - n⁻¹)/ρ = 0/0` at `n = 1`, `ρ = 0`).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

section DualPoincare

/-- **Dual form of the Poincaré inequality** (BGL Prop. 4.8.3, p. 214, restricted to `f ∈ 𝒜₀`):
`P(c) ⟹ ∫ Γ(f) dμ ≤ c ∫ Γ₂(f) dμ` (`∫Γ₂(f) = ∫(Lf)²`, (3.3.8), `ℰ(f) = -∫ f Lf = -∫ (f - m) Lf`, Young, `Var f ≤ c ℰ(f)`). -/
theorem integral_Γ_le_of_PI {c : ℝ} (hPI : T.toDiffusionTriple.PI c) {f : E → ℝ} (hf : f ∈ T.A₀) :
    ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ ≤ c * ∫ x, T.toDiffusionTriple.Γ₂ f f x ∂T.μ := by
  obtain ⟨hprob, hc, hineq⟩ := hPI
  have := hprob
  have hLf : T.L f ∈ T.A₀ := T.L_mem f hf
  have hfi : Integrable f T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple hf
  have hLi : Integrable (T.L f) T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple hLf
  have hfL : Integrable (fun x => f x * T.L f x) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.A₀.mul_mem hf hLf)
  have hLL : Integrable (fun x => T.L f x * T.L f x) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.A₀.mul_mem hLf hLf)
  have hff : Integrable (fun x => f x * f x) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (T.A₀.mul_mem hf hf)
  set m : ℝ := ∫ x, f x ∂T.μ with hm
  set Eg : ℝ := ∫ x, T.Γ f f x ∂T.μ with hEg
  have hEΓ : ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ = Eg :=
    integral_congr_ae (DiffusionTriple.ΓA_ae_eq T.toDiffusionTriple hf hf)
  rw [hEΓ, integral_Γ₂ T hf]
  have hibp := T.ibp f hf f hf
  have hL0 := T.integral_L f hf
  set Q : ℝ := ∫ x, T.L f x * T.L f x ∂T.μ with hQ
  -- `ℰ = -∫ (f - m) L f`
  have hE1 : Eg = -∫ x, (f x - m) * T.L f x ∂T.μ := by
    have e : ∫ x, (f x - m) * T.L f x ∂T.μ =
        (∫ x, f x * T.L f x ∂T.μ) - m * ∫ x, T.L f x ∂T.μ := by
      have i1 : Integrable (fun x => m * T.L f x) T.μ := hLi.const_mul m
      have e' : (fun x => (f x - m) * T.L f x) = fun x => f x * T.L f x - m * T.L f x := by
        funext x; ring
      rw [e', integral_sub hfL i1, integral_const_mul]
    rw [e, hL0]; linarith
  -- variance
  have hV : ProbabilityTheory.variance f T.μ = ∫ x, (f x - m) ^ 2 ∂T.μ := by
    rw [ProbabilityTheory.variance_eq_sub (T.memLp f hf 2 (by norm_num) (by simp))]
    have e : (fun x => (f x - m) ^ 2) = fun x => f x * f x - 2 * m * f x + m ^ 2 := by
      funext x; ring
    have i1 : Integrable (fun x => 2 * m * f x) T.μ := hfi.const_mul _
    have i12 : Integrable (fun x => f x * f x - 2 * m * f x) T.μ := hff.sub i1
    rw [e, integral_add i12 (integrable_const _), integral_sub hff i1, integral_const_mul]
    simp [Pi.pow_apply, sq]
    rw [← hm]
    ring
  have hPIf := hineq f hf
  have hen : energy T.μ T.Γ f = Eg := rfl
  rw [hen] at hPIf
  -- Young: `-(f-m) L f ≤ (1/(2c)) (f-m)² + (c/2) (L f)²`
  have hpt : ∀ x, -((f x - m) * T.L f x) ≤
      1 / (2 * c) * (f x - m) ^ 2 + c / 2 * (T.L f x * T.L f x) := by
    intro x
    have h2 : 0 ≤ (f x - m + c * T.L f x) ^ 2 := sq_nonneg _
    have : 1 / (2 * c) * (f x - m) ^ 2 + c / 2 * (T.L f x * T.L f x) +
        (f x - m) * T.L f x = 1 / (2 * c) * (f x - m + c * T.L f x) ^ 2 := by
      field_simp; ring
    have h3 : 0 ≤ 1 / (2 * c) * (f x - m + c * T.L f x) ^ 2 := by positivity
    linarith
  have iV : Integrable (fun x => (f x - m) ^ 2) T.μ := by
    have e : (fun x => (f x - m) ^ 2) = fun x => f x * f x - 2 * m * f x + m ^ 2 := by
      funext x; ring
    have i1 : Integrable (fun x => 2 * m * f x) T.μ := hfi.const_mul _
    rw [e]; exact (hff.sub i1).add (integrable_const _)
  have iFL : Integrable (fun x => (f x - m) * T.L f x) T.μ := by
    have e' : (fun x => (f x - m) * T.L f x) = fun x => f x * T.L f x - m * T.L f x := by
      funext x; ring
    rw [e']; exact hfL.sub (hLi.const_mul m)
  have iN : Integrable (fun x => -((f x - m) * T.L f x)) T.μ := iFL.neg
  have iR : Integrable (fun x => 1 / (2 * c) * (f x - m) ^ 2 + c / 2 * (T.L f x * T.L f x)) T.μ :=
    (iV.const_mul (1 / (2 * c))).add (hLL.const_mul (c / 2))
  have hint := integral_mono iN iR hpt
  rw [integral_neg, integral_add (iV.const_mul _) (hLL.const_mul _), integral_const_mul,
    integral_const_mul, ← hV, ← hQ] at hint
  -- `hint : Eg ≤ Var/(2c) + c Q/2`, `Var ≤ c Eg`
  have hVc : 1 / (2 * c) * ProbabilityTheory.variance f T.μ ≤ Eg / 2 := by
    have : 1 / (2 * c) * ProbabilityTheory.variance f T.μ ≤ 1 / (2 * c) * (c * Eg) :=
      mul_le_mul_of_nonneg_left hPIf (by positivity)
    have e : 1 / (2 * c) * (c * Eg) = Eg / 2 := by field_simp
    linarith
  rw [← hE1] at hint
  linarith

end DualPoincare

section One

variable {T}
variable {g : E → ℝ}

/-- **BGL p. 272-273, case `n = 1`** (`CD(0,1)` and a Poincaré inequality `P(c)`; the book has `c = 1`).  For `g ∈ 𝒜₀` with
`e^{g/2} ∈ 𝒜₀` (the book's "Prop. 3.3.17 applies to `e^{ag}`"; automatic on compact triples), with `X = ∫ e^g Γ(g,Γ(g))`,
`Y = ∫ e^g Γ(g)²`:
* (i) `X + (2/3) Y ≤ 0` ("Comparing with (5.7.8) with `a = 1/2` indicates ..."; from `CD(0,1)` for `e^{g/3}`, i.e. (5.7.9) at `a = 1/3`, (5.7.7), (5.7.8));
* (ii) `(1/c) ∫ e^g Γ(g) ≤ ∫ e^g Γ₂(g)`, i.e. (5.7.12) with the convention `ρn/(n-1) = 1` when `c = 1`
  (from (5.7.13), the dual Poincaré inequality for `f = e^{g/2}`, and (i)). -/
theorem integral_exp_Γ₂_ge_one {c : ℝ} (hCD : T.CD 0 1) (hPI : T.toDiffusionTriple.PI c)
    (hg0 : g ∈ T.A₀) (he : (fun x => Real.exp (g x / 2)) ∈ T.A₀) :
    ((∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
        2 / 3 * ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ ≤ 0) ∧
    (1 / c) * ∫ x, Real.exp (g x) * G T g g x ∂T.μ ≤
      ∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ := by
  have hc : 0 < c := hPI.2.1
  have hgA := T.A₀_le g hg0
  have hMc := M_comb hg0
  have hibp := integral_exp_L_Γ hg0
  have hW := integral_exp_sq_L hg0 he
  -- (i): CD(0,1) for `e^{ag}`, `a = 1/3`
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = 1 / 3 := ⟨_, rfl⟩
  have hapos : 0 < a := by rw [ha_def]; norm_num
  have hfA : Pw g 1 a ∈ T.A := Pw_mem hgA 1 a
  have q0 := hCD.2 _ hfA
  have q1 := ΓA_comp_comp T (contDiff_kexp 1 a) hgA
  have q2 := L_Pw hgA 1 a
  have q3 := Γ₂_Pw hgA a
  have hpt : ∀ᵐ x ∂T.μ, Real.exp (g x) * (0 * T.toDiffusionTriple.Γ₂ g g x +
        0 * G T g (G T g g) x + a ^ 2 * (G T g g x) ^ 2 + 1 * (T.L g x) ^ 2 +
        (2 * a) * (T.L g x * G T g g x) + 0 * G T g g x) ≤
      Real.exp (g x) * (1 * T.toDiffusionTriple.Γ₂ g g x +
        (1 * a) * G T g (G T g g) x + (1 * a ^ 2) * (G T g g x) ^ 2 + 0 * (T.L g x) ^ 2 +
        0 * (T.L g x * G T g g x) + 0 * G T g g x) := by
    filter_upwards [q0, q1, q2, q3] with x h0 h1 h2 h3
    have h1' : G T (Pw g 1 a) (Pw g 1 a) x = (1 * a * Real.exp (a * g x)) ^ 2 * G T g g x := by
      have := h1
      simp only [deriv_kexp] at this
      exact this
    have hΓ : T.toDiffusionTriple.ΓA (Pw g 1 a) (Pw g 1 a) x =
        (1 * a * Real.exp (a * g x)) ^ 2 * G T g g x := h1'
    have hinv : ((1 : ℝ≥0∞)⁻¹).toReal = 1 := by simp
    rw [hΓ, hinv, h2, h3] at h0
    have hex : Real.exp (2 * a * g x) = Real.exp (a * g x) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hex] at h0
    have hK : 0 < a ^ 2 * Real.exp (a * g x) ^ 2 := by positivity
    have h5 : 0 * ((1 * a * Real.exp (a * g x)) ^ 2 * G T g g x) + 1 *
        (1 * a * Real.exp (a * g x) * T.L g x +
          1 * a * a * Real.exp (a * g x) * T.toDiffusionTriple.ΓA g g x) ^ 2 =
        a ^ 2 * Real.exp (a * g x) ^ 2 * (T.L g x + a * G T g g x) ^ 2 := by
      show 0 * _ + 1 * (1 * a * Real.exp (a * g x) * T.L g x +
          1 * a * a * Real.exp (a * g x) * G T g g x) ^ 2 = _
      ring
    have h6 : a ^ 2 * Real.exp (a * g x) ^ 2 * (T.toDiffusionTriple.Γ₂ g g x +
        a * G T g (G T g g) x + a ^ 2 * (G T g g x) ^ 2) =
        a ^ 2 * Real.exp (a * g x) ^ 2 * (1 * T.toDiffusionTriple.Γ₂ g g x +
        (1 * a) * G T g (G T g g) x + (1 * a ^ 2) * (G T g g x) ^ 2) := by ring
    rw [h5, h6] at h0
    have h7 : (T.L g x + a * G T g g x) ^ 2 ≤ 1 * T.toDiffusionTriple.Γ₂ g g x +
        (1 * a) * G T g (G T g g) x + (1 * a ^ 2) * (G T g g x) ^ 2 :=
      le_of_mul_le_mul_left h0 hK
    have h8 := mul_le_mul_of_nonneg_left h7 (Real.exp_pos (g x)).le
    refine le_trans (le_of_eq ?_) (le_trans h8 (le_of_eq ?_)) <;> ring
  have hint := integral_mono_ae (int_comb hg0 0 0 (a ^ 2) 1 (2 * a) 0)
    (int_comb hg0 1 (1 * a) (1 * a ^ 2) 0 0 0) hpt
  rw [hMc, hMc] at hint
  have hY : 0 ≤ ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ :=
    integral_nonneg fun x => mul_nonneg (Real.exp_pos _).le (sq_nonneg _)
  have hiA : (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
      2 / 3 * ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ ≤ 0 := by
    rw [ha_def] at hint
    linarith [hint, hibp, hW]
  refine ⟨hiA, ?_⟩
  -- (ii): the dual Poincaré inequality for `f = e^{g/2}` (BGL (5.7.13))
  have hdual := integral_Γ_le_of_PI T hPI he
  have hf : (fun x => Real.exp (g x / 2)) = Pw g 1 (1 / 2) := by
    funext x; simp [Pw]; ring_nf
  rw [hf] at hdual
  have a1 := Γ₂_Pw hgA (1 / 2)
  have b1 := ΓA_comp_comp T (contDiff_kexp 1 (1 / 2)) hgA
  have l1 : ∫ x, T.toDiffusionTriple.Γ₂ (Pw g 1 (1 / 2)) (Pw g 1 (1 / 2)) x ∂T.μ =
      ∫ x, Real.exp (g x) * ((1 / 4) * T.toDiffusionTriple.Γ₂ g g x +
        (1 / 8) * G T g (G T g g) x + (1 / 16) * (G T g g x) ^ 2 + 0 * (T.L g x) ^ 2 +
        0 * (T.L g x * G T g g x) + 0 * G T g g x) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [a1] with x hx
    rw [hx]
    have : 2 * (1 / 2 : ℝ) * g x = g x := by ring
    rw [this]; ring
  have l2 : ∫ x, T.toDiffusionTriple.ΓA (Pw g 1 (1 / 2)) (Pw g 1 (1 / 2)) x ∂T.μ =
      ∫ x, Real.exp (g x) * (0 * T.toDiffusionTriple.Γ₂ g g x +
        0 * G T g (G T g g) x + 0 * (G T g g x) ^ 2 + 0 * (T.L g x) ^ 2 +
        0 * (T.L g x * G T g g x) + (1 / 4) * G T g g x) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [b1] with x hx
    have hx' : G T (Pw g 1 (1 / 2)) (Pw g 1 (1 / 2)) x =
        (1 * (1 / 2) * Real.exp (1 / 2 * g x)) ^ 2 * G T g g x := by
      have := hx
      simp only [deriv_kexp] at this
      exact this
    show G T (Pw g 1 (1 / 2)) (Pw g 1 (1 / 2)) x = _
    rw [hx']
    have h1 : Real.exp (1 / 2 * g x) ^ 2 = Real.exp (g x) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have : (1 * (1 / 2) * Real.exp (1 / 2 * g x)) ^ 2 = (1 / 4) * Real.exp (1 / 2 * g x) ^ 2 := by ring
    rw [this, h1]; ring
  rw [l1, l2, hMc, hMc] at hdual
  have hgoal : ∫ x, Real.exp (g x) * G T g g x ∂T.μ ≤
      c * ((∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) +
        1 / 2 * (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
        1 / 4 * ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ) := by
    nlinarith [hdual]
  have hle : (∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) +
        1 / 2 * (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
        1 / 4 * ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ ≤
      ∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ := by
    linarith [hiA, hY]
  have h3 := mul_le_mul_of_nonneg_left hle hc.le
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc]
  linarith

end One

/-- **`∫ Θ(ε + P_s φ) → Θ(ε + ∫ φ)`** as `s → ∞` from a Poincaré inequality `P(c)` alone (the proof of
`tendsto_entE` uses `CD(ρ,·)`, `ρ > 0` only through `P(1/ρ)`; here `P(c)` is the hypothesis, as needed for `n = 1`, `ρ = 0`). -/
theorem tendsto_entE_of_PI [IsProbabilityMeasure T.μ] {c : ℝ} (hPI : T.toDiffusionTriple.PI c) (φ : T.A₀) {ε : ℝ}
    (hε : 0 < ε) (h0 : 0 ≤ᵐ[T.μ] φ.1) :
    Tendsto (T.entE φ ε) atTop
      (𝓝 ((ε + ∫ x, φ.1 x ∂T.μ) * Real.log (ε + ∫ x, φ.1 x ∂T.μ))) := by
  set S := DiffusionTriple.formData T.toDiffusionTriple with hS
  obtain ⟨C0, hC0⟩ := T.bounded φ.1 φ.2
  set M : ℝ := max C0 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hφM : ∀ x, φ.1 x ≤ M := fun x => (le_abs_self _).trans ((hC0 x).trans (le_max_left _ _))
  set m' : ℝ := ∫ x, φ.1 x ∂T.μ with hm'
  have hm'0 : 0 ≤ m' := integral_nonneg_of_ae h0
  have hm'M : m' ≤ M := by
    have : ∫ x, φ.1 x ∂T.μ ≤ ∫ _x, M ∂T.μ :=
      integral_mono (DiffusionTriple.integrable_of_mem T.toDiffusionTriple φ.2) (integrable_const M) hφM
    simpa using this
  set m : ℝ := ε + m' with hm
  have hmI : m ∈ Icc ε (ε + M) := ⟨by linarith, by linarith⟩
  -- the spectral decay
  have hdec := DiffusionTriple.expDecay_of_PI T.toDiffusionTriple T.esaProp hPI
  set u : Lp ℝ 2 T.μ := T.toDiffusionTriple.cls φ - m' • T.toDiffusionTriple.one2 with hu
  have hOrth : S.OrthFixed u := by
    intro v hv
    obtain ⟨c, hc⟩ := DiffusionTriple.fixed_const T.toDiffusionTriple T.ergodic v hv
    have hvc : v = c • T.toDiffusionTriple.one2 := by
      refine Lp.ext ?_
      filter_upwards [hc, T.toDiffusionTriple.coeFn_one2, Lp.coeFn_smul c T.toDiffusionTriple.one2] with x h1 h2 h3
      rw [h1, h3, Pi.smul_apply, h2]; simp
    rw [hvc, inner_smul_right, hu, inner_sub_left, inner_smul_left,
      DiffusionTriple.inner_cls_one2, DiffusionTriple.inner_one2_one2]
    simp [hm']
  set d : ℝ → Lp ℝ 2 T.μ := fun s => T.toDiffusionTriple.semigroup s.toNNReal (T.toDiffusionTriple.cls φ) - m' • T.toDiffusionTriple.one2 with hd
  have hnorm : ∀ s : ℝ, 0 ≤ s → ‖d s‖ ≤ Real.exp (-(1 / c) * s) * ‖u‖ := by
    intro s hs
    have h := hdec u hOrth s.toNNReal
    have e : S.semigroup s.toNNReal u = d s := by
      have hsg : S.semigroup s.toNNReal T.toDiffusionTriple.one2 = T.toDiffusionTriple.one2 :=
        DiffusionTriple.semigroup_one2 T.toDiffusionTriple T.esaProp _
      rw [hu, map_sub, map_smul, hsg]
      rfl
    rw [e, Real.coe_toNNReal s hs] at h
    exact h
  have hlim0 : Tendsto (fun s : ℝ => Real.exp (-(1 / c) * s) * ‖u‖) atTop (𝓝 0) := by
    have : Tendsto (fun s : ℝ => Real.exp (-(1 / c) * s)) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      refine tendsto_id.const_mul_atTop_of_neg ?_
      have hc : 0 < c := hPI.2.1
      have : 0 < 1 / c := by positivity
      linarith
    simpa using this.mul_const ‖u‖
  set K : ℝ := |Real.log ε| + |Real.log (ε + M)| + 1 with hK
  have hbound : ∀ s : ℝ, 0 ≤ s →
      ‖T.entE φ ε s - m * Real.log m‖ ≤ K * ‖d s‖ := by
    intro s hs
    have hy := T.entG_range φ hε hM h0 hφM s
    have hdae : ∀ᵐ x ∂T.μ, (d s : E → ℝ) x = T.Pt s.toNNReal φ x - m' := by
      filter_upwards [Lp.coeFn_sub (T.toDiffusionTriple.semigroup s.toNNReal (T.toDiffusionTriple.cls φ)) (m' • T.toDiffusionTriple.one2),
        Lp.coeFn_smul m' T.toDiffusionTriple.one2, T.toDiffusionTriple.coeFn_one2, T.Pt_ae s.toNNReal φ] with x h1 h2 h3 h4
      rw [hd]
      simp only
      rw [h1, Pi.sub_apply, h2, Pi.smul_apply, h3, h4]; simp
    -- integrability of `g log g`
    have hgm : AEStronglyMeasurable (fun x => T.entG φ ε s x * Real.log (T.entG φ ε s x)) T.μ := by
      have h1 : Measurable (T.entG φ ε s) :=
        measurable_const.add (T.A_measurable _ (T.Pt_mem_A _ φ))
      exact (Real.continuous_mul_log.measurable.comp h1).aestronglyMeasurable
    have hbd : ∀ᵐ x ∂T.μ, ‖T.entG φ ε s x * Real.log (T.entG φ ε s x)‖ ≤
        (ε + M) * (|Real.log ε| + |Real.log (ε + M)|) := by
      filter_upwards [hy] with x hx
      have hpos : 0 < T.entG φ ε s x := lt_of_lt_of_le hε hx.1
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hpos]
      have h1 : Real.log ε ≤ Real.log (T.entG φ ε s x) := Real.log_le_log hε hx.1
      have h2 : Real.log (T.entG φ ε s x) ≤ Real.log (ε + M) :=
        Real.log_le_log hpos hx.2
      have hl : |Real.log (T.entG φ ε s x)| ≤ |Real.log ε| + |Real.log (ε + M)| := by
        have := neg_abs_le (Real.log ε)
        have := le_abs_self (Real.log (ε + M))
        have := abs_nonneg (Real.log ε)
        have := abs_nonneg (Real.log (ε + M))
        rw [abs_le]; constructor <;> linarith
      exact mul_le_mul hx.2 hl (abs_nonneg _) (by linarith)
    have hgi : Integrable (fun x => T.entG φ ε s x * Real.log (T.entG φ ε s x)) T.μ :=
      Integrable.of_bound hgm _ hbd
    have e1 : T.entE φ ε s - m * Real.log m =
        ∫ x, (T.entG φ ε s x * Real.log (T.entG φ ε s x) - m * Real.log m) ∂T.μ := by
      rw [integral_sub hgi (integrable_const _)]
      simp [entE]
    have hdi : Integrable (fun x => K * |(d s : E → ℝ) x|) T.μ :=
      ((Lp.memLp (d s)).integrable one_le_two).abs.const_mul K
    rw [e1]
    refine (norm_integral_le_of_norm_le hdi ?_).trans ?_
    · filter_upwards [hy, hdae] with x hx hxd
      rw [Real.norm_eq_abs, hxd]
      have := lipschitz_mul_log hε hM.le hx hmI
      have e : T.entG φ ε s x - m = T.Pt s.toNNReal φ x - m' := by simp [entG, hm]
      rw [e] at this
      exact this
    · rw [integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      -- `∫ |d| ≤ ‖d‖`
      have h1 : ∫ x, |(d s : E → ℝ) x| ∂T.μ = inner ℝ |d s| T.toDiffusionTriple.one2 := by
        rw [L2_inner_eq]
        refine integral_congr_ae ?_
        filter_upwards [Lp.coeFn_abs (d s), T.toDiffusionTriple.coeFn_one2] with x h1 h2
        rw [h1, h2, mul_one]
      rw [h1]
      calc inner ℝ |d s| T.toDiffusionTriple.one2 ≤ ‖|d s|‖ * ‖T.toDiffusionTriple.one2‖ := real_inner_le_norm _ _
        _ = ‖d s‖ := by
          have : ‖T.toDiffusionTriple.one2‖ = 1 := by
            have h := DiffusionTriple.inner_one2_one2 T.toDiffusionTriple
            rw [real_inner_self_eq_norm_sq] at h
            nlinarith [norm_nonneg T.toDiffusionTriple.one2]
          rw [this, mul_one, norm_abs_eq']
  have hsq : Tendsto (fun s : ℝ => T.entE φ ε s - m * Real.log m) atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun s : ℝ => K * (Real.exp (-(1 / c) * s) * ‖u‖)) ?_
      (by simpa using hlim0.const_mul K)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    exact (hbound s hs).trans (mul_le_mul_of_nonneg_left (hnorm s hs) (by positivity))
  have := hsq.add_const (m * Real.log m)
  simpa using this

/-- **Entropy-Fisher inequality, Poincaré form** (proof of BGL Prop. 5.7.1 with the decay `I' ≤ -2κ I`):
`Ent(ε + φ) ≤ I(ε+φ)/(2κ)`.  The Poincaré inequality `P(c)` serves only the limit `e(s) → m log m`.
Same proof as `ent_le_fisher_dim`, with `P(c)` in place of `CD(ρ,n)`, `ρ > 0` (needed for `n = 1`, `ρ = 0`). -/
theorem ent_le_fisher_of_PI [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {c κ : ℝ}
    (hPI : T.toDiffusionTriple.PI c) (hκ : 0 < κ) (hD : T.FiniteDimInterpolation κ)
    (φ : T.A₀) (h0 : 0 ≤ᵐ[T.μ] φ.1) {ε : ℝ} (hε : 0 < ε) :
    Ent T.μ (fun x => ε + φ.1 x) ≤
      (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) / (2 * κ) := by
  obtain ⟨C0, hC0⟩ := T.bounded φ.1 φ.2
  set M : ℝ := max C0 1 with hMdef
  have hM : 0 < M := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hφM : ∀ x, φ.1 x ≤ M := fun x => (le_abs_self _).trans ((hC0 x).trans (le_max_left _ _))
  obtain ⟨C⟩ := BE.exists_cut hε hM.le
  set m : ℝ := ε + ∫ x, φ.1 x ∂T.μ with hm
  have key := BE.ent_le_of_decay (e := fun s => T.entE φ ε s - m * Real.log m)
    (q := fun s => -T.entI φ ε s) hκ
    ((hE.continuousOn_E φ ε hε h0).sub continuousOn_const)
    ((hE.continuousOn_I φ ε hε h0).neg)
    (fun s hs => (hE.hasDerivAt_E φ ε hε h0 s hs).sub_const _)
    (fun s hs => by
      obtain ⟨i1, i2, hd⟩ := hE.hasDerivAt_I φ ε M hε hM h0 hφM C s hs
      refine ⟨-(-2 * T.entJ C.Λ φ ε s), hd.neg, ?_⟩
      have hAg := entG_mem_A T φ ε s
      obtain ⟨B, hB1, hB2⟩ := hD.bdd φ ε hε h0 s hs
      have hint : κ * ∫ x, T.entG φ ε s x * T.toDiffusionTriple.ΓA (fun y => C.Λ (T.entG φ ε s y))
          (fun y => C.Λ (T.entG φ ε s y)) x ∂T.μ ≤ T.entJ C.Λ φ ε s :=
        hD.ext ε M hε hM _ hAg (entG_range T φ hε hM h0 hφM s) B hB1 hB2 C i1 i2
      rw [← entI_eq T φ hε hM h0 hφM C s] at hint
      show -2 * κ * -T.entI φ ε s ≤ -(-2 * T.entJ C.Λ φ ε s)
      nlinarith [hint])
    (by
      have := (tendsto_entE_of_PI T hPI φ hε h0).sub_const (m * Real.log m)
      simpa [hm] using this)
  have hφi : Integrable φ.1 T.μ := DiffusionTriple.integrable_of_mem T.toDiffusionTriple φ.2
  have hint : (∫ x, (ε + φ.1 x) ∂T.μ) = m := by
    rw [integral_add (integrable_const ε) hφi]; simp [hm]
  have eE0 : T.entE φ ε 0 = ∫ x, (ε + φ.1 x) * Real.log (ε + φ.1 x) ∂T.μ := by
    unfold entE
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_zero φ] with x hx
    simp only [entG, Real.toNNReal_zero, hx]
  have hEnt : Ent T.μ (fun x => ε + φ.1 x) = T.entE φ ε 0 - m * Real.log m := by
    unfold Ent
    rw [eE0, hint]
  have eI0 : T.entI φ ε 0 = ∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ := by
    unfold entI
    refine integral_congr_ae ?_
    filter_upwards [T.Pt_zero φ, ΓA_shift T ε (T.Pt_mem_A (0 : ℝ).toNNReal φ),
      T.ΓA_congr_A (T.Pt_mem_A (0 : ℝ).toNNReal φ) (T.A₀_le φ.1 φ.2) (by simpa using T.Pt_zero φ)]
      with x hx h1 h2
    have e : T.entG φ ε 0 = fun x => ε + T.Pt 0 φ x := by funext x; simp [entG]
    simp only [Real.toNNReal_zero] at h1 h2
    rw [e, h1, h2]
    show _ / (ε + T.Pt 0 φ x) = _
    rw [hx]
  rw [hEnt]
  have := key
  simp only [neg_neg] at this
  rw [eI0] at this
  exact this

/-- The bound for `ε + f²`: `Ent(ε + f²) ≤ (2/κ) ℰ(f)` (Poincaré form). -/
theorem ent_sq_add_le_of_PI [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation) {c κ : ℝ}
    (hPI : T.toDiffusionTriple.PI c) (hκ : 0 < κ) (hD : T.FiniteDimInterpolation κ)
    {f : E → ℝ} (hf : f ∈ T.A₀) {ε : ℝ} (hε : 0 < ε) :
    Ent T.μ (fun x => ε + f x ^ 2) ≤ 2 * (1 / κ) * ∫ x, T.Γ f f x ∂T.μ := by
  set φ : T.A₀ := ⟨fun x => f x ^ 2, sq_mem_A₀ T hf⟩ with hφ
  have h := ent_le_fisher_of_PI T hE hPI hκ hD φ (Eventually.of_forall fun x => sq_nonneg (f x)) hε
  have hfA : f ∈ T.A := T.A₀_le f hf
  have hΓi : Integrable (fun x => T.toDiffusionTriple.ΓA f f x) T.μ :=
    DiffusionTriple.integrable_of_mem T.toDiffusionTriple (ΓA_self_mem_A₀ T hf)
  have hint : (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) ≤
      4 * ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ := by
    rw [← integral_const_mul]
    have hc : (∫ x, T.toDiffusionTriple.ΓA φ.1 φ.1 x / (ε + φ.1 x) ∂T.μ) =
        ∫ x, 4 * f x ^ 2 * T.toDiffusionTriple.ΓA f f x / (ε + f x ^ 2) ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [ΓA_sq T hfA] with x hx
      simp only [hφ] at hx ⊢
      rw [hx]
    rw [hc]
    refine integral_mono_of_nonneg ?_ (hΓi.const_mul 4) ?_
    · filter_upwards [T.ΓA_nonneg f hfA] with x hx
      simp only [Pi.zero_apply]
      have : 0 ≤ T.toDiffusionTriple.ΓA f f x := hx
      positivity
    · filter_upwards [T.ΓA_nonneg f hfA] with x hx
      have hΓ0 : 0 ≤ T.toDiffusionTriple.ΓA f f x := hx
      have hpos : 0 < ε + f x ^ 2 := by positivity
      rw [div_le_iff₀ hpos]
      nlinarith [sq_nonneg (f x), mul_nonneg hΓ0 hε.le]
  refine h.trans ?_
  have h2κ : 0 < 2 * κ := by positivity
  rw [div_le_iff₀ h2κ]
  have e : ∫ x, T.Γ f f x ∂T.μ = ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ :=
    (integral_congr_ae (DiffusionTriple.ΓA_ae_eq T.toDiffusionTriple hf hf)).symm
  rw [e]
  have : 2 * (1 / κ) * (∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ) * (2 * κ) =
      4 * ∫ x, T.toDiffusionTriple.ΓA f f x ∂T.μ := by
    field_simp; ring
  rw [this]; exact hint

/-- `LS(1/κ, 0)` from a Poincaré inequality `P(c)` (any `c > 0`), `EntropyInterpolation` and `FiniteDimInterpolation T κ`, `κ > 0`.
`κ` is arbitrary here (for `κ` larger than the true decay rate the structure is false on nontrivial triples, as for
`logSobolev_of_finiteDim`); the `n = 1` headline `compact_logSobolev_one` pins `κ = 1/c`. -/
theorem logSobolev_of_PI_finiteDim [IsProbabilityMeasure T.μ] (hE : T.EntropyInterpolation)
    {c κ : ℝ} (hPI : T.toDiffusionTriple.PI c) (hκ : 0 < κ)
    (hD : T.FiniteDimInterpolation κ) : T.toDiffusionTriple.LS (1 / κ) 0 := by
  refine ⟨inferInstance, by positivity, le_refl _, fun f hf => ?_⟩
  have hφ := sq_mem_A₀ T hf
  have h2 : MemLp (fun x => f x ^ 2) 2 T.μ := DiffusionTriple.memLp2 T.toDiffusionTriple hφ
  have hlim := BE.tendsto_Ent_add T.μ h2
  have hle : Ent T.μ (fun x => f x ^ 2) ≤ 2 * (1 / κ) * ∫ x, T.Γ f f x ∂T.μ := by
    refine le_of_tendsto hlim ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ent_sq_add_le_of_PI T hE hPI hκ hD hf hε
  simpa [energy, dirichletForm] using hle


end FullTriple

/-! ### Compact triples, `n = 1` -/

namespace CompactTriple

variable {E : Type*} [MeasurableSpace E] (C : CompactTriple E)

/-- **`FiniteDimInterpolation` for `n = 1`** (BGL p. 272-273; `CD(0,1)` and `P(c)`, `κ = 1/c`) on every compact triple:
`bdd` from boundedness of `𝒜₀`, `ext` from `FullTriple.integral_exp_Γ₂_ge_one` applied to `g = Λ∘f ∈ 𝒜₀`, `e^{Λ∘f} = f`
(same proof as `CompactTriple.finiteDimInterpolation`, with (5.7.12) replaced by the `n = 1` inequality). -/
theorem finiteDimInterpolation_one {c : ℝ} (hCD : C.toFullTriple.CD 0 1)
    (hPI : C.toDiffusionTriple.PI c) : C.toFullTriple.FiniteDimInterpolation (1 / c) := by
  refine ⟨?_, ?_⟩
  · intro φ ε hε h0 s hs
    have hg0 : C.toFullTriple.entG φ ε s ∈ C.A₀ := C.entG_mem φ ε s
    obtain ⟨C1, hC1⟩ := C.toFullTriple.bounded _
      (FullTriple.ΓA_self_mem_A₀ C.toFullTriple hg0)
    obtain ⟨C2, hC2⟩ := C.toFullTriple.bounded _ (C.toFullTriple.L_mem _ hg0)
    refine ⟨max C1 C2, Eventually.of_forall fun x => ?_, Eventually.of_forall fun x => ?_⟩
    · exact (le_abs_self _).trans ((hC1 x).trans (le_max_left _ _))
    · exact (hC2 x).trans (le_max_right _ _)
  · intro ε M hε hM f hf hrange B _ _ Cut _ _
    have hfA0 : f ∈ C.A₀ := (C.A_eq f).1 hf
    have hg : (fun y => Cut.Λ (f y)) ∈ C.A := FullTriple.comp_mem_A C.toFullTriple Cut.hΛ hf
    have hg0 : (fun y => Cut.Λ (f y)) ∈ C.A₀ := (C.A_eq _).1 hg
    have he : (fun x => Real.exp ((fun y => Cut.Λ (f y)) x / 2)) ∈ C.A₀ := by
      have hψ : ContDiff ℝ (⊤ : ℕ∞) (fun r : ℝ => Real.exp (Cut.Λ r / 2)) :=
        Real.contDiff_exp.comp (Cut.hΛ.div_const 2)
      exact (C.A_eq _).1 (FullTriple.comp_mem_A C.toFullTriple hψ hf)
    have h := (FullTriple.integral_exp_Γ₂_ge_one (T := C.toFullTriple) hCD hPI hg0 he).2
    have hexp : ∀ᵐ x ∂C.μ, Real.exp (Cut.Λ (f x)) = f x := by
      filter_upwards [hrange] with x hx
      rw [Cut.Λ_eq hx]
      exact Real.exp_log (lt_of_lt_of_le hε hx.1)
    have e1 : ∫ x, Real.exp (Cut.Λ (f x)) * C.toFullTriple.G (fun y => Cut.Λ (f y))
        (fun y => Cut.Λ (f y)) x ∂C.μ =
        ∫ x, f x * C.toDiffusionTriple.ΓA (fun y => Cut.Λ (f y)) (fun y => Cut.Λ (f y)) x ∂C.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hexp] with x hx
      rw [hx]
    have e2 : ∫ x, Real.exp (Cut.Λ (f x)) * C.toDiffusionTriple.Γ₂ (fun y => Cut.Λ (f y))
        (fun y => Cut.Λ (f y)) x ∂C.μ =
        ∫ x, f x * C.toDiffusionTriple.Γ₂ (fun y => Cut.Λ (f y)) (fun y => Cut.Λ (f y)) x ∂C.μ := by
      refine integral_congr_ae ?_
      filter_upwards [hexp] with x hx
      rw [hx]
    rw [e2] at h
    rw [e1] at h
    exact h

/-- **BGL p. 273, the case `n = 1`**: on a compact triple, `CD(0,1)` and the Poincaré inequality `P(c)` give the tight
logarithmic Sobolev inequality `LS(c)` ("the logarithmic Sobolev inequality with constant 1 (equal to the Poincaré constant)",
`c = 1` in the book's normalisation of the torus), unconditionally. -/
theorem compact_logSobolev_one {c : ℝ} (hCD : C.toFullTriple.CD 0 1)
    (hPI : C.toDiffusionTriple.PI c) : C.toDiffusionTriple.LS c 0 := by
  have hc : 0 < c := hPI.2.1
  have h := FullTriple.logSobolev_of_PI_finiteDim C.toFullTriple C.entropyInterpolation hPI
    (κ := 1 / c) (by positivity) (C.finiteDimInterpolation_one hCD hPI)
  rwa [one_div_one_div] at h

/-- **On a compact triple with `CD(0,1)`: `LS(c) ⟺ P(c)`**: `⟸` is `compact_logSobolev_one` (BGL p. 273), `⟹` is
Prop. 5.1.3 (`CompactTriple.PI_of_LS`).  This is the book's "the constant is optimal since it is already optimal for the
Poincaré inequality" for `n = 1`. -/
theorem compact_LS_iff_PI_of_CD_zero_one {c : ℝ} (hCD : C.toFullTriple.CD 0 1) :
    C.toDiffusionTriple.LS c 0 ↔ C.toDiffusionTriple.PI c :=
  ⟨C.PI_of_LS, C.compact_logSobolev_one hCD⟩

end CompactTriple

end MarkovTriple.BGL
