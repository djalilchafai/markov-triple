import Mathlib
import MarkovTriple.BGL.Theory.Interp.EntropyChain
import MarkovTriple.BGL.Theory.Interp.EntropyLam
import MarkovTriple.BGL.Theory.Interp.EntropyHelp

/-!
# The identity behind `I' = -2J` (BGL Prop. 5.7.1), for a general `FullTriple` of finite measure

For `P ∈ 𝒜` with `0 ≤ P ≤ M`, `Γ(P) ≤ B`, `|L P| ≤ B`, `Γ(LP), L(LP), Γ₂(P) ∈ L¹` and `CD(ρ,n)`, with
`λ_k(y) = Λ^{(k)}(ε+y)`, `Q = L P`, `X = Γ(P)`, `a = λ₁(P) = 1/(ε+P)`, `b = λ₂(P)`, `c = λ₃(P)`, `u = λ₀(P)`:

`∫ a Q² + ∫ u L Q = 2 ∫ (ε+P) Γ₂(u)`  (`fisher_alg`),

and `(ε+P)Γ₂(u)`, `(ε+P)Γ(u)` are integrable (`fisher_integrable`).  The proof uses only Green's formula
(`ibp_gen`, i.e. `ibp_bdd`) with the bounded test functions `u, a, X, Q·a` and the `Γ₂` chain rule (`Γ₂_comp`);
`Γ(X) ≤ 4(Γ₂-ρΓ)Γ` (BGL (3.3.6), `reinforced_cd`) makes `X ∈ 𝒟(ℰ)`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

/-- bundle of the regularity facts about `P` used in the identity. -/
structure FisherHyp (T : FullTriple E) (P : E → ℝ) (M B : ℝ) : Prop where
  hB : 0 ≤ B
  A : P ∈ T.A
  range : ∀ᵐ x ∂T.μ, 0 ≤ P x ∧ P x ≤ M
  X_le : ∀ᵐ x ∂T.μ, G T P P x ≤ B
  Q_le : ∀ᵐ x ∂T.μ, |T.L P x| ≤ B
  ΓP : Integrable (G T P P) T.μ
  ΓQ : Integrable (G T (T.L P) (T.L P)) T.μ
  LQ : Integrable (T.L (T.L P)) T.μ
  Γ₂ : Integrable (T.toDiffusionTriple.Γ₂ P P) T.μ

section

variable [IsFiniteMeasure T.μ] {P : E → ℝ} {M B ε : ℝ}

omit [IsFiniteMeasure T.μ] in
lemma integrable_mul_bdd_A {f g : E → ℝ} (hf : f ∈ T.A) {K : ℝ} (hK : ∀ᵐ x ∂T.μ, |f x| ≤ K)
    (hg : Integrable g T.μ) : Integrable (fun x => f x * g x) T.μ := by
  refine (hg.norm.const_mul K).mono' ((T.A_measurable f hf).aestronglyMeasurable.mul
    hg.aestronglyMeasurable) ?_
  filter_upwards [hK] with x hx
  rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

omit [IsFiniteMeasure T.μ] in
lemma integral_lin4 {f1 f2 f3 f4 : E → ℝ} {r1 r2 r3 r4 : ℝ} (h1 : Integrable f1 T.μ)
    (h2 : Integrable f2 T.μ) (h3 : Integrable f3 T.μ) (h4 : Integrable f4 T.μ) :
    ∫ x, (r1 * f1 x + r2 * f2 x + r3 * f3 x + r4 * f4 x) ∂T.μ =
      r1 * ∫ x, f1 x ∂T.μ + r2 * ∫ x, f2 x ∂T.μ + r3 * ∫ x, f3 x ∂T.μ + r4 * ∫ x, f4 x ∂T.μ := by
  have j2 : Integrable (fun x => r1 * f1 x + r2 * f2 x) T.μ := (h1.const_mul r1).add (h2.const_mul r2)
  have j3 : Integrable (fun x => r1 * f1 x + r2 * f2 x + r3 * f3 x) T.μ := j2.add (h3.const_mul r3)
  rw [integral_add j3 (h4.const_mul r4), integral_add j2 (h3.const_mul r3),
    integral_add (h1.const_mul r1) (h2.const_mul r2), integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]

omit [IsFiniteMeasure T.μ] in
/-- `Γ(X) ∈ L¹` for `X = Γ(P)` (BGL (3.3.6)). -/
lemma FisherHyp.ΓX {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (h : FisherHyp T P M B) :
    Integrable (G T (G T P P) (G T P P)) T.μ := by
  have hX := G_mem (T := T) h.A h.A
  refine ((h.Γ₂.abs.const_mul (4 * B)).add (h.ΓP.const_mul (4 * B * |ρ|))).mono'
    (T.A_measurable _ (G_mem hX hX)).aestronglyMeasurable ?_
  filter_upwards [reinforced_cd hCD h.A, h.X_le, T.ΓA_nonneg P h.A, hCD.2 P h.A,
    T.ΓA_nonneg _ hX] with x h1 h2 h3 h4 h5
  have h3' : 0 ≤ G T P P x := h3
  have h5' : 0 ≤ G T (G T P P) (G T P P) x := h5
  have hW : 0 ≤ T.toDiffusionTriple.Γ₂ P P x - ρ * G T P P x := by
    have : 0 ≤ (n⁻¹).toReal * (T.L P x) ^ 2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
    show 0 ≤ T.toDiffusionTriple.Γ₂ P P x - ρ * T.toDiffusionTriple.ΓA P P x
    linarith
  rw [Real.norm_eq_abs, abs_of_nonneg h5']
  calc G T (G T P P) (G T P P) x ≤ 4 * (T.toDiffusionTriple.Γ₂ P P x - ρ * G T P P x) * G T P P x := h1
    _ ≤ 4 * (T.toDiffusionTriple.Γ₂ P P x - ρ * G T P P x) * B :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ ≤ 4 * B * |T.toDiffusionTriple.Γ₂ P P x| + 4 * B * |ρ| * G T P P x := by
        have e1 : T.toDiffusionTriple.Γ₂ P P x ≤ |T.toDiffusionTriple.Γ₂ P P x| := le_abs_self _
        have e2 : -(ρ * G T P P x) ≤ |ρ| * G T P P x := by
          have := neg_abs_le ρ
          nlinarith [abs_nonneg ρ]
        nlinarith [h.hB]

/-- **The identity** `∫ aQ² + ∫ u LQ = 2∫ (ε+P) Γ₂(u)` and the integrability of the two weighted integrands. -/
theorem fisher_alg {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (h : FisherHyp T P M B) (hε : 0 < ε)
    (C : BE.Cut ε M) :
    (Integrable (fun x => (ε + P x) * T.toDiffusionTriple.Γ₂ (fun y => lam0 C (P y))
        (fun y => lam0 C (P y)) x) T.μ ∧
      Integrable (fun x => (ε + P x) * G T (fun y => lam0 C (P y)) (fun y => lam0 C (P y)) x) T.μ) ∧
    (∫ x, lam1 C (P x) * T.L P x * T.L P x ∂T.μ + ∫ x, lam0 C (P x) * T.L (T.L P) x ∂T.μ =
      2 * ∫ x, (ε + P x) * T.toDiffusionTriple.Γ₂ (fun y => lam0 C (P y))
        (fun y => lam0 C (P y)) x ∂T.μ) := by
  have hP := h.A
  have hQA : T.L P ∈ T.A := L_memA hP
  have hXA : G T P P ∈ T.A := G_mem hP hP
  have hs0 := Lam.smooth0 C
  have hs1 := Lam.smooth1 C
  have hs2 := Lam.smooth2 C
  have hs3 := Lam.smooth3 C
  have huA : (fun x => lam0 C (P x)) ∈ T.A := comp_mem_A T hs0 hP
  have haA : (fun x => lam1 C (P x)) ∈ T.A := comp_mem_A T hs1 hP
  have hbA : (fun x => lam2 C (P x)) ∈ T.A := comp_mem_A T hs2 hP
  have hcA : (fun x => lam3 C (P x)) ∈ T.A := comp_mem_A T hs3 hP
  obtain ⟨K, hK0, hK⟩ := Lam.bounds C
  have hrel : ∀ᵐ x ∂T.μ, lam1 C (P x) = (ε + P x)⁻¹ ∧ lam2 C (P x) = -(lam1 C (P x)) ^ 2 ∧
      lam3 C (P x) = -2 * lam1 C (P x) * lam2 C (P x) := by
    filter_upwards [h.range] with x hx
    exact Lam.values C hx hε
  have hX0 : ∀ᵐ x ∂T.μ, 0 ≤ G T P P x := by
    filter_upwards [T.ΓA_nonneg P hP] with x hx; exact hx
  have hXb : ∀ᵐ x ∂T.μ, |G T P P x| ≤ B := by
    filter_upwards [hX0, h.X_le] with x h1 h2
    rw [abs_of_nonneg h1]; exact h2
  -- the chain-rule identities
  have F1 : G T (fun x => lam0 C (P x)) (fun x => lam0 C (P x)) =ᵐ[T.μ]
      fun x => lam1 C (P x) ^ 2 * G T P P x := by
    have := ΓA_comp_comp T hs0 hP
    rw [Lam.deriv0] at this
    exact this
  have F2 : G T (fun x => lam0 C (P x)) (T.L P) =ᵐ[T.μ]
      fun x => lam1 C (P x) * G T P (T.L P) x := by
    have := ΓA_comp_left T hs0 hP hQA
    rw [Lam.deriv0] at this
    exact this
  have F3 : G T (fun x => lam1 C (P x)) (fun x => lam1 C (P x)) =ᵐ[T.μ]
      fun x => lam2 C (P x) ^ 2 * G T P P x := by
    have := ΓA_comp_comp T hs1 hP
    rw [Lam.deriv1] at this
    exact this
  have F4 : G T (fun x => lam1 C (P x)) (G T P P) =ᵐ[T.μ]
      fun x => lam2 C (P x) * G T P (G T P P) x := by
    have := ΓA_comp_left T hs1 hP hXA
    rw [Lam.deriv1] at this
    exact this
  have F5 : G T (fun x => lam1 C (P x)) P =ᵐ[T.μ] fun x => lam2 C (P x) * G T P P x := by
    have := ΓA_comp_left T hs1 hP hP
    rw [Lam.deriv1] at this
    exact this
  have F6 : T.L (fun x => lam1 C (P x)) =ᵐ[T.μ]
      fun x => lam2 C (P x) * T.L P x + lam3 C (P x) * G T P P x := by
    have := L_comp T hs1 hP
    rw [Lam.deriv1, Lam.deriv2] at this
    exact this
  have F7 : T.toDiffusionTriple.Γ₂ (fun x => lam0 C (P x)) (fun x => lam0 C (P x)) =ᵐ[T.μ]
      fun x => lam1 C (P x) ^ 2 * T.toDiffusionTriple.Γ₂ P P x +
        lam1 C (P x) * lam2 C (P x) * G T P (G T P P) x + lam2 C (P x) ^ 2 * G T P P x ^ 2 := by
    have := Γ₂_comp hs0 hP
    rw [Lam.deriv0, Lam.deriv1] at this
    exact this
  -- integrability
  have iQ : Integrable (T.L P) T.μ := (memLp_of_bdd hQA h.Q_le).integrable one_le_two
  have iΓPQ : Integrable (G T P (T.L P)) T.μ := integrable_Γ_cross hP hQA h.ΓP h.ΓQ
  have iΓX : Integrable (G T (G T P P) (G T P P)) T.μ := h.ΓX hCD
  have iΓPX : Integrable (G T P (G T P P)) T.μ := integrable_Γ_cross hP hXA h.ΓP iΓX
  have iLX : Integrable (T.L (G T P P)) T.μ :=
    ((h.Γ₂.const_mul 2).add (iΓPQ.const_mul 2)).congr
      (Eventually.of_forall fun x => (L_G_self T P x).symm)
  have bu : ∀ᵐ x ∂T.μ, |lam0 C (P x)| ≤ K := Eventually.of_forall fun x => (hK (P x)).1
  have ba : ∀ᵐ x ∂T.μ, |lam1 C (P x)| ≤ K := Eventually.of_forall fun x => (hK (P x)).2.1
  have bb : ∀ᵐ x ∂T.μ, |lam2 C (P x)| ≤ K := Eventually.of_forall fun x => (hK (P x)).2.2.1
  have bc : ∀ᵐ x ∂T.μ, |lam3 C (P x)| ≤ K := Eventually.of_forall fun x => (hK (P x)).2.2.2
  have iΓu : Integrable (G T (fun x => lam0 C (P x)) (fun x => lam0 C (P x))) T.μ := by
    refine (h.ΓP.const_mul (K ^ 2)).mono' (T.A_measurable _ (G_mem huA huA)).aestronglyMeasurable ?_
    filter_upwards [F1, hX0] with x h1 h2
    have h1' : G T (fun x => lam0 C (P x)) (fun x => lam0 C (P x)) x = lam1 C (P x) ^ 2 * G T P P x := h1
    rw [Real.norm_eq_abs, h1', abs_of_nonneg (mul_nonneg (sq_nonneg _) h2)]
    refine mul_le_mul_of_nonneg_right ?_ h2
    have := (hK (P x)).2.1
    nlinarith [abs_nonneg (lam1 C (P x)), sq_abs (lam1 C (P x))]
  have iΓa : Integrable (G T (fun x => lam1 C (P x)) (fun x => lam1 C (P x))) T.μ := by
    refine (h.ΓP.const_mul (K ^ 2)).mono' (T.A_measurable _ (G_mem haA haA)).aestronglyMeasurable ?_
    filter_upwards [F3, hX0] with x h1 h2
    have h1' : G T (fun x => lam1 C (P x)) (fun x => lam1 C (P x)) x = lam2 C (P x) ^ 2 * G T P P x := h1
    rw [Real.norm_eq_abs, h1', abs_of_nonneg (mul_nonneg (sq_nonneg _) h2)]
    refine mul_le_mul_of_nonneg_right ?_ h2
    have := (hK (P x)).2.2.1
    nlinarith [abs_nonneg (lam2 C (P x)), sq_abs (lam2 C (P x))]
  have iLa : Integrable (T.L (fun x => lam1 C (P x))) T.μ := by
    refine (memLp_of_bdd (L_memA haA) (K := K * B + K * B) ?_).integrable one_le_two
    filter_upwards [F6, ba, bb, bc, h.Q_le, hXb] with x h1 h2 h3 h4 h5 h6
    rw [h1]
    calc |lam2 C (P x) * T.L P x + lam3 C (P x) * G T P P x|
        ≤ |lam2 C (P x) * T.L P x| + |lam3 C (P x) * G T P P x| := abs_add_le _ _
      _ ≤ K * B + K * B := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul h3 h5 (abs_nonneg _) hK0) (mul_le_mul h4 h6 (abs_nonneg _) hK0)
  -- Green's formulas
  have ibp_a := ibp_gen hQA h.Q_le h.ΓQ h.LQ huA bu iΓu
  have ibp_c := ibp_gen hXA hXb iΓX iLX haA ba iΓa
  have ibp_b := ibp_gen haA ba iΓa iLa hXA hXb iΓX
  have hQab : (fun x => lam1 C (P x)) * T.L P ∈ T.A := T.A.mul_mem haA hQA
  have iΓaQ : Integrable (G T ((fun x => lam1 C (P x)) * T.L P) ((fun x => lam1 C (P x)) * T.L P)) T.μ := by
    refine ((h.ΓQ.const_mul (2 * K ^ 2)).add (h.ΓP.const_mul (2 * B ^ 2 * K ^ 2))).mono'
      (T.A_measurable _ (G_mem hQab hQab)).aestronglyMeasurable ?_
    filter_upwards [Γ_prod_le haA hQA, F3, ba, h.Q_le, hX0, T.ΓA_nonneg _ hQab,
      T.ΓA_nonneg (T.L P) hQA, bb] with x h1 e3 h3 h4 h5 hn h6 h7
    have hn' : 0 ≤ G T ((fun x => lam1 C (P x)) * T.L P) ((fun x => lam1 C (P x)) * T.L P) x := hn
    have h6' : 0 ≤ G T (T.L P) (T.L P) x := h6
    have e3' : G T (fun x => lam1 C (P x)) (fun x => lam1 C (P x)) x = lam2 C (P x) ^ 2 * G T P P x := e3
    have s1 : lam1 C (P x) ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h3 2
    have s2 : T.L P x ^ 2 ≤ B ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h4 2
    have s3 : lam2 C (P x) ^ 2 ≤ K ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h7 2
    rw [Real.norm_eq_abs, abs_of_nonneg hn']
    have h1' : G T ((fun x => lam1 C (P x)) * T.L P) ((fun x => lam1 C (P x)) * T.L P) x ≤
        2 * lam1 C (P x) ^ 2 * G T (T.L P) (T.L P) x +
          2 * T.L P x ^ 2 * G T (fun x => lam1 C (P x)) (fun x => lam1 C (P x)) x := h1
    rw [e3'] at h1'
    show _ ≤ 2 * K ^ 2 * G T (T.L P) (T.L P) x + 2 * B ^ 2 * K ^ 2 * G T P P x
    have t1 : 2 * lam1 C (P x) ^ 2 * G T (T.L P) (T.L P) x ≤ 2 * K ^ 2 * G T (T.L P) (T.L P) x :=
      mul_le_mul_of_nonneg_right (by linarith) h6'
    have t2 : 2 * T.L P x ^ 2 * (lam2 C (P x) ^ 2 * G T P P x) ≤ 2 * B ^ 2 * K ^ 2 * G T P P x := by
      have : T.L P x ^ 2 * lam2 C (P x) ^ 2 ≤ B ^ 2 * K ^ 2 :=
        mul_le_mul s2 s3 (sq_nonneg _) (sq_nonneg _)
      nlinarith [mul_le_mul_of_nonneg_right this h5]
    linarith
  have hPb : ∀ᵐ x ∂T.μ, |P x| ≤ M := by
    filter_upwards [h.range] with x hx
    rw [abs_of_nonneg hx.1]; exact hx.2
  have bQa : ∀ᵐ x ∂T.μ, |((fun x => lam1 C (P x)) * T.L P) x| ≤ K * B := by
    filter_upwards [ba, h.Q_le] with x h1 h2
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hK0
  have ibp_d := ibp_gen hP hPb h.ΓP iQ hQab bQa iΓaQ
  -- conversions of the integrands
  have cv_a : ∫ x, G T (T.L P) (fun x => lam0 C (P x)) x ∂T.μ =
      ∫ x, lam1 C (P x) * G T P (T.L P) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [F2] with x hx
    rw [congrFun (G_comm (T := T) (T.L P) (fun x => lam0 C (P x))) x]
    exact hx
  have cv_c : ∫ x, G T (G T P P) (fun x => lam1 C (P x)) x ∂T.μ =
      ∫ x, lam2 C (P x) * G T P (G T P P) x ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [F4] with x hx
    rw [congrFun (G_comm (T := T) (G T P P) (fun x => lam1 C (P x))) x]
    exact hx
  have cv_b : ∫ x, G T (fun x => lam1 C (P x)) (G T P P) x ∂T.μ =
      ∫ x, lam2 C (P x) * G T P (G T P P) x ∂T.μ := integral_congr_ae F4
  have cv_b2' : ∫ x, G T P P x * T.L (fun x => lam1 C (P x)) x ∂T.μ =
      ∫ x, (lam2 C (P x) * T.L P x * G T P P x + lam3 C (P x) * G T P P x * G T P P x) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [F6] with x hx
    rw [hx]; ring
  have cv_d' : ∫ x, G T P ((fun x => lam1 C (P x)) * T.L P) x ∂T.μ =
      ∫ x, (lam1 C (P x) * G T P (T.L P) x + lam2 C (P x) * T.L P x * G T P P x) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [G_mul_right haA hQA hP, F5] with x h1 h2
    rw [h1, congrFun (G_comm (T := T) P (fun x => lam1 C (P x))) x, h2]
    ring
  -- pointwise facts
  have hga : ∀ᵐ x ∂T.μ, (ε + P x) * lam1 C (P x) = 1 := by
    filter_upwards [hrel, h.range] with x h1 h2
    rw [h1.1]
    exact mul_inv_cancel₀ (by linarith [h2.1])
  -- atoms
  have iF1 : Integrable (fun x => lam1 C (P x) * G T P (T.L P) x) T.μ :=
    integrable_mul_bdd_A haA ba iΓPQ
  have iF2 : Integrable (fun x => lam2 C (P x) * G T P (G T P P) x) T.μ :=
    integrable_mul_bdd_A hbA bb iΓPX
  have iF3 : Integrable (fun x => lam1 C (P x) * T.L (G T P P) x) T.μ :=
    integrable_mul_bdd_A haA ba iLX
  have hab : (fun x => lam1 C (P x) * lam2 C (P x) * G T P P x) ∈ T.A := by
    exact T.A.mul_mem (T.A.mul_mem haA hbA) hXA
  have iF4 : Integrable (fun x => lam1 C (P x) * lam2 C (P x) * G T P P x * G T P P x) T.μ := by
    refine integrable_mul_bdd_A (f := fun x => lam1 C (P x) * lam2 C (P x) * G T P P x)
      hab (K := K * K * B) ?_ h.ΓP
    filter_upwards [ba, bb, hXb] with x h1 h2 h3
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul h1 h2 (abs_nonneg _) hK0) h3 (abs_nonneg _) (by positivity)
  have hbQ : (fun x => lam2 C (P x) * T.L P x) ∈ T.A := T.A.mul_mem hbA hQA
  have iF5 : Integrable (fun x => lam2 C (P x) * T.L P x * G T P P x) T.μ := by
    refine integrable_mul_bdd_A (f := fun x => lam2 C (P x) * T.L P x) hbQ (K := K * B) ?_ h.ΓP
    filter_upwards [bb, h.Q_le] with x h1 h2
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hK0
  have hcX : (fun x => lam3 C (P x) * G T P P x) ∈ T.A := T.A.mul_mem hcA hXA
  have iF6 : Integrable (fun x => lam3 C (P x) * G T P P x * G T P P x) T.μ := by
    refine integrable_mul_bdd_A (f := fun x => lam3 C (P x) * G T P P x) hcX (K := K * B) ?_ h.ΓP
    filter_upwards [bc, hXb] with x h1 h2
    rw [abs_mul]
    exact mul_le_mul h1 h2 (abs_nonneg _) hK0
  -- Green's formulas in canonical form
  have R_a : ∫ x, lam1 C (P x) * G T P (T.L P) x ∂T.μ = -∫ x, lam0 C (P x) * T.L (T.L P) x ∂T.μ := by
    rw [← cv_a]; exact ibp_a
  have R_c : ∫ x, lam2 C (P x) * G T P (G T P P) x ∂T.μ =
      -∫ x, lam1 C (P x) * T.L (G T P P) x ∂T.μ := by
    rw [← cv_c]; exact ibp_c
  have R_b : ∫ x, lam2 C (P x) * G T P (G T P P) x ∂T.μ =
      -(∫ x, lam2 C (P x) * T.L P x * G T P P x ∂T.μ +
        ∫ x, lam3 C (P x) * G T P P x * G T P P x ∂T.μ) := by
    rw [← cv_b, ibp_b, cv_b2', integral_add iF5 iF6]
  have R_d : ∫ x, lam1 C (P x) * G T P (T.L P) x ∂T.μ +
      ∫ x, lam2 C (P x) * T.L P x * G T P P x ∂T.μ =
      -∫ x, lam1 C (P x) * T.L P x * T.L P x ∂T.μ := by
    rw [← integral_add iF1 iF5, ← cv_d', ibp_d]
    simp only [Pi.mul_apply]
  have R_e : ∫ x, lam3 C (P x) * G T P P x * G T P P x ∂T.μ =
      -2 * ∫ x, lam1 C (P x) * lam2 C (P x) * G T P P x * G T P P x ∂T.μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hrel] with x hx
    rw [hx.2.2]; ring
  -- the weighted Γ₂ integrand
  have pw : ∀ᵐ x ∂T.μ, (ε + P x) * T.toDiffusionTriple.Γ₂ (fun y => lam0 C (P y))
      (fun y => lam0 C (P y)) x =
      (1 / 2) * (lam1 C (P x) * T.L (G T P P) x) + (-1) * (lam1 C (P x) * G T P (T.L P) x) +
        1 * (lam2 C (P x) * G T P (G T P P) x) +
        (-1) * (lam1 C (P x) * lam2 C (P x) * G T P P x * G T P P x) := by
    filter_upwards [F7, hrel, h.range] with x h1 h2 h3
    have hg0 : 0 < ε + P x := by linarith [h3.1]
    rw [h1, L_G_self T P x]
    obtain ⟨e1, e2, -⟩ := h2
    rw [e2, e1]
    field_simp
    ring
  have hRHS : Integrable (fun x => (1 / 2) * (lam1 C (P x) * T.L (G T P P) x) +
      (-1) * (lam1 C (P x) * G T P (T.L P) x) + 1 * (lam2 C (P x) * G T P (G T P P) x) +
      (-1) * (lam1 C (P x) * lam2 C (P x) * G T P P x * G T P P x)) T.μ := by
    have j3 : Integrable (fun x => (1 / 2) * (lam1 C (P x) * T.L (G T P P) x) +
        (-1) * (lam1 C (P x) * G T P (T.L P) x)) T.μ := (iF3.const_mul _).add (iF1.const_mul _)
    have j4 : Integrable (fun x => (1 / 2) * (lam1 C (P x) * T.L (G T P P) x) +
        (-1) * (lam1 C (P x) * G T P (T.L P) x) + 1 * (lam2 C (P x) * G T P (G T P P) x)) T.μ :=
      j3.add (iF2.const_mul _)
    exact j4.add (iF4.const_mul _)
  refine ⟨⟨hRHS.congr (pw.mono fun x hx => hx.symm), ?_⟩, ?_⟩
  · refine (integrable_mul_bdd_A haA ba h.ΓP).congr ?_
    filter_upwards [F1, hga] with x h1 h2
    have h1' : G T (fun x => lam0 C (P x)) (fun x => lam0 C (P x)) x = lam1 C (P x) ^ 2 * G T P P x := h1
    show lam1 C (P x) * G T P P x = (ε + P x) * G T (fun y => lam0 C (P y)) (fun y => lam0 C (P y)) x
    rw [h1']
    linear_combination (-(lam1 C (P x) * G T P P x)) * h2
  · rw [integral_congr_ae pw, integral_lin4 iF3 iF1 iF2 iF4]
    linarith

end

end FullTriple

end MarkovTriple.BGL
