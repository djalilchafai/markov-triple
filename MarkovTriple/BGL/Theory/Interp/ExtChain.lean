import Mathlib
import MarkovTriple.BGL.Theory.Interp.ExtBdd

/-!
# BGL (5.7.7)-(5.7.8) for bounded `g ∈ 𝒜` (the extension step of Thm 5.7.4, p. 272)

The chain of `Theory/LogSobolevDimChain.lean` (proved there for `g ∈ 𝒜₀` with `e^{g/2} ∈ 𝒜₀`) redone for `Bdd T g`
(`g ∈ 𝒜` bounded together with `Γ(g)` and `L g`; finite measure; `CD(ρ,n)`):
`[g] ∈ 𝒟(L)` (Prop. 3.3.6), `∫Γ₂(e^{g/2}) = ∫(L e^{g/2})²` (Prop. 3.3.17), the integration by parts (5.7.7) against
`e^g Γ(g) ∈ 𝒜 ∩ 𝒟(ℰ)` (`ibp_of_domain`; `Γ(Γ g) ∈ L¹` by the reinforced inequality (3.3.6)).
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E} [IsFiniteMeasure T.μ] {g : E → ℝ}

omit [IsFiniteMeasure T.μ] in
lemma Bdd.bounds (hb : Bdd T g) : ∃ K B : ℝ, 0 ≤ K ∧ 0 ≤ B ∧ (∀ᵐ x ∂T.μ, |g x| ≤ K) ∧
    (∀ᵐ x ∂T.μ, |G T g g x| ≤ B) ∧ ∀ᵐ x ∂T.μ, |T.L g x| ≤ B := by
  obtain ⟨hA, K, B, hK, hΓ, hL⟩ := hb
  refine ⟨|K|, |B|, abs_nonneg _, abs_nonneg _, hK.mono fun x hx => hx.trans (le_abs_self _), ?_,
    hL.mono fun x hx => hx.trans (le_abs_self _)⟩
  filter_upwards [hΓ, T.ΓA_nonneg g hA] with x h1 h2
  have : 0 ≤ G T g g x := h2
  rw [abs_of_nonneg this]; exact h1.trans (le_abs_self _)

omit [IsFiniteMeasure T.μ] in
lemma Bdd.measurable_g (hb : Bdd T g) : Measurable g := T.A_measurable _ hb.memA

/-- `e^g · φ` is integrable for bounded measurable `φ`. -/
lemma Bdd.intW (hb : Bdd T g) {φ : E → ℝ} (hm : Measurable φ) {C : ℝ}
    (hC : ∀ᵐ x ∂T.μ, |φ x| ≤ C) : Integrable (fun x => Real.exp (g x) * φ x) T.μ := by
  obtain ⟨K, B, hK0, -, hK, -, -⟩ := hb.bounds
  refine intB (hb.measurable_g.exp.mul hm) (C := Real.exp K * C) ?_
  filter_upwards [hK, hC] with x h1 h2
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  have h3 : Real.exp (g x) ≤ Real.exp K := Real.exp_le_exp.2 ((le_abs_self _).trans h1)
  exact mul_le_mul h3 h2 (abs_nonneg _) (Real.exp_pos _).le

omit [IsFiniteMeasure T.μ] in
/-- `e^g · φ` is integrable for `φ ∈ L¹`. -/
lemma Bdd.intW1 (hb : Bdd T g) {φ : E → ℝ} (hφ : Integrable φ T.μ) :
    Integrable (fun x => Real.exp (g x) * φ x) T.μ := by
  obtain ⟨K, B, hK0, -, hK, -, -⟩ := hb.bounds
  refine (hφ.bdd_mul (c := Real.exp K) hb.measurable_g.exp.aestronglyMeasurable ?_).congr
    (Eventually.of_forall fun x => by simp [mul_comm])
  filter_upwards [hK] with x h1
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 ((le_abs_self _).trans h1)

omit [IsFiniteMeasure T.μ] in
lemma Bdd.expg_memA (hb : Bdd T g) : (fun x => Real.exp (g x)) ∈ T.A :=
  comp_mem_A T Real.contDiff_exp hb.memA

/-- **(5.7.7)** for bounded `g` (BGL p. 271), and the integrability of `e^g Γ(g,Γ(g))`. -/
theorem integral_exp_L_Γ_bdd {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hb : Bdd T g) :
    Integrable (fun x => Real.exp (g x) * G T g (G T g g) x) T.μ ∧
    ∫ x, Real.exp (g x) * (T.L g x * G T g g x) ∂T.μ =
      -(∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) -
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
  have hgA := hb.memA
  have hu : G T g g ∈ T.A := G_mem hgA hgA
  have hEA := hb.expg_memA
  obtain ⟨K, B, hK0, hB0, hK, hu_b, hl_b⟩ := hb.bounds
  set k : E → ℝ := G T g g * (fun x => Real.exp (g x)) with hk
  have hkA : k ∈ T.A := T.A.mul_mem hu hEA
  have hkb : ∀ᵐ x ∂T.μ, |k x| ≤ B * Real.exp K := by
    filter_upwards [hK, hu_b] with x h1 h2
    simp only [hk, Pi.mul_apply]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul h2 (Real.exp_le_exp.2 ((le_abs_self _).trans h1)) (Real.exp_pos _).le hB0
  have hΓu := hb.integrable_ΓΓ hCD
  have hΓk : Integrable (G T k k) T.μ := by
    have hΓE : ∀ᵐ x ∂T.μ, G T (fun x => Real.exp (g x)) (fun x => Real.exp (g x)) x =
        Real.exp (g x) ^ 2 * G T g g x := by
      filter_upwards [ΓA_comp_comp T Real.contDiff_exp hgA] with x hx
      have hx' := hx
      rw [Real.deriv_exp] at hx'
      exact hx'
    refine ((integrable_const (2 * B ^ 2 * (Real.exp K ^ 2 * B))).add
      (hΓu.const_mul (2 * Real.exp K ^ 2))).mono'
      (T.A_measurable _ (G_mem hkA hkA)).aestronglyMeasurable ?_
    filter_upwards [Γ_prod_le hu hEA, hΓE, hK, hu_b, T.ΓA_nonneg k hkA, T.ΓA_nonneg g hgA,
      T.ΓA_nonneg _ hu] with x h1 h2 h3 h4 h5 h6 h7
    have h5' : 0 ≤ G T k k x := h5
    have h6' : 0 ≤ G T g g x := h6
    have h7' : 0 ≤ G T (G T g g) (G T g g) x := h7
    rw [Real.norm_eq_abs, abs_of_nonneg h5']
    refine h1.trans ?_
    have e1 : Real.exp (g x) ≤ Real.exp K := Real.exp_le_exp.2 ((le_abs_self _).trans h3)
    have e2 : Real.exp (g x) ^ 2 ≤ Real.exp K ^ 2 :=
      pow_le_pow_left₀ (Real.exp_pos _).le e1 2
    have e3 : G T g g x ≤ B := (le_abs_self _).trans h4
    have e5 : G T g g x ^ 2 ≤ B ^ 2 := pow_le_pow_left₀ h6' e3 2
    have e6 : Real.exp (g x) ^ 2 * G T g g x ≤ Real.exp K ^ 2 * B :=
      mul_le_mul e2 e3 h6' (sq_nonneg _)
    have e7 : G T (fun x => Real.exp (g x)) (fun x => Real.exp (g x)) x ≤ Real.exp K ^ 2 * B := by
      rw [h2]; exact e6
    have e8 : 0 ≤ G T (fun x => Real.exp (g x)) (fun x => Real.exp (g x)) x := by
      rw [h2]; positivity
    rw [← hk] at h1
    have t1 := mul_le_mul e5 e7 e8 (sq_nonneg B)
    have t2 := mul_le_mul_of_nonneg_right e2 h7'
    simp only [Pi.add_apply]
    linarith [t1, t2]
  obtain ⟨hint, hibp⟩ := ibp_of_domain hgA hb.memLp2 hb.domain hkA (memLp_of_bdd hkA hkb)
    (memQ_of_bdd hkA hkb hΓk)
  have a1 := G_mul_left (T := T) hu hEA hgA
  have a2 := ΓA_comp_left T Real.contDiff_exp hgA hgA
  have e1 : ∀ᵐ x ∂T.μ, G T g k x =
      Real.exp (g x) * G T g (G T g g) x + Real.exp (g x) * (G T g g x) ^ 2 := by
    filter_upwards [a1, a2] with x h1 h2
    rw [congrFun (G_comm (T := T) g k) x, hk, h1]
    have h3 : G T (fun x => Real.exp (g x)) g x = Real.exp (g x) * G T g g x := by
      have h2' := h2
      rw [Real.deriv_exp] at h2'
      exact h2'
    rw [h3, congrFun (G_comm (T := T) (G T g g) g) x]; ring
  have iu2 : Integrable (fun x => Real.exp (g x) * (G T g g x) ^ 2) T.μ :=
    hb.intW ((T.A_measurable _ hu).pow_const 2) (C := B ^ 2) (by
      filter_upwards [hu_b] with x h1
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2)
  have iv : Integrable (fun x => Real.exp (g x) * G T g (G T g g) x) T.μ := by
    refine (hint.sub iu2).congr ?_
    filter_upwards [e1] with x hx
    simp only [Pi.sub_apply]
    rw [hx]; ring
  refine ⟨iv, ?_⟩
  have e2 : ∫ x, G T g k x ∂T.μ =
      (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
    rw [← integral_add iv iu2]
    exact integral_congr_ae e1
  have e3 : ∫ x, T.L g x * k x ∂T.μ =
      ∫ x, Real.exp (g x) * (T.L g x * G T g g x) ∂T.μ := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hk, Pi.mul_apply]; ring
  rw [e2, e3] at hibp
  linarith

/-- the six integrable weighted terms. -/
theorem Bdd.ints {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hb : Bdd T g) :
    Integrable (fun x => Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x) T.μ ∧
    Integrable (fun x => Real.exp (g x) * G T g (G T g g) x) T.μ ∧
    Integrable (fun x => Real.exp (g x) * (G T g g x) ^ 2) T.μ ∧
    Integrable (fun x => Real.exp (g x) * (T.L g x) ^ 2) T.μ ∧
    Integrable (fun x => Real.exp (g x) * (T.L g x * G T g g x)) T.μ ∧
    Integrable (fun x => Real.exp (g x) * G T g g x) T.μ := by
  have hgA := hb.memA
  have hu : G T g g ∈ T.A := G_mem hgA hgA
  have hl : T.L g ∈ T.A := L_memA hgA
  obtain ⟨K, B, hK0, hB0, hK, hu_b, hl_b⟩ := hb.bounds
  have mu := T.A_measurable _ hu
  have ml := T.A_measurable _ hl
  refine ⟨hb.intW1 (hb.integrable_Γ₂ hCD), (integral_exp_L_Γ_bdd hCD hb).1,
    hb.intW (mu.pow_const 2) (C := B ^ 2) ?_, hb.intW (ml.pow_const 2) (C := B ^ 2) ?_,
    hb.intW (ml.mul mu) (C := B * B) ?_, hb.intW mu hu_b⟩
  · filter_upwards [hu_b] with x h1
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  · filter_upwards [hl_b] with x h1
    rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  · filter_upwards [hu_b, hl_b] with x h1 h2
    rw [abs_mul]; exact mul_le_mul h2 h1 (abs_nonneg _) hB0

lemma int_comb' {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hb : Bdd T g) (c0 c1 c2 c3 c4 c5 : ℝ) :
    Integrable (fun x => Real.exp (g x) * (c0 * T.toDiffusionTriple.Γ₂ g g x +
      c1 * G T g (G T g g) x + c2 * (G T g g x) ^ 2 + c3 * (T.L g x) ^ 2 +
      c4 * (T.L g x * G T g g x) + c5 * G T g g x)) T.μ := by
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := hb.ints hCD
  have e : (fun x => Real.exp (g x) * (c0 * T.toDiffusionTriple.Γ₂ g g x +
      c1 * G T g (G T g g) x + c2 * (G T g g x) ^ 2 + c3 * (T.L g x) ^ 2 +
      c4 * (T.L g x * G T g g x) + c5 * G T g g x)) = fun x =>
      c0 * (Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x) +
      c1 * (Real.exp (g x) * G T g (G T g g) x) + c2 * (Real.exp (g x) * (G T g g x) ^ 2) +
      c3 * (Real.exp (g x) * (T.L g x) ^ 2) +
      c4 * (Real.exp (g x) * (T.L g x * G T g g x)) + c5 * (Real.exp (g x) * G T g g x) := by
    funext x; ring
  rw [e]
  exact (((((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _)).add
    (i3.const_mul _)).add (i4.const_mul _)).add (i5.const_mul _)

/-- the weighted moment of the combination. -/
lemma M_comb' {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hb : Bdd T g) (c0 c1 c2 c3 c4 c5 : ℝ) :
    ∫ x, Real.exp (g x) * (c0 * T.toDiffusionTriple.Γ₂ g g x +
      c1 * G T g (G T g g) x + c2 * (G T g g x) ^ 2 + c3 * (T.L g x) ^ 2 +
      c4 * (T.L g x * G T g g x) + c5 * G T g g x) ∂T.μ =
    c0 * (∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) +
    c1 * (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
    c2 * (∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ) +
    c3 * (∫ x, Real.exp (g x) * (T.L g x) ^ 2 ∂T.μ) +
    c4 * (∫ x, Real.exp (g x) * (T.L g x * G T g g x) ∂T.μ) +
    c5 * (∫ x, Real.exp (g x) * G T g g x ∂T.μ) := by
  obtain ⟨i0, i1, i2, i3, i4, i5⟩ := hb.ints hCD
  have e : (fun x => Real.exp (g x) * (c0 * T.toDiffusionTriple.Γ₂ g g x +
      c1 * G T g (G T g g) x + c2 * (G T g g x) ^ 2 + c3 * (T.L g x) ^ 2 +
      c4 * (T.L g x * G T g g x) + c5 * G T g g x)) = fun x =>
      c0 * (Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x) +
      c1 * (Real.exp (g x) * G T g (G T g g) x) + c2 * (Real.exp (g x) * (G T g g x) ^ 2) +
      c3 * (Real.exp (g x) * (T.L g x) ^ 2) +
      c4 * (Real.exp (g x) * (T.L g x * G T g g x)) + c5 * (Real.exp (g x) * G T g g x) := by
    funext x; ring
  rw [e, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]
  all_goals first
    | exact (((((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _)).add
        (i3.const_mul _)).add (i4.const_mul _))
    | exact ((((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _)).add (i3.const_mul _))
    | exact (((i0.const_mul _).add (i1.const_mul _)).add (i2.const_mul _))
    | exact ((i0.const_mul _).add (i1.const_mul _))
    | exact (i0.const_mul _)
    | exact (i1.const_mul _) | exact (i2.const_mul _) | exact (i3.const_mul _)
    | exact (i4.const_mul _) | exact (i5.const_mul _)

/-- **(5.7.8) at `a = 1/2`** for bounded `g`: `∫ e^g (Lg)² = ∫ e^g Γ₂(g) + 3/2 ∫ e^g Γ(g,Γ(g)) + ∫ e^g Γ(g)²`
(BGL p. 271; `∫Γ₂(e^{g/2}) = ∫(L e^{g/2})²` is Prop. 3.3.17 for `e^{g/2} ∈ 𝒜 ∩ 𝒟(L)`). -/
theorem integral_exp_sq_L_bdd {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hb : Bdd T g) :
    ∫ x, Real.exp (g x) * (T.L g x) ^ 2 ∂T.μ =
      (∫ x, Real.exp (g x) * T.toDiffusionTriple.Γ₂ g g x ∂T.μ) +
      3 / 2 * (∫ x, Real.exp (g x) * G T g (G T g g) x ∂T.μ) +
        ∫ x, Real.exp (g x) * (G T g g x) ^ 2 ∂T.μ := by
  have hgA := hb.memA
  have hMc := M_comb' hCD hb
  have hibp := (integral_exp_L_Γ_bdd hCD hb).2
  have hh : Bdd T (Pw g 1 (1 / 2)) := Bdd.comp (ψ := fun r : ℝ => 1 * Real.exp (1 / 2 * r)) (contDiff_kexp 1 (1 / 2)) hb
  have h338 := (integrable_Γ₂_of_domain hCD hh.memA hh.memLp2 hh.domain).2.2
  have a1 := Γ₂_Pw hgA (1 / 2)
  have a2 := L_Pw hgA 1 (1 / 2)
  have l1 : ∫ x, T.toDiffusionTriple.Γ₂ (Pw g 1 (1 / 2)) (Pw g 1 (1 / 2)) x ∂T.μ =
      ∫ x, Real.exp (g x) * ((1 / 4) * T.toDiffusionTriple.Γ₂ g g x +
        (1 / 8) * G T g (G T g g) x + (1 / 16) * (G T g g x) ^ 2 + 0 * (T.L g x) ^ 2 +
        0 * (T.L g x * G T g g x) + 0 * G T g g x) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [a1] with x hx
    rw [hx]
    have : 2 * (1 / 2 : ℝ) * g x = g x := by ring
    rw [this]; ring
  have l2 : ∫ x, (T.L (Pw g 1 (1 / 2)) x) ^ 2 ∂T.μ =
      ∫ x, Real.exp (g x) * (0 * T.toDiffusionTriple.Γ₂ g g x +
        0 * G T g (G T g g) x + (1 / 16) * (G T g g x) ^ 2 + (1 / 4) * (T.L g x) ^ 2 +
        (1 / 4) * (T.L g x * G T g g x) + 0 * G T g g x) ∂T.μ := by
    refine integral_congr_ae ?_
    filter_upwards [a2] with x hx
    rw [hx]
    have h1 : Real.exp (1 / 2 * g x) * Real.exp (1 / 2 * g x) = Real.exp (g x) := by
      rw [← Real.exp_add]; congr 1; ring
    calc _ = (Real.exp (1 / 2 * g x) * Real.exp (1 / 2 * g x)) *
          ((1 / 4) * (T.L g x) ^ 2 + (1 / 4) * (T.L g x * G T g g x) +
          (1 / 16) * (G T g g x) ^ 2) := by
            show (1 * (1 / 2 : ℝ) * Real.exp (1 / 2 * g x) * T.L g x +
              1 * (1 / 2) * (1 / 2) * Real.exp (1 / 2 * g x) * G T g g x) ^ 2 = _
            ring
      _ = _ := by rw [h1]; ring
  rw [l1, l2, hMc, hMc] at h338
  linarith

end FullTriple

end MarkovTriple.BGL
