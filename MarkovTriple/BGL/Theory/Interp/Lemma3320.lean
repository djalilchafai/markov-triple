import Mathlib
import MarkovTriple.BGL.Theory.Interp.PsiBounds
import MarkovTriple.BGL.Theory.Strong.Interpolation
import MarkovTriple.BGL.Theory.Extension.Gamma2Ident
import MarkovTriple.BGL.Theory.Extension.GammaELin

/-!
# BGL Lemma 3.3.20 (p. 163): `G_ε = √(Γ(g) + ε²) - ε ∈ 𝒟(ℰ)`, plus `L G_ε ∈ L¹`

For `g ∈ 𝒜` with `[g] ∈ 𝒟(L)`, `L g ∈ 𝒟(ℰ)` (the case `g = P_τ f`, `f ∈ 𝒜₀`) and `CD(ρ,n)`:
`G_ε = ψ_ε(Γ g) ∈ 𝒜 ∩ L²`, `[G_ε] ∈ 𝒟(ℰ)` (Prop. 3.3.6 (ii) + the bound `Γ(G_ε) ≤ Γ₂(g) - ρΓ(g)`, the book's
"extended Γ₂ inequality (3.2.4)"), and `L G_ε ∈ L¹` (via `L G_ε = ψ'(u) L u + ψ''(u) Γ(u)`, `L u = 2Γ₂ + 2Γ(g,Lg)`).
Only the forward direction of Prop. 3.3.17 (`integrable_Γ₂_of_domain`) is used.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

section

variable {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) {g : E → ℝ} (hg : g ∈ T.A) (hg2 : MemLp g 2 T.μ)
  (hu : hg2.toLp g ∈ T.toDiffusionTriple.generator.domain) {ε : ℝ} (hε : 0 < ε)

include hCD hg hg2 hu in
/-- `W := Γ₂(g) - ρΓ(g)` is a.e. nonnegative and integrable. -/
lemma W_facts : Integrable (fun x => T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x) T.μ ∧
    0 ≤ᵐ[T.μ] (fun x => T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x) := by
  obtain ⟨hΓi, hΓ₂i, -⟩ := integrable_Γ₂_of_domain hCD hg hg2 hu
  refine ⟨hΓ₂i.sub (hΓi.const_mul ρ), ?_⟩
  filter_upwards [hCD.2 g hg] with x hx
  have : 0 ≤ (n⁻¹).toReal * (T.L g x) ^ 2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  show 0 ≤ T.toDiffusionTriple.Γ₂ g g x - ρ * T.toDiffusionTriple.ΓA g g x
  linarith

include hCD hg hε in
/-- pointwise: `0 ≤ Γ(G_ε) ≤ W` and `|ψ''(u)|Γ(u) ≤ W/ε`. -/
lemma pointwise_bounds :
    ∀ᵐ x ∂T.μ, 0 ≤ G T g g x ∧
      G T (fun y => psiS ε (G T g g y)) (fun y => psiS ε (G T g g y)) x ≤
        T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x ∧
      |deriv (deriv (psiS ε)) (G T g g x)| * G T (G T g g) (G T g g) x ≤
        (T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x) / ε := by
  have hu : G T g g ∈ T.A := G_mem hg hg
  have a1 := ΓA_comp_comp T (psiS_smooth hε) hu
  have a2 := reinforced_cd hCD hg
  have a3 := hCD.2 g hg
  have a4 := T.ΓA_nonneg g hg
  have a5 := T.ΓA_nonneg _ hu
  filter_upwards [a1, a2, a3, a4, a5] with x e1 e2 e3 e4 e5
  have h0 : 0 ≤ G T g g x := e4
  have hW : 0 ≤ T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x := by
    have : 0 ≤ (n⁻¹).toReal * (T.L g x) ^ 2 := mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
    show 0 ≤ T.toDiffusionTriple.Γ₂ g g x - ρ * T.toDiffusionTriple.ΓA g g x
    linarith
  refine ⟨h0, ?_, ?_⟩
  · have e1' : G T (fun y => psiS ε (G T g g y)) (fun y => psiS ε (G T g g y)) x =
        deriv (psiS ε) (G T g g x) ^ 2 * G T (G T g g) (G T g g) x := e1
    rw [e1', deriv_psiS hε h0]
    set u := G T g g x
    set W := T.toDiffusionTriple.Γ₂ g g x - ρ * u
    have hS2 : Real.sqrt (u + ε ^ 2) ^ 2 = u + ε ^ 2 := Real.sq_sqrt (by positivity)
    have hSp : 0 < Real.sqrt (u + ε ^ 2) := Real.sqrt_pos.2 (by positivity)
    have : (1 / (2 * Real.sqrt (u + ε ^ 2))) ^ 2 = 1 / (4 * (u + ε ^ 2)) := by
      rw [div_pow, one_pow, mul_pow, hS2]; norm_num
    rw [this]
    have hY : G T (G T g g) (G T g g) x ≤ 4 * W * u := e2
    rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg hW (sq_nonneg ε), mul_nonneg hW h0]
  · rw [deriv2_psiS hε h0]
    set u := G T g g x
    set W := T.toDiffusionTriple.Γ₂ g g x - ρ * u
    set Y := G T (G T g g) (G T g g) x
    have hS2 : Real.sqrt (u + ε ^ 2) ^ 2 = u + ε ^ 2 := Real.sq_sqrt (by positivity)
    have hSp : ε ≤ Real.sqrt (u + ε ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
    set S := Real.sqrt (u + ε ^ 2)
    have hY : Y ≤ 4 * W * u := e2
    have hY0 : 0 ≤ Y := e5
    have habs : |(-1) / (4 * S ^ 3)| = 1 / (4 * S ^ 3) := by
      rw [abs_div, abs_neg, abs_one, abs_of_pos (by positivity)]
    rw [habs, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hε]
    have hu2 : u ≤ S ^ 2 := by nlinarith
    have h1 : Y * ε ≤ 4 * W * u * ε := by nlinarith
    have h3 : 4 * W * u * ε ≤ 4 * W * S ^ 2 * ε := by
      have := mul_le_mul_of_nonneg_left hu2 (by positivity : 0 ≤ 4 * W * ε)
      nlinarith
    have h4 : S ^ 2 * ε ≤ S ^ 3 := by
      have := mul_le_mul_of_nonneg_left hSp (sq_nonneg S)
      nlinarith
    have h5 : 4 * W * S ^ 2 * ε ≤ W * (4 * S ^ 3) := by
      have := mul_le_mul_of_nonneg_left h4 (by positivity : 0 ≤ 4 * W)
      nlinarith
    linarith


include hg hε in
lemma psiS_comp_mem : (fun x => psiS ε (G T g g x)) ∈ T.A := comp_mem_A T (psiS_smooth hε) (G_mem hg hg)

include hCD hg hg2 hu hε in
/-- **BGL Lemma 3.3.20** (p. 163): `G_ε = ψ_ε(Γ g) ∈ L²` and `[G_ε] ∈ 𝒟(ℰ)`. -/
theorem lemma3320 : ∃ hG2 : MemLp (fun x => psiS ε (G T g g x)) 2 T.μ,
    hG2.toLp _ ∈ T.formDomain := by
  obtain ⟨hΓi, hΓ₂i, -⟩ := integrable_Γ₂_of_domain hCD hg hg2 hu
  have hGA := psiS_comp_mem (T := T) (g := g) hg hε
  have hm : AEStronglyMeasurable (fun x => psiS ε (G T g g x)) T.μ :=
    (T.A_measurable _ hGA).aestronglyMeasurable
  have hG2 : MemLp (fun x => psiS ε (G T g g x)) 2 T.μ := by
    refine (memLp_two_iff_integrable_sq hm).2 ?_
    refine hΓi.mono' (hm.pow 2) ?_
    filter_upwards [T.ΓA_nonneg g hg] with x hx
    have := psiS_hH hε (le_refl (0 : ℝ)) (show 0 ≤ G T g g x from hx)
    rw [psiS_zero hε, sub_zero, sub_zero, abs_of_nonneg (show 0 ≤ G T g g x from hx)] at this
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact this
  refine ⟨hG2, mem_formDomain_of_ESA hGA hG2 ?_⟩
  obtain ⟨hWi, -⟩ := W_facts hCD hg hg2 hu
  refine hWi.mono' (T.A_measurable _ (G_mem hGA hGA)).aestronglyMeasurable ?_
  filter_upwards [pointwise_bounds hCD hg hε, T.ΓA_nonneg _ hGA] with x h1 h2
  rw [Real.norm_eq_abs, abs_of_nonneg h2]
  exact h1.2.1

include hCD hg hg2 hu hε in
/-- `L G_ε ∈ L¹` (given `L g ∈ 𝒟(ℰ)`). -/
theorem integrable_L_psi (hLg2 : MemLp (T.L g) 2 T.μ)
    (hQLg : hLg2.toLp (T.L g) ∈ T.formDomain) :
    Integrable (T.L (fun x => psiS ε (G T g g x))) T.μ := by
  obtain ⟨hΓi, hΓ₂i, -⟩ := integrable_Γ₂_of_domain hCD hg hg2 hu
  obtain ⟨hWi, -⟩ := W_facts hCD hg hg2 hu
  have hQg := ((DiffusionTriple.formData T.toDiffusionTriple).generator_mem_Q_and_form hu).1
  have hcross : Integrable (G T g (T.L g)) T.μ :=
    (L1.integrable_coeFn _).congr (gammaE_eq_ΓA hg hg2 hQg (T.L_mem_A g hg) hLg2 hQLg)
  have huA : G T g g ∈ T.A := G_mem hg hg
  have hL := L_comp T (psiS_smooth hε) huA
  have hmeas : AEStronglyMeasurable (T.L (fun x => psiS ε (G T g g x))) T.μ :=
    (T.A_measurable _ (T.L_mem_A _ (psiS_comp_mem (T := T) (g := g) hg hε))).aestronglyMeasurable
  have hbound : Integrable (fun x => (1 / (2 * ε)) * (2 * |T.toDiffusionTriple.Γ₂ g g x| +
      2 * |G T g (T.L g) x|) + (T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x) / ε) T.μ :=
    (((hΓ₂i.abs.const_mul 2).add (hcross.abs.const_mul 2)).const_mul (1 / (2 * ε))).add
      (hWi.div_const ε)
  refine hbound.mono' hmeas ?_
  filter_upwards [hL, pointwise_bounds hCD hg hε, T.ΓA_nonneg g hg, T.ΓA_nonneg _ huA] with x h1 h2 h3 h4
  have h0 : 0 ≤ G T g g x := h3
  have hLu := L_G_self T g x
  have hd1 := psiS_deriv_bound hε h0
  have hd2 := h2.2.2
  rw [Real.norm_eq_abs, h1, hLu]
  have e1 : |deriv (psiS ε) (G T g g x) * (2 * T.toDiffusionTriple.Γ₂ g g x + 2 * G T g (T.L g) x)| ≤
      (1 / (2 * ε)) * (2 * |T.toDiffusionTriple.Γ₂ g g x| + 2 * |G T g (T.L g) x|) := by
    rw [abs_mul]
    refine mul_le_mul hd1 ?_ (abs_nonneg _) (by positivity)
    calc |2 * T.toDiffusionTriple.Γ₂ g g x + 2 * G T g (T.L g) x|
        ≤ |2 * T.toDiffusionTriple.Γ₂ g g x| + |2 * G T g (T.L g) x| := abs_add_le _ _
      _ = _ := by rw [abs_mul, abs_mul]; norm_num
  have e2 : |deriv (deriv (psiS ε)) (G T g g x) * T.toDiffusionTriple.ΓA (G T g g) (G T g g) x| ≤
      (T.toDiffusionTriple.Γ₂ g g x - ρ * G T g g x) / ε := by
    have hY : 0 ≤ G T (G T g g) (G T g g) x := h4
    rw [abs_mul, abs_of_nonneg (show 0 ≤ T.toDiffusionTriple.ΓA (G T g g) (G T g g) x from hY)]
    exact hd2
  calc |deriv (psiS ε) (G T g g x) * (2 * T.toDiffusionTriple.Γ₂ g g x + 2 * G T g (T.L g) x) +
        deriv (deriv (psiS ε)) (G T g g x) * T.toDiffusionTriple.ΓA (G T g g) (G T g g) x|
      ≤ |deriv (psiS ε) (G T g g x) * (2 * T.toDiffusionTriple.Γ₂ g g x + 2 * G T g (T.L g) x)| +
        |deriv (deriv (psiS ε)) (G T g g x) * T.toDiffusionTriple.ΓA (G T g g) (G T g g) x| :=
        abs_add_le _ _
    _ ≤ _ := add_le_add e1 e2

end

end FullTriple

end MarkovTriple.BGL
