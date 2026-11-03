import Mathlib
import MarkovTriple.BGL.Theory.Interp.EntropyHelp
import MarkovTriple.BGL.Theory.LogSobolevDimChain

/-!
# Bounded elements of `𝒜` (BGL p. 272: "functions `f ∈ 𝒜` which are bounded, together with `Γ(f)` and `Lf`")

`Bdd T h`: `h ∈ 𝒜`, `|h|`, `Γ(h)`, `|L h|` essentially bounded.  Finite measure, `CD(ρ,n)`:
* `Bdd.domain` (BGL Prop. 3.3.6 (i), "such functions belong to `𝒟(L)`");
* `Bdd.integrable_Γ₂` (Prop. 3.3.17 second paragraph / Lemma 3.3.16), `Bdd.integrable_ΓΓ`
  (via the reinforced inequality (3.3.6): `Γ(Γ h) ≤ 4(Γ₂(h) - ρΓ(h))Γ(h)`);
* `Bdd.comp`: stability under smooth post-composition.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

/-- Bounded elements of `𝒜`: `h ∈ 𝒜`, `|h| ≤ K`, `Γ(h) ≤ B`, `|L h| ≤ B` a.e. -/
def Bdd (T : FullTriple E) (h : E → ℝ) : Prop :=
  h ∈ T.A ∧ ∃ K B : ℝ, (∀ᵐ x ∂T.μ, |h x| ≤ K) ∧ (∀ᵐ x ∂T.μ, G T h h x ≤ B) ∧
    ∀ᵐ x ∂T.μ, |T.L h x| ≤ B

variable {T : FullTriple E}

lemma intB [IsFiniteMeasure T.μ] {φ : E → ℝ} (hm : Measurable φ) {C : ℝ}
    (hC : ∀ᵐ x ∂T.μ, |φ x| ≤ C) : Integrable φ T.μ :=
  Integrable.of_bound hm.aestronglyMeasurable C (hC.mono fun x hx => by rwa [Real.norm_eq_abs])

namespace Bdd

variable {h : E → ℝ}

lemma memA (hb : Bdd T h) : h ∈ T.A := hb.1

lemma memLp2 [IsFiniteMeasure T.μ] (hb : Bdd T h) : MemLp h 2 T.μ := by
  obtain ⟨hA, K, -, hK, -⟩ := hb
  exact memLp_of_bdd hA hK

lemma memLpL [IsFiniteMeasure T.μ] (hb : Bdd T h) : MemLp (T.L h) 2 T.μ := by
  obtain ⟨hA, -, B, -, -, hL⟩ := hb
  exact memLp_of_bdd (L_memA hA) hL

lemma integrable_Γ [IsFiniteMeasure T.μ] (hb : Bdd T h) : Integrable (G T h h) T.μ := by
  obtain ⟨hA, -, B, -, hΓ, -⟩ := hb
  refine intB (T.A_measurable _ (G_mem hA hA)) (C := |B|) ?_
  filter_upwards [hΓ, T.ΓA_nonneg h hA] with x h1 h2
  have : 0 ≤ G T h h x := h2
  rw [abs_of_nonneg this]
  exact h1.trans (le_abs_self _)

/-- BGL Prop. 3.3.6 (i): `[h] ∈ 𝒟(L)`. -/
lemma domain [IsFiniteMeasure T.μ] (hb : Bdd T h) :
    hb.memLp2.toLp h ∈ T.toDiffusionTriple.generator.domain :=
  (mem_domain_of_ESA hb.memA hb.memLp2 hb.memLpL).1

lemma integrable_Γ₂ [IsFiniteMeasure T.μ] {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hb : Bdd T h) :
    Integrable (T.toDiffusionTriple.Γ₂ h h) T.μ :=
  (integrable_Γ₂_of_domain hCD hb.memA hb.memLp2 hb.domain).2.1

/-- `Γ(Γ h) ∈ L¹`, from the reinforced inequality (3.3.6). -/
lemma integrable_ΓΓ [IsFiniteMeasure T.μ] {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hb : Bdd T h) :
    Integrable (G T (G T h h) (G T h h)) T.μ := by
  have hA := hb.memA
  have i2 := hb.integrable_Γ₂ hCD
  have i1 := hb.integrable_Γ
  obtain ⟨-, -, B, -, hΓ, -⟩ := hb
  have hu : G T h h ∈ T.A := G_mem hA hA
  refine ((i2.norm.add (i1.norm.const_mul |ρ|)).const_mul (4 * |B|)).mono'
    (T.A_measurable _ (G_mem hu hu)).aestronglyMeasurable ?_
  filter_upwards [reinforced_cd hCD hA, hΓ, T.ΓA_nonneg h hA,
    T.ΓA_nonneg _ hu] with x h1 h2 h3 h4
  have h3' : 0 ≤ G T h h x := h3
  have h4' : 0 ≤ G T (G T h h) (G T h h) x := h4
  rw [Real.norm_eq_abs, abs_of_nonneg h4']
  refine h1.trans ?_
  have hB : G T h h x ≤ |B| := h2.trans (le_abs_self _)
  have e1 : T.toDiffusionTriple.Γ₂ h h x - ρ * G T h h x ≤
      ‖T.toDiffusionTriple.Γ₂ h h x‖ + |ρ| * ‖G T h h x‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h3']
    have := le_abs_self (T.toDiffusionTriple.Γ₂ h h x)
    have := neg_abs_le ρ
    nlinarith [abs_nonneg ρ]
  have e2 : 0 ≤ ‖T.toDiffusionTriple.Γ₂ h h x‖ + |ρ| * ‖G T h h x‖ := by positivity
  calc 4 * (T.toDiffusionTriple.Γ₂ h h x - ρ * G T h h x) * G T h h x
      ≤ 4 * (‖T.toDiffusionTriple.Γ₂ h h x‖ + |ρ| * ‖G T h h x‖) * |B| := by
        have := mul_le_mul e1 hB h3' e2
        nlinarith [this]
    _ = _ := by simp only [Pi.add_apply]; ring

/-- stability under smooth post-composition. -/
theorem comp {ψ : ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hb : Bdd T h) :
    Bdd T (fun x => ψ (h x)) := by
  obtain ⟨hA, K, B, hK, hΓ, hL⟩ := hb
  have hψ1 : ContDiff ℝ (⊤ : ℕ∞) (deriv ψ) := (contDiff_infty_iff_deriv.1 hψ).2
  have hψ2 : ContDiff ℝ (⊤ : ℕ∞) (deriv (deriv ψ)) := (contDiff_infty_iff_deriv.1 hψ1).2
  obtain ⟨C0, hC0⟩ := (isCompact_Icc (a := -K) (b := K)).exists_bound_of_continuousOn
    hψ.continuous.continuousOn
  obtain ⟨C1, hC1⟩ := (isCompact_Icc (a := -K) (b := K)).exists_bound_of_continuousOn
    hψ1.continuous.continuousOn
  obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := -K) (b := K)).exists_bound_of_continuousOn
    hψ2.continuous.continuousOn
  refine ⟨comp_mem_A T hψ hA, C0, max (C1 ^ 2 * B) (C1 * B + C2 * B), ?_, ?_, ?_⟩
  · filter_upwards [hK] with x hx
    have := hC0 (h x) (abs_le.1 hx |> fun p => ⟨p.1, p.2⟩)
    rwa [Real.norm_eq_abs] at this
  · filter_upwards [hΓ, T.ΓA_nonneg h hA, ΓA_comp_comp T hψ hA, hK] with x h1 h2 h3 h4
    have h2' : 0 ≤ G T h h x := h2
    have hx := abs_le.1 h4
    have c1 := hC1 (h x) ⟨hx.1, hx.2⟩
    rw [Real.norm_eq_abs] at c1
    have h3' : G T (fun x => ψ (h x)) (fun x => ψ (h x)) x = deriv ψ (h x) ^ 2 * G T h h x := h3
    rw [h3']
    refine le_trans ?_ (le_max_left _ _)
    have : deriv ψ (h x) ^ 2 ≤ C1 ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) c1 2
    nlinarith [mul_le_mul this h1 h2' (sq_nonneg C1)]
  · filter_upwards [hL, hΓ, T.ΓA_nonneg h hA, L_comp T hψ hA, hK] with x h1 h2 h3 h4 h5
    have h3' : 0 ≤ G T h h x := h3
    have hx := abs_le.1 h5
    have c1 := hC1 (h x) ⟨hx.1, hx.2⟩
    have c2 := hC2 (h x) ⟨hx.1, hx.2⟩
    rw [Real.norm_eq_abs] at c1 c2
    have h4' : T.L (fun x => ψ (h x)) x = deriv ψ (h x) * T.L h x +
        deriv (deriv ψ) (h x) * G T h h x := h4
    rw [h4']
    refine le_trans ?_ (le_max_right _ _)
    have hB : 0 ≤ B := (abs_nonneg _).trans h1
    calc |deriv ψ (h x) * T.L h x + deriv (deriv ψ) (h x) * G T h h x|
        ≤ |deriv ψ (h x)| * |T.L h x| + |deriv (deriv ψ) (h x)| * G T h h x := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg h3']
      _ ≤ C1 * B + C2 * B := by
          have hC1' : 0 ≤ C1 := (abs_nonneg _).trans c1
          have hC2' : 0 ≤ C2 := (abs_nonneg _).trans c2
          have e1 := mul_le_mul c1 h1 (abs_nonneg _) hC1'
          have e2 := mul_le_mul c2 h2 h3' hC2'
          linarith

end Bdd

end FullTriple

end MarkovTriple.BGL
