import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllDiff

/-!
# Direct converse of BGL Prop. 3.3.17 for `EllData d`: completeness cut-offs and Fatou (R20, Stream D2)

Statements: `STATEMENTS_R20_DirectEll.md` (D1).

## DIFFERENCE FROM BGL

*BGL* proves the converse of Prop. 3.3.17 (p. 161-162) through a density statement for `(L² + Id)𝒜₀` (`Core2`, ERRATA R15-1),
which R17-R19 could establish only under growth conditions (`CoreCut`: bounded `Γχ, Lχ, L²χ, Γ(Lχ), Γ₂(χ)` for the cut-offs).
*Here* (Stream D2) we avoid `Core2` altogether and follow instead the cut-off (Caccioppoli) technique of BGL Prop. 3.2.1 (p. 142)
applied to `Γ₂`.  This file only needs the cheapest cut-off family: the completeness cut-offs of BGL Def. 3.3.9, i.e. the ones
produced by the field `a_exh` of `EllData` (`diff_isComplete`, `ζ_k = s(2 − ψ/R_k)`), of which only
`0 ≤ χ ≤ 1`, compact support, `Γ(χ) ≤ 1` and `χ_n → 1` a.e. are used.  No bound on `Lχ`, `Γ₂(χ)`, ... is required, which is
what makes the argument work for the hyperbolic plane (no `CoreCut`).

* `ae_le_cont`: an a.e. inequality between continuous functions holds everywhere (`μ` open-positive);
* `EllData.GradCutFamily`, `EllData.exists_gradCut`: the cut-off sequence, from `diff_isComplete`;
* `integrable_of_cut_ae`: Fatou, a continuous `g ≥ 0` whose cut-off integrals are bounded is integrable (a.e. convergence).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

/-- an a.e. inequality between continuous real functions on `ℝ^d` holds everywhere, for an open-positive measure -/
lemma ae_le_cont {μ : Measure (Rd d)} [μ.IsOpenPosMeasure] {f g : Rd d → ℝ} (hf : Continuous f)
    (hg : Continuous g) (h : f ≤ᵐ[μ] g) : ∀ x, f x ≤ g x := by
  intro x
  have h1 : min f g =ᵐ[μ] f := by
    filter_upwards [h] with y hy
    exact min_eq_left hy
  have h2 := (Continuous.ae_eq_iff_eq μ (hf.min hg) hf).1 h1
  have h3 := congrFun h2 x
  exact min_eq_left_iff.1 h3

/-- **Fatou**: a continuous `g ≥ 0` with `∫ φ_n g ≤ B` for continuous compactly supported `0 ≤ φ_n → 1` a.e. is integrable. -/
lemma integrable_of_cut_ae {μ : Measure (Rd d)} [IsFiniteMeasure μ] {φ : ℕ → Rd d → ℝ} {g : Rd d → ℝ}
    (hg : Continuous g) (hg0 : ∀ x, 0 ≤ g x) (hφc : ∀ n, Continuous (φ n)) (hφ0 : ∀ n x, 0 ≤ φ n x)
    (hcs : ∀ n, HasCompactSupport (φ n)) (hev : ∀ᵐ x ∂μ, Tendsto (fun n => φ n x) atTop (𝓝 1)) {B : ℝ}
    (hB : ∀ n, ∫ x, φ n x * g x ∂μ ≤ B) : Integrable g μ := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => hg0 x)]
  have hc : ∀ n, Continuous (fun x => φ n x * g x) := fun n => (hφc n).mul hg
  have hint : ∀ n, Integrable (fun x => φ n x * g x) μ := fun n =>
    (hc n).integrable_of_hasCompactSupport (hcs n).mul_right
  set F : ℕ → Rd d → ENNReal := fun n x => ENNReal.ofReal (φ n x * g x) with hF
  have hFm : ∀ n, Measurable (F n) := fun n => ENNReal.measurable_ofReal.comp (hc n).measurable
  have hlim : ∀ᵐ x ∂μ, liminf (fun n => F n x) atTop = ENNReal.ofReal (g x) := by
    filter_upwards [hev] with x hx
    have : Tendsto (fun n => F n x) atTop (𝓝 (ENNReal.ofReal (g x))) := by
      have := ENNReal.tendsto_ofReal (hx.mul_const (g x))
      simpa [hF] using this
    exact this.liminf_eq
  have h1 := lintegral_liminf_le (μ := μ) (u := (atTop : Filter ℕ)) hFm
  rw [lintegral_congr_ae hlim] at h1
  refine lt_of_le_of_lt h1 ?_
  have h2 : ∀ n, ∫⁻ x, F n x ∂μ ≤ ENNReal.ofReal B := fun n => by
    simp only [hF]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (Eventually.of_forall fun x => mul_nonneg (hφ0 n x) (hg0 x))]
    exact ENNReal.ofReal_le_ofReal (hB n)
  have h3 : liminf (fun n : ℕ => ∫⁻ x, F n x ∂μ) atTop ≤ ENNReal.ofReal B :=
    liminf_le_of_frequently_le' (Frequently.of_forall h2)
  exact lt_of_le_of_lt h3 ENNReal.ofReal_lt_top

namespace EllData
variable (E : EllData d)

/-- **gradient-bounded cut-offs** (BGL Def. 3.3.9): smooth, compactly supported, `0 ≤ χ_n ≤ 1`, `Γ(χ_n) ≤ 1` everywhere,
`χ_n → 1` `μ`-a.e.  Nothing is assumed on `Lχ_n`, `Γ₂(χ_n)`, ... (contrast `CutFamily`). -/
structure GradCutFamily (E : EllData d) (χ : ℕ → Rd d → ℝ) : Prop where
  smooth : ∀ n, Sm (χ n)
  cs : ∀ n, HasCompactSupport (χ n)
  mem : ∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1
  grad : ∀ n x, E.Γ (χ n) (χ n) x ≤ 1
  tendsto : ∀ᵐ x ∂E.μ, Tendsto (fun n => χ n x) atTop (𝓝 1)

/-- **D1**: the completeness of `E` (`a_exh`, `diff_isComplete`) yields a gradient-bounded cut-off family. -/
theorem exists_gradCut : ∃ χ : ℕ → Rd d → ℝ, E.GradCutFamily χ := by
  obtain ⟨ζ, hmem, h0, hmono, hlim, hΓ⟩ := E.diff_isComplete
  have hsm : ∀ n, Sm (ζ n) := fun n => (hmem n).1
  have hcont : ∀ n, Continuous (ζ n) := fun n => (hsm n).continuous
  have hnn : ∀ n x, 0 ≤ ζ n x := fun n =>
    ae_le_cont (μ := E.μ) (f := fun _ => (0 : ℝ)) continuous_const (hcont n) (h0 n)
  have hle1 : ∀ n x, ζ n x ≤ 1 := by
    intro n
    have hall : ∀ᵐ x ∂E.μ, (∀ k, ζ k x ≤ ζ (k + 1) x) ∧ Tendsto (fun k => ζ k x) atTop (𝓝 1) := by
      filter_upwards [ae_all_iff.2 hmono, hlim] with x h1 h2
      exact ⟨h1, h2⟩
    have : ζ n ≤ᵐ[E.μ] fun _ => (1 : ℝ) := by
      filter_upwards [hall] with x hx
      exact (monotone_nat_of_le_succ hx.1).ge_of_tendsto hx.2 n
    exact ae_le_cont (μ := E.μ) (hcont n) continuous_const this
  have hG : ∀ n x, E.Γ (ζ n) (ζ n) x ≤ 1 := by
    intro n
    have h : E.Γ (ζ n) (ζ n) ≤ᵐ[E.μ] fun _ => (1 : ℝ) := by
      filter_upwards [hΓ n] with x hx
      refine hx.trans ?_
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      exact pow_le_one₀ (by positivity) h1
    exact ae_le_cont (μ := E.μ) (E.sm_Γ (hsm n) (hsm n)).continuous continuous_const h
  exact ⟨ζ, ⟨hsm, fun n => (hmem n).2, fun n x => ⟨hnn n x, hle1 n x⟩, hG, hlim⟩⟩

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
