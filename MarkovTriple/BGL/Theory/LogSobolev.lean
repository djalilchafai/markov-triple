import Mathlib
import MarkovTriple.BGL.Theory.GammaCalculus
import MarkovTriple.BGL.Theory.Gamma2Integral
import MarkovTriple.BGL.Theory.ESAOne
import MarkovTriple.BGL.Theory.Poincare
import MarkovTriple.BGL.Frozen.LSI
import MarkovTriple.BGL.Frozen.Ent
import MarkovTriple.BGL.Calculus.LSIExtend
import MarkovTriple.BGL.Analysis.BE.Gronwall
import MarkovTriple.BGL.Analysis.BE.Cut
import MarkovTriple.BGL.Analysis.BE.EntLimit

/-!
# Logarithmic Sobolev inequality from `CD(ρ,∞)` (BGL Prop. 5.7.1, Thm 5.7.4 with `n = ∞`)

**Status: conditional on the explicit hypothesis `EntropyInterpolation T`** (G3 of `Theory/GAPS.md`).

Route (BGL §5.7, proof of Prop. 5.7.1; de Bruijn identity, Prop. 5.5.3, plus the second derivative
`Φ'' = 2∫ P_t f Γ₂(log P_t f)`): for `φ ∈ 𝒜₀`, `φ ≥ 0`, `ε > 0`, `g_s = ε + P_s φ` (`≥ ε`, bounded
by `ε + M`), `e(s) = ∫ g_s log g_s`, `I(s) = ∫ Γ(g_s)/g_s`:

* `e' = -I`, `I' = -2 ∫ g_s Γ₂(log g_s)` (hypothesis, regularity),
* `CD(ρ,∞)` applied to `log g_s ∈ 𝒜` (F3, via a smooth cutoff) gives `I' ≤ -2ρ I`, i.e. `I(s) ≤ e^{-2ρ s} I(0)`
  (proved here: the real-variable lemma `BE.fisher_decay`),
* `e(s) → m log m` as `s → ∞` (PROVED from the Poincaré inequality / spectral gap:
  `Theory/Convergence.lean`, `tendsto_entE`),
* hence `Ent(ε + φ) = e(0) - m log m = ∫_0^∞ I ≤ I(0)/(2ρ)` (`ent_le_fisher`),
* `φ = f²`, `Γ(f²) = 4f²Γ(f)` (F6, proved) and `ε → 0` (`BE.tendsto_Ent_add`) give
  `Ent(f²) ≤ (2/ρ) ℰ(f)`, i.e. `LS(1/ρ, 0)` on `𝒜₀` (`logSobolev_of_CD_infty`), and then on `𝒟(ℰ)`
  (`DiffusionTriple.LS.extend`).

Everything except the four regularity items of `EntropyInterpolation` is proved from F1–F10.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- `0 ≤ φ ≤ M` ⇒ `0 ≤ P_t φ ≤ M` (positivity and sub-Markov property of the semigroup). -/
theorem Pt_le (φ : T.A₀) {M : ℝ} (hM : 0 < M) (hφ : ∀ x, φ.1 x ≤ M) (t : ℝ≥0) :
    T.Pt t φ ≤ᵐ[T.μ] fun _ => M := by
  have hu : ((M⁻¹ • T.toDiffusionTriple.cls φ : Lp ℝ 2 T.μ) : E → ℝ) ≤ᵐ[T.μ] (1 : E → ℝ) := by
    filter_upwards [Lp.coeFn_smul M⁻¹ (T.toDiffusionTriple.cls φ),
    DiffusionTriple.coeFn_cls T.toDiffusionTriple φ] with x h1 h2
    rw [h1, Pi.smul_apply, h2, smul_eq_mul]
    have := hφ x
    rw [inv_mul_le_iff₀ hM]; simpa using this
  have h := T.toDiffusionTriple.semigroup_le_one t _ hu
  rw [map_smul] at h
  filter_upwards [h, Lp.coeFn_smul M⁻¹ (T.toDiffusionTriple.semigroup t (T.toDiffusionTriple.cls φ)),
    T.Pt_ae t φ] with x h1 h2 h3
  rw [h2, Pi.smul_apply, smul_eq_mul, h3] at h1
  rw [inv_mul_le_iff₀ hM] at h1
  simpa using h1

/-- the shifted function `g_s = ε + P_s φ` of the entropy interpolation. -/
noncomputable def entG (φ : T.A₀) (ε s : ℝ) : E → ℝ := fun x => ε + T.Pt s.toNNReal φ x

/-- `e(s) = ∫ g_s log g_s`. -/
noncomputable def entE (φ : T.A₀) (ε s : ℝ) : ℝ :=
  ∫ x, T.entG φ ε s x * Real.log (T.entG φ ε s x) ∂T.μ

/-- `I(s) = ∫ Γ(g_s)/g_s` (Fisher information of `g_s`). -/
noncomputable def entI (φ : T.A₀) (ε s : ℝ) : ℝ :=
  ∫ x, T.toDiffusionTriple.ΓA (T.entG φ ε s) (T.entG φ ε s) x / T.entG φ ε s x ∂T.μ

/-- `J_Λ(s) = ∫ g_s Γ₂(Λ∘g_s)` (`Λ` a smooth cutoff of `log`). -/
noncomputable def entJ (Λ : ℝ → ℝ) (φ : T.A₀) (ε s : ℝ) : ℝ :=
  ∫ x, T.entG φ ε s x * T.toDiffusionTriple.Γ₂ (fun y => Λ (T.entG φ ε s y))
    (fun y => Λ (T.entG φ ε s y)) x ∂T.μ

/-- **Regularity hypothesis of the entropy interpolation (G3 of `GAPS.md`).**  For `φ ∈ 𝒜₀`,
`0 ≤ φ ≤ M`, `ε > 0` (writing `g_s = ε + P_s φ`, `e(s) = ∫ g_s log g_s`, `I(s) = ∫ Γ(g_s)/g_s`):

* `e`, `I` are continuous on `[0,∞)`;
* `e' = -I` on `(0,∞)` (de Bruijn);
* for every smooth cutoff `Λ` of `log` on `[ε, ε+M]` (`BE.Cut`): `g_s Γ₂(Λ∘g_s)`, `g_s Γ(Λ∘g_s)` are
  integrable and `I' = -2 ∫ g_s Γ₂(Λ∘g_s)` on `(0,∞)`;

This is the analytic content of the book's "analysis of Sect. 3.3 indicates that for `t > 0`, `P_t f` is
in `𝒜` and bounded together with `Γ(P_t f)` and `L P_t f`" (§5.7) together with the differentiation
under the integral sign of Prop. 5.5.3.  It is NOT derived from F1–F10 here; it is a hypothesis. -/
structure EntropyInterpolation : Prop where
  continuousOn_E : ∀ (φ : T.A₀) (ε : ℝ), 0 < ε → 0 ≤ᵐ[T.μ] φ.1 →
    ContinuousOn (T.entE φ ε) (Ici 0)
  continuousOn_I : ∀ (φ : T.A₀) (ε : ℝ), 0 < ε → 0 ≤ᵐ[T.μ] φ.1 →
    ContinuousOn (T.entI φ ε) (Ici 0)
  hasDerivAt_E : ∀ (φ : T.A₀) (ε : ℝ), 0 < ε → 0 ≤ᵐ[T.μ] φ.1 → ∀ s : ℝ, 0 < s →
    HasDerivAt (T.entE φ ε) (-T.entI φ ε s) s
  hasDerivAt_I : ∀ (φ : T.A₀) (ε : ℝ) (M : ℝ), 0 < ε → 0 < M → 0 ≤ᵐ[T.μ] φ.1 →
    (∀ x, φ.1 x ≤ M) → ∀ C : BE.Cut ε M, ∀ s : ℝ, 0 < s →
    Integrable (fun x => T.entG φ ε s x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (T.entG φ ε s y))
      (fun y => C.Λ (T.entG φ ε s y)) x) T.μ ∧
    Integrable (fun x => T.entG φ ε s x * T.toDiffusionTriple.ΓA (fun y => C.Λ (T.entG φ ε s y))
      (fun y => C.Λ (T.entG φ ε s y)) x) T.μ ∧
    HasDerivAt (T.entI φ ε) (-2 * T.entJ C.Λ φ ε s) s

lemma entG_mem_A (φ : T.A₀) (ε s : ℝ) : T.entG φ ε s ∈ T.A :=
  T.A.add_mem (const_mem_A T ε) (T.Pt_mem_A _ φ)

lemma entG_range (φ : T.A₀) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[T.μ] φ.1)
    (hφ : ∀ x, φ.1 x ≤ M) (s : ℝ) :
    ∀ᵐ x ∂T.μ, T.entG φ ε s x ∈ Icc ε (ε + M) := by
  filter_upwards [T.Pt_nonneg s.toNNReal φ h0, T.Pt_le φ hM hφ s.toNNReal] with x h1 h2
  simp only [Pi.zero_apply] at h1
  exact ⟨by simp only [entG]; linarith, by simp only [entG]; linarith⟩

/-- `I(s) = ∫ g_s Γ(Λ∘g_s)` for a cutoff `Λ` of `log`. -/
lemma entI_eq (φ : T.A₀) {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) (h0 : 0 ≤ᵐ[T.μ] φ.1)
    (hφ : ∀ x, φ.1 x ≤ M) (C : BE.Cut ε M) (s : ℝ) :
    T.entI φ ε s = ∫ x, T.entG φ ε s x * T.toDiffusionTriple.ΓA (fun y => C.Λ (T.entG φ ε s y))
      (fun y => C.Λ (T.entG φ ε s y)) x ∂T.μ := by
  unfold entI
  refine integral_congr_ae ?_
  filter_upwards [entG_range T φ hε hM h0 hφ s,
    ΓA_comp_comp T C.hΛ (entG_mem_A T φ ε s)] with x hx hx2
  rw [hx2, C.deriv_Λ_eq hε hx]
  have hpos : 0 < T.entG φ ε s x := lt_of_lt_of_le hε hx.1
  field_simp

end FullTriple

end MarkovTriple.BGL
