import Mathlib
import MarkovTriple.BGL.Theory.Compact.Entropy
import MarkovTriple.BGL.Theory.LogSobolevMain
import MarkovTriple.BGL.Instances.Circle.Triple

/-!
# Unconditional consequences on compact triples (and on the circle)

With `compact_gradientInterpolation` and `compact_entropyInterpolation` the conditional theorems of
`GradientBound.lean`, `LogSobolev.lean`, `LogSobolevMain.lean` become unconditional for every
`CompactTriple`:

* `compact_gradient_bound`: `CD(ρ,n) ⇒ Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)` (in `Compact/Gradient.lean`);
* `compact_logSobolev`: `CD(ρ,n)`, `ρ > 0` ⇒ `LS(1/ρ, 0)` (log-Sobolev, Prop. 5.7.1);
* `compact_fisher_decay`, `compact_fisher_antitone`: along the heat flow `e' = -I` and
  `I(s) ≤ e^{-2ρ s} I(0)`, `I` nonincreasing for `ρ ≥ 0`;

and for the circle (`CD(0,∞)`): `circle_gradient_bound` (`Γ(P_t f) ≤ P_t Γ(f)`),
`circle_entropy_decay`, `circle_fisher_antitone`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

/-- **Log-Sobolev inequality on every compact triple** with `CD(ρ,n)`, `ρ > 0`. -/
theorem compact_logSobolev (C : CompactTriple E) {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ)
    (hCD : C.toFullTriple.CD ρ n) : C.toDiffusionTriple.LS (1 / ρ) 0 :=
  FullTriple.logSobolev_of_CD_infty C.toFullTriple C.entropyInterpolation hρ hCD

namespace CompactTriple

variable (C : CompactTriple E)

/-- the derivative of the Fisher information along the flow is `≤ -2ρ I`. -/
theorem fisher_deriv_le {ρ : ℝ} {n : ℝ≥0∞} (hCD : C.toFullTriple.CD ρ n) (φ : C.A₀)
    (h0 : 0 ≤ᵐ[C.μ] φ.1) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : 0 < s) :
    ∃ q', HasDerivAt (C.toFullTriple.entI φ ε) q' s ∧
      q' ≤ -2 * ρ * C.toFullTriple.entI φ ε s := by
  obtain ⟨M, hM, hφ, ⟨K⟩⟩ := C.exists_data φ hε
  refine ⟨_, C.entI_hasDerivAt φ hε hM h0 hφ K hs, ?_⟩
  obtain ⟨i1, i2⟩ := C.entJ_integrable φ hε hM h0 hφ K s
  have hAg := C.entG_mem φ ε s
  have hΛA := C.comp_mem_A K.hΛ (C.A₀_le _ hAg)
  have hcd := hCD.2 _ hΛA
  have hint : ρ * ∫ x, C.toFullTriple.entG φ ε s x * C.toDiffusionTriple.ΓA
      (fun y => K.Λ (C.toFullTriple.entG φ ε s y))
      (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) x ∂C.μ ≤ C.toFullTriple.entJ K.Λ φ ε s := by
    rw [← integral_const_mul]
    refine integral_mono_ae (i2.const_mul ρ) i1 ?_
    filter_upwards [FullTriple.entG_range C.toFullTriple φ hε hM h0 hφ s, hcd] with x hx h2
    have hpos : 0 < C.toFullTriple.entG φ ε s x := lt_of_lt_of_le hε hx.1
    have : 0 ≤ (n⁻¹).toReal * (C.L (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) x) ^ 2 :=
      mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
    have h3 : ρ * C.toDiffusionTriple.ΓA (fun y => K.Λ (C.toFullTriple.entG φ ε s y))
        (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) x ≤ C.toDiffusionTriple.Γ₂
        (fun y => K.Λ (C.toFullTriple.entG φ ε s y))
        (fun y => K.Λ (C.toFullTriple.entG φ ε s y)) x := by linarith
    calc ρ * (C.toFullTriple.entG φ ε s x * _) = C.toFullTriple.entG φ ε s x * (ρ * _) := by ring
      _ ≤ C.toFullTriple.entG φ ε s x * _ := mul_le_mul_of_nonneg_left h3 hpos.le
  rw [← FullTriple.entI_eq C.toFullTriple φ hε hM h0 hφ K s] at hint
  linarith

/-- **Decay of the Fisher information** along the heat flow (compact triple, `CD(ρ,n)`, any `ρ ∈ ℝ`):
`I(s) ≤ e^{-2ρ s} I(0)`; here `e' = -I` is `compact_entropyInterpolation.hasDerivAt_E`. -/
theorem fisher_decay {ρ : ℝ} {n : ℝ≥0∞} (hCD : C.toFullTriple.CD ρ n) (φ : C.A₀)
    (h0 : 0 ≤ᵐ[C.μ] φ.1) {ε : ℝ} (hε : 0 < ε) {s : ℝ} (hs : 0 ≤ s) :
    C.toFullTriple.entI φ ε s ≤
      Real.exp (-2 * ρ * s) * C.toFullTriple.entI φ ε 0 := by
  have h := BE.fisher_decay (q := fun s => -C.toFullTriple.entI φ ε s) (ρ := ρ)
    ((C.entropyInterpolation.continuousOn_I φ ε hε h0).neg)
    (fun s hs => by
      obtain ⟨q', hq', hle⟩ := C.fisher_deriv_le hCD φ h0 hε hs
      exact ⟨-q', hq'.neg, by linarith⟩) s hs
  simpa using h

/-- the Fisher information is nonnegative. -/
lemma entI_nonneg (φ : C.A₀) (h0 : 0 ≤ᵐ[C.μ] φ.1) {ε : ℝ} (hε : 0 < ε) (s : ℝ) :
    0 ≤ C.toFullTriple.entI φ ε s := by
  obtain ⟨M, hM, hφ, ⟨K⟩⟩ := C.exists_data φ hε
  unfold FullTriple.entI
  refine integral_nonneg_of_ae ?_
  have hgA := C.A₀_le _ (C.entG_mem φ ε s)
  filter_upwards [FullTriple.entG_range C.toFullTriple φ hε hM h0 hφ s,
    C.toFullTriple.ΓA_nonneg _ hgA] with x hx h2
  exact div_nonneg h2 (by linarith [hx.1])

/-- **The Fisher information is nonincreasing** along the heat flow when `CD(ρ,n)`, `ρ ≥ 0`
(in particular on the circle). -/
theorem fisher_antitone {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 ≤ ρ) (hCD : C.toFullTriple.CD ρ n) (φ : C.A₀)
    (h0 : 0 ≤ᵐ[C.μ] φ.1) {ε : ℝ} (hε : 0 < ε) :
    AntitoneOn (C.toFullTriple.entI φ ε) (Ici 0) := by
  refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
    (C.entropyInterpolation.continuousOn_I φ ε hε h0) ?_ ?_
  · intro s hs
    rw [interior_Ici] at hs
    obtain ⟨q', hq', _⟩ := C.fisher_deriv_le hCD φ h0 hε hs
    exact hq'.differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    obtain ⟨q', hq', hle⟩ := C.fisher_deriv_le hCD φ h0 hε hs
    rw [hq'.deriv]
    have := C.entI_nonneg φ h0 hε s
    nlinarith

end CompactTriple

namespace Circle

/-- **Gradient bound on the circle**: `Γ(P_t f) ≤ P_t Γ(f)` a.e. (`CD(0,∞)`; BGL Cor. 3.3.19, `ρ = 0`),
unconditional. -/
theorem circle_gradient_bound (f : circleCompact.A₀) (t : ℝ≥0) :
    circleCompact.toDiffusionTriple.ΓA (circleCompact.Pt t f) (circleCompact.Pt t f) ≤ᵐ[circleCompact.μ]
      fun x => (circleCompact.toDiffusionTriple.semigroup t
        (circleCompact.toDiffusionTriple.cls ⟨circleCompact.toDiffusionTriple.ΓA f.1 f.1,
          circleCompact.ΓA_self_mem_A₀ f.2⟩) : Lp ℝ 2 circleCompact.μ) x := by
  have h := compact_gradient_bound circleCompact circle_CD_zero_top f t
  simpa using h

/-- **Entropy dissipation on the circle**: for `φ ∈ 𝒜₀`, `φ ≥ 0`, `ε > 0`: `e' = -I` on `(0,∞)`. -/
theorem circle_entropy_deriv (φ : circleCompact.A₀) (h0 : 0 ≤ᵐ[circleCompact.μ] φ.1) {ε : ℝ}
    (hε : 0 < ε) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (circleCompact.toFullTriple.entE φ ε) (-circleCompact.toFullTriple.entI φ ε s) s :=
  circleCompact.entropyInterpolation.hasDerivAt_E φ ε hε h0 s hs

/-- **`I' ≤ 0` on the circle**: the Fisher information is nonincreasing along the heat flow. -/
theorem circle_fisher_antitone (φ : circleCompact.A₀) (h0 : 0 ≤ᵐ[circleCompact.μ] φ.1) {ε : ℝ}
    (hε : 0 < ε) : AntitoneOn (circleCompact.toFullTriple.entI φ ε) (Ici 0) :=
  circleCompact.fisher_antitone le_rfl circle_CD_zero_top φ h0 hε

end Circle

end MarkovTriple.BGL
