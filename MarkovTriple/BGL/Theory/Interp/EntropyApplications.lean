import Mathlib
import MarkovTriple.BGL.Theory.Interp.EntropyMain
import MarkovTriple.BGL.Theory.LogSobolevDim
import MarkovTriple.BGL.Instances.Gibbs.InterpMain

/-!
# Consequences of `FullTriple.entropyInterpolation` (BGL Prop. 5.7.1, Thm 5.7.4)

* `FullTriple.logSobolev_unconditional`: every `FullTriple` with probability measure and `CD(ρ,n)`, `ρ > 0`
  satisfies `LS(1/ρ, 0)` (`Ent(f²) ≤ (2/ρ) ℰ(f)` on `𝒜₀`) — no hypothesis other than `CD`;
* `FullTriple.logSobolev_domain_unconditional`: the same on the whole Dirichlet domain;
* `GibbsData.gibbsFull_logSobolev_unconditional`: the Gibbs measure `e^{-V}dx`, `V'' ≥ ρ > 0`;
* `FullTriple.finiteDim_bdd`: the field `bdd` (BGL p. 270) of `FiniteDimInterpolation` is a theorem
  (`CD(ρ,n)`, `ρ ≥ 0`);
* `FullTriple.finiteDimInterpolation_of_ext`, `FullTriple.logSobolev_dim_of_ext`: Thm 5.7.4 for non-compact triples
  reduces to the single extension statement `ext` (BGL p. 272), which is NOT proved here.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- **Log-Sobolev from `CD(ρ,n)`, `ρ > 0`, unconditionally** (BGL Prop. 5.7.1): `LS(1/ρ, 0)`. -/
theorem logSobolev_unconditional [IsProbabilityMeasure T.μ] {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ)
    (hCD : T.CD ρ n) : T.toDiffusionTriple.LS (1 / ρ) 0 :=
  logSobolev_of_CD_infty T (entropyInterpolation T hCD hρ.le) hρ hCD

/-- The log-Sobolev inequality on the whole Dirichlet domain, unconditionally. -/
theorem logSobolev_domain_unconditional [IsProbabilityMeasure T.μ] {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ)
    (hCD : T.CD ρ n) (u : T.toDiffusionTriple.formDomain) :
    Integrable (fun x => ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 *
        Real.log (((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2)) T.μ ∧
      Ent T.μ (fun x => ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2) ≤
        2 * (1 / ρ) * T.toDiffusionTriple.closedForm u u +
          0 * ∫ x, ((u : Lp ℝ 2 T.μ) : E → ℝ) x ^ 2 ∂T.μ :=
  logSobolev_extend_domain T (entropyInterpolation T hCD hρ.le) hρ hCD u

/-- **The field `bdd` of `FiniteDimInterpolation`** (BGL p. 270: `P_t f` bounded together with `Γ(P_t f)`,
`L P_t f`), for `CD(ρ,n)`, `ρ ≥ 0`, finite `μ`. -/
theorem finiteDim_bdd [IsFiniteMeasure T.μ] {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) (hρ : 0 ≤ ρ)
    (φ : T.A₀) (ε : ℝ) (_hε : 0 < ε) (h0 : 0 ≤ᵐ[T.μ] φ.1) (s : ℝ) (_hs : 0 < s) :
    ∃ B : ℝ, (∀ᵐ x ∂T.μ, T.toDiffusionTriple.ΓA (T.entG φ ε s) (T.entG φ ε s) x ≤ B) ∧
      ∀ᵐ x ∂T.μ, |T.L (T.entG φ ε s) x| ≤ B := by
  obtain ⟨M, hM, hφ⟩ := T.exists_bound φ
  obtain ⟨B, hH⟩ := fisherHyp hCD hρ φ hM h0 hφ s
  have hP := hH.A
  have hc : (fun _ : E => ε) ∈ T.A := const_mem_A T ε
  refine ⟨B, ?_, ?_⟩
  · filter_upwards [ΓA_shift T ε hP, hH.X_le] with x h1 h2
    have h1' : T.toDiffusionTriple.ΓA (fun x => ε + T.Pt s.toNNReal φ x)
        (fun x => ε + T.Pt s.toNNReal φ x) x = G T (T.Pt s.toNNReal φ) (T.Pt s.toNNReal φ) x := h1
    show T.toDiffusionTriple.ΓA (fun x => ε + T.Pt s.toNNReal φ x)
      (fun x => ε + T.Pt s.toNNReal φ x) x ≤ B
    rw [h1']; exact h2
  · filter_upwards [L_lin hc hP 1, L_const (T := T) ε, hH.Q_le] with x h1 h2 h3
    have e : T.L (fun x => ε + 1 * T.Pt s.toNNReal φ x) x = T.L (T.entG φ ε s) x := by
      congr 1; funext y; simp [entG]
    rw [e] at h1
    rw [h1, h2]
    simpa using h3

/-- **Thm 5.7.4 for a `FullTriple` modulo the extension step `ext`**: `FiniteDimInterpolation κ` follows from the
extension of (5.7.12) to bounded `f ∈ 𝒜` (BGL p. 272; open here) together with `CD(ρ,n)`, `ρ ≥ 0`. -/
theorem finiteDimInterpolation_of_ext [IsFiniteMeasure T.μ] {ρ κ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n)
    (hρ : 0 ≤ ρ)
    (hext : ∀ (ε M : ℝ), 0 < ε → 0 < M → ∀ f ∈ T.A, (∀ᵐ x ∂T.μ, f x ∈ Icc ε (ε + M)) →
      ∀ B : ℝ, (∀ᵐ x ∂T.μ, T.toDiffusionTriple.ΓA f f x ≤ B) → (∀ᵐ x ∂T.μ, |T.L f x| ≤ B) →
      ∀ C : BE.Cut ε M,
      Integrable (fun x => f x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x) T.μ →
      Integrable (fun x => f x * T.toDiffusionTriple.ΓA (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x) T.μ →
      κ * ∫ x, f x * T.toDiffusionTriple.ΓA (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x ∂T.μ ≤
        ∫ x, f x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x ∂T.μ) :
    T.FiniteDimInterpolation κ where
  bdd := fun φ ε hε h0 s hs => finiteDim_bdd T hCD hρ φ ε hε h0 s hs
  ext := hext

/-- **BGL Thm 5.7.4 (`LS((n-1)/(ρ n), 0)`) for a `FullTriple` modulo the extension `ext`** (p. 272). -/
theorem logSobolev_dim_of_ext [IsProbabilityMeasure T.μ] {ρ : ℝ} {n : ℝ≥0∞} (hρ : 0 < ρ)
    (hn1 : 1 < n) (hn : n ≠ ⊤) (hCD : T.CD ρ n)
    (hext : ∀ (ε M : ℝ), 0 < ε → 0 < M → ∀ f ∈ T.A, (∀ᵐ x ∂T.μ, f x ∈ Icc ε (ε + M)) →
      ∀ B : ℝ, (∀ᵐ x ∂T.μ, T.toDiffusionTriple.ΓA f f x ≤ B) → (∀ᵐ x ∂T.μ, |T.L f x| ≤ B) →
      ∀ C : BE.Cut ε M,
      Integrable (fun x => f x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x) T.μ →
      Integrable (fun x => f x * T.toDiffusionTriple.ΓA (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x) T.μ →
      (ρ * (n.toReal / (n.toReal - 1))) *
          ∫ x, f x * T.toDiffusionTriple.ΓA (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x ∂T.μ ≤
        ∫ x, f x * T.toDiffusionTriple.Γ₂ (fun y => C.Λ (f y)) (fun y => C.Λ (f y)) x ∂T.μ) :
    T.toDiffusionTriple.LS (dimLSConst ρ n) 0 :=
  logSobolev_of_CD_dim T (entropyInterpolation T hCD hρ.le) hρ hn1 hn hCD
    (finiteDimInterpolation_of_ext T hCD hρ.le hext)

end FullTriple

namespace Instances.Gibbs

namespace GibbsData

variable (G : GibbsData)

/-- **Log-Sobolev for the Gibbs measure `e^{-V}dx`, unconditionally** (`V'' ≥ ρ > 0`): `Ent(f²) ≤ (2/ρ) ∫ f'² dμ`,
`LS(1/ρ, 0)` (BGL Prop. 5.7.1), with no `EntropyInterpolation` hypothesis. -/
theorem gibbsFull_logSobolev_unconditional {ρ : ℝ} (hρpos : 0 < ρ)
    (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) :
    G.gibbsFull_unconditional.toDiffusionTriple.LS (1 / ρ) 0 :=
  haveI : IsProbabilityMeasure G.gibbsFull_unconditional.μ :=
    (inferInstance : IsProbabilityMeasure G.μ)
  FullTriple.logSobolev_unconditional _ hρpos (G.gibbsFull_CD_unconditional hρ)

end GibbsData

end Instances.Gibbs

end MarkovTriple.BGL
