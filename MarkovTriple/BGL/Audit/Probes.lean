import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Frozen.FormDomain
import MarkovTriple.BGL.Frozen.Fisher
import MarkovTriple.BGL.Frozen.Poincare
import MarkovTriple.BGL.Frozen.LSI

/-! Hostile probes of the BGL frozen surface (NOT imported by root). -/
open MeasureTheory
namespace MarkovTriple.BGL.Audit

variable {E : Type*} [MeasurableSpace E]

/-- PROBE 1: `PoincareIneq` is vacuous on the empty class, for *any* `Γ`, any constant `C > 0`. -/
theorem pi_empty (μ : Measure E) [IsProbabilityMeasure μ]
    (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (C : ℝ) (hC : 0 < C) : PoincareIneq μ Γ ∅ C :=
  ⟨inferInstance, hC, fun f hf => absurd hf (Set.notMem_empty f)⟩

/-- PROBE 2: same for LS(C,D). -/
theorem lsi_empty (μ : Measure E) [IsProbabilityMeasure μ]
    (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (C D : ℝ) (hC : 0 < C) (hD : 0 ≤ D) :
    LogSobolevIneq μ Γ ∅ C D :=
  ⟨inferInstance, hC, hD, fun f hf => absurd hf (Set.notMem_empty f)⟩

/-- PROBE 3: Bochner junk.  If the energy integrand is not integrable, `energy = 0`; so
`PoincareIneq μ Γ 𝒞 C` is *false* as soon as `𝒞` contains a nonconstant `f` of positive variance
with non-integrable `Γ(f,f)` (e.g. `𝒞 = T.A` for OU with `f = e^{x²/4}/(1+x²)`). -/
theorem energy_junk (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (f : E → ℝ)
    (h : ¬ Integrable (Γ f f) μ) : energy μ Γ f = 0 := by
  unfold energy dirichletForm; exact integral_undef h

theorem pi_fails_of_junk (μ : Measure E) (Γ : (E → ℝ) → (E → ℝ) → (E → ℝ)) (f : E → ℝ)
    (C : ℝ) (𝒞 : Set (E → ℝ)) (hf : f ∈ 𝒞) (h : ¬ Integrable (Γ f f) μ)
    (hv : 0 < ProbabilityTheory.variance f μ) : ¬ PoincareIneq μ Γ 𝒞 C := by
  intro ⟨_, _, H⟩
  have := H f hf
  rw [energy_junk μ Γ f h] at this
  linarith

/-- PROBE 4: `IsExhaustion` (a.e. reading) admits sequences whose first term is very negative, and
sequences differing from the constant `1` on a null set; S11 must be proved for all of them. -/
example {A₀ : NonUnitalSubalgebra ℝ (E → ℝ)} (μ : Measure E) (h1 : (fun _ => (1 : ℝ)) ∈ A₀)
    (h5 : (fun _ => (-5 : ℝ)) ∈ A₀) :
    IsExhaustion μ A₀ (fun n => if n = 0 then fun _ => (-5 : ℝ) else fun _ => 1) := by
  refine ⟨fun n => ?_, fun n => ?_, ?_⟩
  · by_cases hn : n = 0 <;> simp [hn, h1, h5]
  · refine Filter.Eventually.of_forall fun x => ?_
    by_cases hn : n = 0 <;> simp [hn]
    norm_num
  · refine Filter.Eventually.of_forall fun x => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    simp [Nat.pos_iff_ne_zero.1 hn]

/-- PROBE 5: `finite_prob` excludes the zero measure and non-normalised finite measures. -/
example (T : DiffusionTriple E) [IsFiniteMeasure T.μ] : IsProbabilityMeasure T.μ :=
  T.finite_prob ‹_›

end MarkovTriple.BGL.Audit
