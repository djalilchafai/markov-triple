import Mathlib
import MarkovTriple.BGL.Sanity.Trivial
import MarkovTriple.BGL.Theory.Poincare
import MarkovTriple.BGL.Theory.GradientBound
import MarkovTriple.BGL.Theory.LogSobolevMain

/-!
# Tests of the `BGL/Theory` results on the trivial compact triple (one-point space)

* the integral identities and the Poincaré theorems apply (the trivial triple is a probability,
  ergodic, ESA full triple with `CD(ρ, n)` for all `ρ`, `n ≥ 1`);
* the two explicit regularity hypotheses `GradientInterpolation`, `EntropyInterpolation` are
  satisfiable (they hold for the trivial triple), so they are not vacuous/contradictory;
* the ESA ⇒ `P_t 1 = 1` theorem applies.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Sanity

private noncomputable abbrev TT : FullTriple Unit := trivialCompact.toFullTriple

instance : IsProbabilityMeasure TT.μ := (inferInstance : IsProbabilityMeasure (Measure.dirac ()))

lemma TT_L (f : Unit → ℝ) (x : Unit) : TT.L f x = 0 := rfl

lemma TT_ΓA (f g : Unit → ℝ) : TT.toDiffusionTriple.ΓA f g = 0 := by
  funext x; simp [DiffusionTriple.ΓA, TT_L]

lemma TT_Γ₂ (f g : Unit → ℝ) : TT.toDiffusionTriple.Γ₂ f g = 0 := by
  funext x; simp [DiffusionTriple.Γ₂, TT_ΓA, TT_L]

/-- Poincaré for the trivial triple, via the general theorem (with `ρ = 1`, `n = ∞`). -/
theorem TT_PI : TT.toDiffusionTriple.PI (1 / 1) :=
  FullTriple.poincare_of_CD_infty TT one_pos (trivialCompact_CD 1 le_top)

/-- Lichnerowicz form for `n = 2`. -/
theorem TT_PI_dim : TT.toDiffusionTriple.PI ((1 - ((2 : ℝ≥0∞)⁻¹).toReal) / 1) :=
  FullTriple.poincare_of_CD_dim TT one_pos (by norm_num) (trivialCompact_CD 1 (by norm_num))

/-- Integrated `Γ₂` identity on the trivial triple. -/
example (f : Unit → ℝ) (hf : f ∈ TT.A₀) :
    ∫ x, TT.toDiffusionTriple.Γ₂ f f x ∂TT.μ = ∫ x, TT.L f x * TT.L f x ∂TT.μ :=
  FullTriple.integral_Γ₂ TT hf

/-- ESA ⇒ `P_t 1 = 1` applies to the trivial triple (finite measure). -/
example (t : ℝ≥0) :
    TT.toDiffusionTriple.semigroup t TT.toDiffusionTriple.one2 = TT.toDiffusionTriple.one2 :=
  DiffusionTriple.semigroup_one2 TT.toDiffusionTriple TT.esaProp t

/-- `GradientInterpolation` is satisfiable. -/
theorem TT_GradientInterpolation : TT.GradientInterpolation := by
  have h0 : ∀ (f h : TT.A₀) (t : ℝ≥0), TT.gradPhi f h t = fun _ => 0 := by
    intro f h t; funext s; simp [FullTriple.gradPhi, TT_ΓA]
  refine ⟨fun f h _ t => ?_, fun f h _ t s hs => ?_⟩
  · rw [h0]; exact continuousOn_const
  · refine ⟨by simp [TT_ΓA], by simp [TT_Γ₂], ?_⟩
    rw [h0]
    simpa [TT_Γ₂] using hasDerivAt_const s (0 : ℝ)

/-- On `Unit` with the Dirac measure, an a.e. equality is a pointwise equality. -/
lemma ae_unit {f g : Unit → ℝ} (h : f =ᵐ[TT.μ] g) : f () = g () := by
  have h' : f =ᵐ[Measure.dirac ()] g := h
  rw [ae_dirac_eq] at h'
  exact Filter.eventually_pure.1 h'

lemma TT_Pt (t : ℝ≥0) (f : TT.A₀) : TT.Pt t f () = f.1 () := by
  have e : TT.toDiffusionTriple.semigroup t (TT.toDiffusionTriple.cls f) =
      TT.toDiffusionTriple.cls f := trivialDiffusion_semigroup_cls _ t f
  have h1 := TT.Pt_ae t f
  rw [e] at h1
  have h2 := DiffusionTriple.coeFn_cls TT.toDiffusionTriple f
  exact (ae_unit h1).symm.trans (ae_unit h2)

lemma TT_entG (φ : TT.A₀) (ε s : ℝ) : TT.entG φ ε s = fun _ => ε + φ.1 () := by
  funext x; cases x; simp [FullTriple.entG, TT_Pt]

lemma TT_entE (φ : TT.A₀) (ε s : ℝ) :
    TT.entE φ ε s = (ε + φ.1 ()) * Real.log (ε + φ.1 ()) := by
  unfold FullTriple.entE
  rw [TT_entG]
  show ∫ x : Unit, _ ∂(Measure.dirac ()) = _
  rw [integral_dirac]

lemma TT_entI (φ : TT.A₀) (ε s : ℝ) : TT.entI φ ε s = 0 := by
  simp [FullTriple.entI, TT_ΓA]

lemma TT_entJ (Λ : ℝ → ℝ) (φ : TT.A₀) (ε s : ℝ) : TT.entJ Λ φ ε s = 0 := by
  simp [FullTriple.entJ, TT_Γ₂]

/-- `EntropyInterpolation` is satisfiable. -/
theorem TT_EntropyInterpolation : TT.EntropyInterpolation := by
  refine ⟨fun φ ε _ _ => ?_, fun φ ε _ _ => ?_, fun φ ε _ _ s _ => ?_,
    fun φ ε M _ _ _ _ C s _ => ?_⟩
  · have : TT.entE φ ε = fun _ => (ε + φ.1 ()) * Real.log (ε + φ.1 ()) := funext (TT_entE φ ε)
    rw [this]; exact continuousOn_const
  · have : TT.entI φ ε = fun _ => 0 := funext (TT_entI φ ε)
    rw [this]; exact continuousOn_const
  · have : TT.entE φ ε = fun _ => (ε + φ.1 ()) * Real.log (ε + φ.1 ()) := funext (TT_entE φ ε)
    rw [this, TT_entI]
    simpa using hasDerivAt_const s ((ε + φ.1 ()) * Real.log (ε + φ.1 ()))
  · refine ⟨by simp [TT_Γ₂], by simp [TT_ΓA], ?_⟩
    have : TT.entI φ ε = fun _ => 0 := funext (TT_entI φ ε)
    rw [this, TT_entJ]
    simpa using hasDerivAt_const s (0 : ℝ)

end MarkovTriple.BGL.Sanity
