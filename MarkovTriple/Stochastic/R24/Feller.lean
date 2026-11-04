import Mathlib
import MarkovTriple.Stochastic.R24.Cutoff

/-!
# Round 24 (C), part 3: the exact Feller kernels `κ_t(x, ·)` for infinite `μ`

For `hF : IsFellerC0 T` and every `t`, `x`, the map `f ↦ (Q_t f)(x)` is a positive linear functional on `C_c(X)`.
Mathlib's Riesz-Markov-Kakutani theorem (`RealRMK.rieszMeasure`) turns it into a regular Borel measure `κ_t(x, ·)`,
of mass at most one (inner regularity + `|Q_t f| ≤ 1` for `0 ≤ f ≤ 1`).  See `STATEMENTS_R24_C.md`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R24

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R23

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

/-- the positive linear functional `f ↦ (Q_t f)(x)` on `C_c(X)` -/
noncomputable def lam (t : ℝ≥0) (x : X) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => Qop hF t f x
      map_add' := fun f g => by simp [Qop_add hF t f g]
      map_smul' := fun c f => by simp [Qop_smul hF t c f] }
    (fun f hf => Qop_nonneg hF t (fun y => hf y) x)

omit [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X] in
lemma lam_apply (t : ℝ≥0) (x : X) (f : C_c(X, ℝ)) : lam hF t x f = Qop hF t f x := rfl

/-- the Riesz measure of `f ↦ (Q_t f)(x)` -/
noncomputable def fellerMeasure (t : ℝ≥0) (x : X) : Measure X := RealRMK.rieszMeasure (lam hF t x)

omit [SecondCountableTopology X] in
lemma integral_fellerMeasure (t : ℝ≥0) (x : X) (f : C_c(X, ℝ)) :
    ∫ y, f y ∂(fellerMeasure hF t x) = Qop hF t f x := RealRMK.integral_rieszMeasure (lam hF t x) f

instance fellerMeasure_regular (t : ℝ≥0) (x : X) : (fellerMeasure hF t x).Regular :=
  RealRMK.regular_rieszMeasure (lam hF t x)

lemma fellerMeasure_univ_le (t : ℝ≥0) (x : X) : fellerMeasure hF t x Set.univ ≤ 1 := by
  rw [MeasurableSet.univ.measure_eq_iSup_isCompact]
  refine iSup₂_le fun K _ => iSup_le fun hK => ?_
  obtain ⟨f, hf1, hf2, -, hf3⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ
    (Set.subset_univ K)
  let f' : C_c(X, ℝ) := ⟨f, hasCompactSupport_def.mpr hf2⟩
  have h1 := RealRMK.rieszMeasure_le_of_eq_one (lam hF t x) (f := f') (fun y => (hf3 y).1) hK
    (fun y hy => show f y = 1 by simpa using hf1 hy)
  refine h1.trans ?_
  rw [lam_apply]
  have : Qop hF t f' x ≤ 1 :=
    (le_abs_self _).trans (Qop_abs_le hF t f' (C := 1) (fun y => show |f y| ≤ 1 by
      rw [abs_of_nonneg (hf3 y).1]; exact (hf3 y).2) x)
  simpa using ENNReal.ofReal_le_ofReal this

instance fellerMeasure_finite (t : ℝ≥0) (x : X) : IsFiniteMeasure (fellerMeasure hF t x) :=
  ⟨lt_of_le_of_lt (fellerMeasure_univ_le hF t x) ENNReal.one_lt_top⟩

/-- **The exact Feller kernels** (defined at every point). -/
noncomputable def fellerKernelInf (t : ℝ≥0) : Kernel X X where
  toFun := fellerMeasure hF t
  measurable' := measurable_of_integrals_cc (κ := fellerMeasure hF t) fun f => by
    simp_rw [integral_fellerMeasure]
    exact (Qop hF t f).continuous.measurable

lemma fellerKernelInf_apply (t : ℝ≥0) (x : X) : fellerKernelInf hF t x = fellerMeasure hF t x := rfl

/-- **Pointwise representation on `C_c`, for all `x`.** -/
theorem integral_fellerKernelInf (t : ℝ≥0) (x : X) (f : C_c(X, ℝ)) :
    ∫ y, f y ∂(fellerKernelInf hF t x) = Qop hF t f x := integral_fellerMeasure hF t x f

theorem fellerKernelInf_subMarkov (t : ℝ≥0) (x : X) : fellerKernelInf hF t x Set.univ ≤ 1 :=
  fellerMeasure_univ_le hF t x

instance (t : ℝ≥0) : IsFiniteKernel (fellerKernelInf hF t) :=
  ⟨⟨1, ENNReal.one_lt_top, fellerKernelInf_subMarkov hF t⟩⟩

end MarkovTriple.Stochastic.R24
