import Mathlib
import MarkovTriple.Stochastic.R25.Mass

/-!
# Round 27 (K), part 1: pointwise mass one for Feller + S11: the conditional theory

S11 + `IsFellerC0` give `κ_t(x, X) = 1` only a.e. (R25-E).  Here: the mass is non-increasing in time (CK), and if the kernels are
absolutely continuous w.r.t. `μ` the a.e. mass-one statement transfers through CK, so the pointwise mass is *time-independent* for `t > 0`
(`fellerKernelInf_univ_const_of_ac`); a pointwise initial condition `Q_t f(x) → f(x)` then forces it to be `1`.
Nothing here shows that S11 + Feller alone gives mass one everywhere, nor that it fails (see `STATEMENTS_R27_K.md`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R27

open MarkovTriple.BGL MarkovTriple.Stochastic MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R23
  MarkovTriple.Stochastic.R25

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]

section Antitone

variable {T : DiffusionTriple X} [IsFiniteMeasureOnCompacts T.μ] [T.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 T)

/-- `kappa_{s+t}(x, X) = ∫ kappa_t(y, X) d kappa_s(x, y)` -/
theorem fellerKernelInf_univ_add (s t : ℝ≥0) (x : X) :
    fellerKernelInf hF (s + t) x Set.univ = ∫⁻ y, fellerKernelInf hF t y Set.univ ∂(fellerKernelInf hF s x) := by
  rw [fellerKernelInf_add hF s t, Kernel.comp_apply' _ _ _ MeasurableSet.univ]

/-- the total mass is non-increasing in time -/
theorem fellerKernelInf_univ_antitone (s t : ℝ≥0) (x : X) :
    fellerKernelInf hF (s + t) x Set.univ ≤ fellerKernelInf hF s x Set.univ := by
  rw [fellerKernelInf_univ_add hF s t x]
  calc ∫⁻ y, fellerKernelInf hF t y Set.univ ∂(fellerKernelInf hF s x)
      ≤ ∫⁻ _y, 1 ∂(fellerKernelInf hF s x) := lintegral_mono fun y => fellerKernelInf_subMarkov hF t y
    _ = fellerKernelInf hF s x Set.univ := by simp

end Antitone

section AC

variable (S : StandardTriple X) [IsFiniteMeasureOnCompacts S.μ] [S.μ.IsOpenPosMeasure]
  (hF : IsFellerC0 S.toDiffusionTriple)

/-- absolute continuity of `κ_s(x, ·)` transfers the a.e. mass-one statement through CK. -/
theorem fellerKernelInf_univ_add_of_ac (s t : ℝ≥0) (x : X) (hac : fellerKernelInf hF s x ≪ S.μ) :
    fellerKernelInf hF (s + t) x Set.univ = fellerKernelInf hF s x Set.univ := by
  rw [fellerKernelInf_univ_add hF s t x]
  have h1 : ∀ᵐ y ∂(fellerKernelInf hF s x), fellerKernelInf hF t y Set.univ = 1 :=
    hac.ae_le (fellerKernelInf_univ_ae S hF t)
  rw [lintegral_congr_ae h1]
  simp

theorem fellerKernelInf_univ_const_of_ac
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ S.μ) (s t : ℝ≥0) (hs : 0 < s) (ht : 0 < t)
    (x : X) : fellerKernelInf hF s x Set.univ = fellerKernelInf hF t x Set.univ := by
  have h1 := fellerKernelInf_univ_add_of_ac S hF s t x (hac s hs x)
  have h2 := fellerKernelInf_univ_add_of_ac S hF t s x (hac t ht x)
  rw [add_comm t s] at h2
  rw [← h1, h2]

theorem fellerKernelInf_univ_eq_one_of_ac_init
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ S.μ)
    (hinit : ∀ (x : X) (f : C_c(X, ℝ)),
      Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x)))
    (t : ℝ≥0) (x : X) : fellerKernelInf hF t x Set.univ = 1 := by
  rcases eq_or_lt_of_le (bot_le : (0:ℝ≥0) ≤ t) with h0 | ht
  · have h0' : t = 0 := h0.symm
    rw [h0', fellerKernelInf_zero hF]; simp
  have hle := fellerKernelInf_subMarkov hF t x
  refine le_antisymm hle ?_
  obtain ⟨φ, hφ, hφx, -⟩ := exists_bump x Set.univ Filter.univ_mem
  -- Q_s φ (x) ≤ κ_s(x, X) = κ_t(x, X) for every s > 0
  have hbound : ∀ s : ℝ≥0, 0 < s → Qop hF s φ x ≤ (fellerKernelInf hF t x Set.univ).toReal := by
    intro s hs
    rw [← integral_fellerKernelInf hF s x φ]
    have hi : Integrable φ (fellerKernelInf hF s x) :=
      φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport
    have : ∫ y, φ y ∂(fellerKernelInf hF s x) ≤ ∫ y, (1 : ℝ) ∂(fellerKernelInf hF s x) :=
      integral_mono hi (integrable_const _) fun y => (hφ y).2
    refine this.trans ?_
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real]
    rw [fellerKernelInf_univ_const_of_ac S hF hac s t hs ht x]
  have hlim : (1 : ℝ) ≤ (fellerKernelInf hF t x Set.univ).toReal := by
    have hT := hinit x φ
    rw [hφx] at hT
    refine le_of_tendsto hT ?_
    filter_upwards [self_mem_nhdsWithin] with s hs using hbound s hs
  have : (1 : ℝ≥0∞).toReal ≤ (fellerKernelInf hF t x Set.univ).toReal := by simpa using hlim
  exact (ENNReal.toReal_le_toReal ENNReal.one_ne_top
    (ne_top_of_le_ne_top ENNReal.one_ne_top hle)).1 this

/-- **A `MarkovProcessBridge` for a conservative `C_0`-Feller triple whose kernels are absolutely continuous and satisfy
the pointwise initial condition.** -/
noncomputable def fellerMarkovProcessBridgeInf_of_ac_init
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ S.μ)
    (hinit : ∀ (x : X) (f : C_c(X, ℝ)),
      Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x))) :
    MarkovProcessBridge S.toDiffusionTriple :=
  fellerMarkovProcessBridgeInf hF (fun t x => fellerKernelInf_univ_eq_one_of_ac_init S hF hac hinit t x)

end AC

end MarkovTriple.Stochastic.R27
