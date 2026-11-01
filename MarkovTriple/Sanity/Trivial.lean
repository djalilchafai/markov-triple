import Mathlib
import MarkovTriple.Frozen.FullMarkovTriple
import MarkovTriple.Frozen.CD
import MarkovTriple.Frozen.Poincare
import MarkovTriple.Frozen.LSI

/-!
# Sanity checks (NOT frozen): the structures are satisfiable.

The trivial triple `L = 0`, `Γ = 0` on a finite discrete measurable space with a finite measure.
This shows non-vacuity of every field of `MarkovTriple` and `FullMarkovTriple` and of `IsSemigroupOf`
(with `P_t = id`). It does *not* test the nontrivial `Γ ≠ 0` case: see `FROZEN_REVIEW.md`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovTriple.Sanity

variable {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Finite E]

/-- The trivial Markov triple on a finite discrete space. -/
noncomputable def trivialTriple (μ : Measure E) [IsFiniteMeasure μ] : MarkovTriple E where
  μ := μ
  sigmaFinite := inferInstance
  A₀ := ⊤
  comp_mem := fun _ _ _ _ _ _ => Set.mem_univ _
  Γ := fun _ _ _ => 0
  L := fun _ _ => 0
  measurable := fun f _ => Measurable.of_discrete
  memLp := fun f _ p _ _ => MemLp.of_discrete
  Γ_mem := fun _ _ _ _ => Set.mem_univ _
  L_mem := fun _ _ => Set.mem_univ _
  Γ_symm := fun _ _ _ _ => rfl
  Γ_add := fun _ _ _ _ _ _ => by ext; simp
  Γ_smul := fun _ _ _ _ _ => by ext; simp
  Γ_nonneg := fun _ _ _ => le_refl _
  L_add := fun _ _ _ _ => by ext; simp
  L_smul := fun _ _ _ => by ext; simp
  carre_du_champ := fun _ _ _ _ _ => by simp
  ibp := fun _ _ _ _ => by simp
  dense := fun p _ _ => by
    have : {u : Lp ℝ p μ | ∃ f ∈ (⊤ : NonUnitalSubalgebra ℝ (E → ℝ)), (u : E → ℝ) =ᵐ[μ] f} = Set.univ :=
      Set.eq_univ_of_forall fun u => ⟨u, Set.mem_univ _, Filter.EventuallyEq.refl _ _⟩
    rw [this]; exact dense_univ
  diffusion := fun k ψ _ _ f _ => by
    refine ⟨fun g _ => ?_, ?_⟩ <;> ext x <;> simp

/-- The trivial *full* Markov triple (`𝒜 = 𝒜₀ = ⊤`). Requires `P_t`-stability, here `P_t = id`. -/
noncomputable def trivialFull (μ : Measure E) [IsFiniteMeasure μ] : FullMarkovTriple E where
  toMarkovTriple := trivialTriple μ
  A := ⊤
  A₀_le := fun _ _ => Algebra.mem_top
  A_comp := fun _ _ _ _ _ => Algebra.mem_top
  A_measurable := fun f _ => Measurable.of_discrete
  L_mem_A := fun _ _ => Algebra.mem_top
  Γ_mem_A := fun _ _ _ _ => Algebra.mem_top
  Γ_symm_A := fun _ _ _ _ => rfl
  Γ_add_A := fun _ _ _ _ _ _ => by ext; simp [trivialTriple]
  Γ_smul_A := fun _ _ _ _ _ => by ext; simp [trivialTriple]
  Γ_nonneg_A := fun _ _ _ => le_refl _
  L_add_A := fun _ _ _ _ => by ext; simp [trivialTriple]
  L_smul_A := fun _ _ _ => by ext; simp [trivialTriple]
  carre_du_champ_A := fun _ _ _ _ _ => by simp [trivialTriple]
  diffusion_A := fun k ψ _ f _ => by
    refine ⟨fun g _ => ?_, ?_⟩ <;> ext x <;> simp [trivialTriple]
  esa := dense_univ.mono fun u _ =>
    ⟨u, Set.mem_univ _, by filter_upwards with x; simp [trivialTriple]⟩
  ibp_A := fun f _ _ _ g _ => by
    refine ⟨?_, ?_⟩ <;> simp [trivialTriple]
  ibp_A_symm := fun f _ _ _ g _ => by simp [trivialTriple]
  ibp_AA := fun f _ k _ _ _ _ _ _ => by
    refine ⟨?_, ?_⟩ <;> simp [trivialTriple]
  semigroup_stable := fun P hP t f _ u hu => by
    exact ⟨_, Algebra.mem_top, Lp.memLp _, by simp [trivialTriple],
      Filter.EventuallyEq.refl _ _⟩

/-- `P_t = id` is a semigroup of the trivial triple. -/
theorem trivialTriple_isSemigroup (μ : Measure E) [IsFiniteMeasure μ] :
    (trivialTriple μ).IsSemigroupOf (fun _ => ContinuousLinearMap.id ℝ _) := by
  refine ⟨rfl, fun s t => rfl, fun u => ?_, fun t u v => rfl, fun t u hu => hu,
    fun t u hu => hu, fun t u hu => hu, fun f _ u v hu hv => ?_⟩
  · exact tendsto_const_nhds
  · have hv0 : v = 0 := Lp.ext (hv.trans (Lp.coeFn_zero ℝ 2 μ).symm)
    simp [hv0]

/-- `CD(ρ,n)` holds for the trivial triple, for every `ρ` and every `0 < n ≤ ∞` (both `n = ∞`
and finite `n`), and fails for `n = 0`. -/
theorem trivialTriple_CD (μ : Measure E) [IsFiniteMeasure μ] (ρ : ℝ) {n : ℝ≥0∞} (hn : 0 < n) :
    (trivialTriple μ).CD ρ n :=
  ⟨hn, fun f _ => by filter_upwards with x; simp [Γ₂, trivialTriple]⟩

theorem trivialTriple_not_CD_zero (μ : Measure E) [IsFiniteMeasure μ] (ρ : ℝ) :
    ¬ (trivialTriple μ).CD ρ 0 := fun h => lt_irrefl _ h.1

/-- `PI(0)` holds on the one-point space (all test functions are constant). -/
theorem unit_PI : (trivialTriple (Measure.dirac ())).PoincareIneq 0 := by
  refine ⟨by simp [trivialTriple]; infer_instance, fun f _ => ?_⟩
  have : ProbabilityTheory.variance f (Measure.dirac ()) = 0 := ProbabilityTheory.variance_dirac ()
  simp [this, energy, trivialTriple]

end MarkovTriple.Sanity
