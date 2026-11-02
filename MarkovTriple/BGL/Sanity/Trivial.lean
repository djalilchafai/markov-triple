import Mathlib
import MarkovTriple.BGL.Frozen.CompactTriple
import MarkovTriple.BGL.Frozen.CD
import MarkovTriple.BGL.Frozen.Poincare
import MarkovTriple.BGL.Frozen.LSI
import MarkovTriple.BGL.Frozen.FormDomain
import MarkovTriple.BGL.SemigroupLemmas

/-!
# Sanity checks (NOT frozen): the new structures are non-vacuous

* `trivialDiffusion μ`: the trivial Diffusion Markov Triple (`L = 0`, `Γ = 0`, `𝒜₀ = ⊤`) on any finite
  discrete space with a probability measure `μ`.  Boundedness, exhaustion (`u_n = 1`), density, all
  fields are checked.
* `trivialCompact`: on the one-point space, the trivial *Compact* Markov triple (so `StandardTriple`,
  `FullTriple` too): ergodicity S10, conservativeness S11 (the Friedrichs semigroup is `P_t = id`),
  F1–F10, with `𝒜 = 𝒜₀ = ⊤`.  (On a space with two or more points of positive mass the trivial
  triple is not ergodic, hence not standard; this is why the one-point space is used.)
* `CD(ρ,n)`, `P(C)`, `LS(C,D)` hold on it; `CD(ρ, n)` fails for `n < 1`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Sanity

section Diffusion

variable {E : Type*} [MeasurableSpace E] [DiscreteMeasurableSpace E] [Finite E]

/-- The trivial Diffusion Markov Triple on a finite discrete probability space. -/
noncomputable def trivialDiffusion (μ : Measure E) [IsProbabilityMeasure μ] : DiffusionTriple E where
  μ := μ
  sigmaFinite := inferInstance
  finite_prob := fun _ => inferInstance
  A₀ := ⊤
  measurable := fun _ _ => Measurable.of_discrete
  bounded := fun f _ => by
    obtain ⟨C, hC⟩ := (Set.finite_range (fun x => |f x|)).bddAbove
    exact ⟨C, fun x => hC ⟨x, rfl⟩⟩
  memLp := fun _ _ _ _ _ => MemLp.of_discrete
  dense := fun p _ _ => by
    have : {u : Lp ℝ p μ | ∃ f ∈ (⊤ : NonUnitalSubalgebra ℝ (E → ℝ)), (u : E → ℝ) =ᵐ[μ] f} =
        Set.univ :=
      Set.eq_univ_of_forall fun u => ⟨u, Set.mem_univ _, Filter.EventuallyEq.refl _ _⟩
    rw [this]; exact dense_univ
  comp_mem := fun _ _ _ _ _ _ => Set.mem_univ _
  exhaustion := ⟨fun _ _ => 1, fun _ => Set.mem_univ _,
    fun _ => Filter.Eventually.of_forall fun _ => le_refl _,
    Filter.Eventually.of_forall fun _ => tendsto_const_nhds⟩
  Γ := fun _ _ _ => 0
  L := fun _ _ => 0
  Γ_mem := fun _ _ _ _ => Set.mem_univ _
  L_mem := fun _ _ => Set.mem_univ _
  Γ_symm := fun _ _ _ _ => Filter.EventuallyEq.refl _ _
  Γ_add := fun _ _ _ _ _ _ => Filter.Eventually.of_forall fun x => by simp
  Γ_smul := fun _ _ _ _ _ => Filter.Eventually.of_forall fun x => by simp
  Γ_nonneg := fun _ _ => Filter.Eventually.of_forall fun x => le_refl _
  diffusion := fun _ _ _ _ _ _ _ _ => Filter.Eventually.of_forall fun x => by simp
  ibp := fun _ _ _ _ => by simp
  integral_L := fun _ _ => by simp

/-- For the trivial triple the Friedrichs semigroup is the identity on classes of test functions. -/
theorem trivialDiffusion_semigroup_cls (μ : Measure E) [IsProbabilityMeasure μ] (t : ℝ≥0)
    (f : (trivialDiffusion μ).A₀) :
    (trivialDiffusion μ).semigroup t ((trivialDiffusion μ).cls f) = (trivialDiffusion μ).cls f :=
  DiffusionTriple.semigroup_cls_of_L_zero _ (fun _ _ => Filter.EventuallyEq.refl _ _) t f

end Diffusion

/-- The trivial Compact Markov Triple on the one-point space with the Dirac measure. -/
noncomputable def trivialCompact : CompactTriple Unit where
  toDiffusionTriple := trivialDiffusion (Measure.dirac ())
  ergodic := fun u _ _ => ⟨u (), Filter.Eventually.of_forall fun x => by cases x; rfl⟩
  conservative := fun u hu _ t => by
    have h1 : ∀ᵐ x ∂(Measure.dirac ()), ∀ n,
        (((trivialDiffusion (Measure.dirac ())).semigroup t
          ((trivialDiffusion (Measure.dirac ())).cls ⟨u n, hu.1 n⟩) : Lp ℝ 2 _) : Unit → ℝ) x =
          u n x := by
      rw [ae_all_iff]
      intro n
      rw [trivialDiffusion_semigroup_cls]
      exact DiffusionTriple.coeFn_cls _ ⟨u n, hu.1 n⟩
    filter_upwards [h1, hu.2.2] with x h1 h2
    simp only [h1]; exact h2
  A := ⊤
  A₀_le := fun _ _ => Algebra.mem_top
  A_measurable := fun _ _ => Measurable.of_discrete
  ideal := fun _ _ _ _ => Set.mem_univ _
  pos_detect := fun f _ h => Filter.Eventually.of_forall fun x => by
    have := h (fun _ => 1) (Set.mem_univ _) (Filter.Eventually.of_forall fun _ => zero_le_one)
    cases x
    simpa [trivialDiffusion] using this
  A_comp := fun _ _ _ _ _ => Algebra.mem_top
  L_mem_A := fun _ _ => Algebra.mem_top
  ΓA_nonneg := fun f _ => Filter.Eventually.of_forall fun x => by
    simp [DiffusionTriple.ΓA, trivialDiffusion]
  diffusion_Γ_A := fun k ψ _ f _ g _ => Filter.Eventually.of_forall fun x => by
    simp [DiffusionTriple.ΓA, trivialDiffusion]
  diffusion_L_A := fun k ψ _ f _ => Filter.Eventually.of_forall fun x => by
    simp [DiffusionTriple.ΓA, trivialDiffusion]
  ibp_A := fun f _ g _ => by
    refine ⟨?_, ?_⟩ <;> simp [DiffusionTriple.ΓA, trivialDiffusion]
  semigroup_A := fun t f => ⟨f.1, Algebra.mem_top, by
    rw [trivialDiffusion_semigroup_cls]
    exact DiffusionTriple.coeFn_cls _ f⟩
  connected := fun f _ _ => ⟨f (), Filter.Eventually.of_forall fun x => by cases x; rfl⟩
  esa := fun u hu => by
    have hmem : (u : Unit → ℝ) ∈ (trivialDiffusion (Measure.dirac ())).A₀ := Set.mem_univ _
    have hu' : (trivialDiffusion (Measure.dirac ())).cls ⟨(u : Unit → ℝ), hmem⟩ = u :=
      Lp.ext (DiffusionTriple.coeFn_cls _ ⟨(u : Unit → ℝ), hmem⟩)
    refine ⟨fun _ => ⟨(u : Unit → ℝ), hmem⟩, ?_, ?_⟩
    · simp only [hu']; exact tendsto_const_nhds
    · have := DiffusionTriple.generator_cls (trivialDiffusion (Measure.dirac ()))
        ⟨(u : Unit → ℝ), hmem⟩ (by rw [hu']; exact hu)
      have h2 : (trivialDiffusion (Measure.dirac ())).generator ⟨u, hu⟩ =
          (trivialDiffusion (Measure.dirac ())).Lcls ⟨(u : Unit → ℝ), hmem⟩ := by
        have e : (⟨u, hu⟩ : (trivialDiffusion (Measure.dirac ())).generator.domain) =
            ⟨(trivialDiffusion (Measure.dirac ())).cls ⟨(u : Unit → ℝ), hmem⟩, by
              rw [hu']; exact hu⟩ := Subtype.ext hu'.symm
        rw [e]; exact this
      rw [h2]; exact tendsto_const_nhds
  A_eq := fun f => ⟨fun _ => Set.mem_univ _, fun _ => Algebra.mem_top⟩

/-- `CD(ρ, n)` holds for the trivial compact triple, for every `ρ` and every `n ∈ [1, ∞]`. -/
theorem trivialCompact_CD (ρ : ℝ) {n : ℝ≥0∞} (hn : 1 ≤ n) :
    trivialCompact.toFullTriple.CD ρ n :=
  ⟨hn, fun f _ => Filter.Eventually.of_forall fun x => by
    simp [DiffusionTriple.ΓA, DiffusionTriple.Γ₂, trivialCompact, trivialDiffusion]⟩

/-- `CD(ρ, n)` fails for `n < 1` (the book's range is `n ∈ [1, ∞]`). -/
theorem trivialCompact_not_CD_zero (ρ : ℝ) : ¬ trivialCompact.toFullTriple.CD ρ 0 :=
  fun h => absurd h.1 (not_le.2 zero_lt_one)

/-- `P(1)` holds on the one-point space (all test functions are constant). -/
theorem trivialCompact_PI :
    PoincareIneq (Measure.dirac ()) (trivialDiffusion (Measure.dirac ())).Γ
      (trivialDiffusion (Measure.dirac ())).A₀ 1 := by
  refine ⟨inferInstance, one_pos, fun f _ => ?_⟩
  have : ProbabilityTheory.variance f (Measure.dirac ()) = 0 := ProbabilityTheory.variance_dirac ()
  simp [this, energy, dirichletForm, trivialDiffusion]

/-- `LS(1, 0)` holds on the one-point space. -/
theorem trivialCompact_LS :
    LogSobolevIneq (Measure.dirac ()) (trivialDiffusion (Measure.dirac ())).Γ
      (trivialDiffusion (Measure.dirac ())).A₀ 1 0 := by
  refine ⟨inferInstance, one_pos, le_refl _, fun f _ => ?_⟩
  simp [Ent, energy, dirichletForm, trivialDiffusion]

end MarkovTriple.BGL.Sanity
