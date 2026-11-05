import Mathlib
import MarkovTriple.Stochastic.R29.GaussRd
import MarkovTriple.Stochastic.R30.GaussIdentify

/-!
# Round 30 (S), part 8: `IsTestClassRep` and the unconditional `MarkovProcessBridge` for `gaussRdFull d`

Frozen statements `S2`, `S3` of `STATEMENTS_R30_S.md`.  The hypothesis `1 ≤ d` of the frozen text is not needed (the proofs work for every `d`);
the `_all` versions are the hypothesis-free statements and the frozen forms are their specialisations.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MarkovTriple.Stochastic.R30

open MarkovTriple.BGL MarkovTriple.BGL.LebesgueRd MarkovTriple.Stochastic MarkovTriple.Stochastic.OU
open MarkovTriple.Stochastic.R29 (mehlerKernelRd mehlerKernelRd_apply gaussRdFull_bridge_of_rep)

variable {d : ℕ}

/-- the Mehler average is the integral against the Mehler kernel -/
lemma integral_mehlerKernelRd {f : (Fin d → ℝ) → ℝ} (hf : Measurable f) (t : ℝ≥0) (x : Fin d → ℝ) :
    ∫ y, f y ∂(mehlerKernelRd d t x) = Gm f (t : ℝ) x := by
  rw [mehlerKernelRd_apply, integral_map (by fun_prop) hf.aestronglyMeasurable]
  rfl

/-- **S2 (hypothesis-free)**: the Mehler kernels represent the Friedrichs semigroup of `gaussRdFull d` on `C_c^∞(ℝ^d)`. -/
theorem gaussRdFull_isTestClassRep_all (d : ℕ) :
    IsTestClassRep (gaussRdFull d).toDiffusionTriple (mehlerKernelRd d) := by
  intro t f hf u hu
  have hf' : f ∈ A₀ d := hf
  have hu' : u = (gaussRdFull d).toDiffusionTriple.cls ⟨f, hf⟩ :=
    Lp.ext (hu.trans (DiffusionTriple.coeFn_cls (gaussRdFull d).toDiffusionTriple ⟨f, hf⟩).symm)
  rw [hu', gaussRdFull_semigroup_eq_Q hf' t]
  have hm : Measurable f := (smooth hf').continuous.measurable
  filter_upwards [(memLp_Gm_ν (hμ d) hf' (t : ℝ)).coeFn_toLp] with x hx
  show (memLp_Gm_ν (hμ d) hf' (t : ℝ)).toLp (Gm f (t : ℝ)) x = _
  rw [hx, integral_mehlerKernelRd hm]

/-- **S2** (frozen form, with the unnecessary hypothesis `1 ≤ d`) -/
theorem gaussRdFull_isTestClassRep (hd : 1 ≤ d) :
    IsTestClassRep (gaussRdFull d).toDiffusionTriple (mehlerKernelRd d) := by
  have _ := hd
  exact gaussRdFull_isTestClassRep_all d

/-- **S3 (hypothesis-free)**: the unconditional `MarkovProcessBridge` of the Gaussian Full triple on `ℝ^d`, with the product Mehler kernels. -/
noncomputable def gaussRdFull_bridge_all (d : ℕ) : MarkovProcessBridge (gaussRdFull d).toDiffusionTriple :=
  gaussRdFull_bridge_of_rep (gaussRdFull_mu d) (gaussRdFull_isTestClassRep_all d)

/-- **S3** (frozen form) -/
noncomputable def gaussRdFull_bridge (_hd : 1 ≤ d) : MarkovProcessBridge (gaussRdFull d).toDiffusionTriple :=
  gaussRdFull_bridge_all d

theorem gaussRdFull_bridge_kernel (hd : 1 ≤ d) (t : ℝ≥0) (x : Fin d → ℝ) :
    (gaussRdFull_bridge hd).kernel t x = mehlerKernelRd d t x := rfl

theorem gaussRdFull_bridge_isMarkov (hd : 1 ≤ d) (t : ℝ≥0) (x : Fin d → ℝ) :
    (gaussRdFull_bridge hd).kernel t x Set.univ = 1 := by
  rw [gaussRdFull_bridge_kernel hd]
  exact measure_univ

/-! ### Corollaries of the bridge -/

/-- the Mehler kernels represent `P_t` on ALL bounded measurable `L²(γ_d)` functions (`rep` field of the bridge) -/
theorem gaussRdFull_rep (d : ℕ) (t : ℝ≥0) (g : (Fin d → ℝ) → ℝ) (hg : Measurable g)
    (hb : ∃ C, ∀ x, |g x| ≤ C) (hL : MemLp g 2 (gaussRdFull d).toDiffusionTriple.μ) :
    ((gaussRdFull d).toDiffusionTriple.semigroup t (hL.toLp g) : (Fin d → ℝ) → ℝ)
      =ᵐ[(gaussRdFull d).toDiffusionTriple.μ] fun x => ∫ y, g y ∂(mehlerKernelRd d t x) :=
  (gaussRdFull_bridge_all d).rep t g hg hb hL

/-- `γ_d` is invariant for the transition kernels of the bridge -/
theorem gaussRdFull_bridge_invariant (d : ℕ) (t : ℝ≥0) :
    (gam d).bind ((gaussRdFull_bridge_all d).kernel t) = gam d := by
  have := (gaussRdFull_bridge_all d).invariant t
  rwa [gaussRdFull_mu d] at this

/-- the same bridge for the Gibbs triple of `gaussData d` (it is `gaussRdFull d` by definition) -/
noncomputable def gaussData_bridge (d : ℕ) :
    MarkovProcessBridge (MarkovTriple.BGL.Instances.GibbsRd.gaussData d).gibbsRdFull_unconditional.toDiffusionTriple :=
  gaussRdFull_bridge_all d

/-- the Mehler transition semigroup of the bridge is Markov (conservative): every kernel has total mass one -/
theorem gaussRdFull_bridge_all_isMarkov (d : ℕ) (t : ℝ≥0) (x : Fin d → ℝ) :
    (gaussRdFull_bridge_all d).kernel t x Set.univ = 1 :=
  measure_univ (μ := mehlerKernelRd d t x)

end MarkovTriple.Stochastic.R30
