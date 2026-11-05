import Mathlib
import MarkovTriple.Stochastic.R30T.Init

/-!
# Round 30 (T), part 5: instances (Gibbs `ℝ^d`, elliptic `E.fullU`, Riemannian) and the reduced conditional bridge

See `STATEMENTS_R30_T.md`.  The generic theorems are `rd_semigroup_cc_exists_cont` (G1), `rd_isFellerC0_iff_decay` (G2)
(`Continuity.lean`) and `rd_initial_condition` (G3) (`Init.lean`).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal ZeroAtInfty CompactlySupported

namespace MarkovTriple.Stochastic.R30T

open MarkovTriple.BGL MarkovTriple.BGL.Instances MarkovTriple.BGL.Instances.GibbsRd MarkovTriple.Stochastic
  MarkovTriple.Stochastic.R24 MarkovTriple.Stochastic.R27 MarkovTriple.Stochastic.R29

section Gibbs

variable {d : ℕ} (G : GibbsRdData d)

/-- G1 for `ℝ^d` Gibbs -/
theorem gibbsRdFull_semigroup_cc_exists_cont (t : ℝ≥0) (f : C_c(Rd d, ℝ)) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∃ g : C(Rd d, ℝ), (∀ x, |g x| ≤ C) ∧
      (G.gibbsRdFull_unconditional.toDiffusionTriple.semigroup t
        (ccL2 G.gibbsRdFull_unconditional.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[G.gibbsRdFull_unconditional.toDiffusionTriple.μ] g :=
  rd_semigroup_cc_exists_cont G.gibbsRdFull_unconditional rfl rfl t f hC

theorem gibbsRdFull_isFellerC0_iff_decay :
    IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (f : C_c(Rd d, ℝ)) (g : C(Rd d, ℝ)),
      (G.gibbsRdFull_unconditional.toDiffusionTriple.semigroup t
        (ccL2 G.gibbsRdFull_unconditional.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[G.gibbsRdFull_unconditional.toDiffusionTriple.μ] g →
        Tendsto g (cocompact (Rd d)) (𝓝 0) :=
  rd_isFellerC0_iff_decay G.gibbsRdFull_unconditional rfl rfl

/-- local ellipticity of the Gibbs carré du champ (`Γ = |∇|²`) -/
lemma gibbsRdFull_hell : ∀ R : ℝ, ∃ c : ℝ, 0 < c ∧ ∀ g : Rd d → ℝ, Sm g → ∀ x : Rd d, ‖x‖ ≤ R →
    c * ∑ i, pderiv g i x ^ 2 ≤ G.gibbsRdFull_unconditional.toDiffusionTriple.ΓA g g x := by
  intro R
  refine ⟨1, one_pos, fun g hg x _ => ?_⟩
  have h1 : G.gibbsRdFull_unconditional.toDiffusionTriple.ΓA g g = G.toEll.Γ g g := G.toEll.ΓA_eq hg hg
  rw [h1, G.toEll_Γ]
  simp [Gr, sq]

theorem gibbsRdFull_hinit (hV : HessGe G.V 0)
    (hF : IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple)
    (x : Rd d) (f : C_c(Rd d, ℝ)) :
    Tendsto (fun t : ℝ≥0 => Qop hF t f x) (𝓝[>] 0) (𝓝 (f x)) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hδt⟩ := rd_initial_condition G.gibbsRdFull_unconditional rfl rfl
    (G.gibbsRdFull_CD_unconditional hV) (gibbsRdFull_hell G) f x hε
  refine ⟨δ, hδ, fun {t} _ ht => ?_⟩
  have htδ : t < δ := by
    rw [NNReal.dist_eq] at ht
    simpa using ht
  have := hδt t htδ (Qop hF t f).toContinuousMap (Qop_ae hF t f)
  rw [Real.dist_eq]
  exact this

/-- R29 `gibbsRdFull_bridge_of_feller` with the initial-condition hypothesis (d) discharged (convex `V`). -/
noncomputable def gibbsRdFull_bridge_of_feller_ac (hV : HessGe G.V 0)
    (hF : IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple)
    (hac : ∀ s : ℝ≥0, 0 < s → ∀ x, fellerKernelInf hF s x ≪ G.gibbsRdFull_unconditional.toDiffusionTriple.μ) :
    MarkovProcessBridge G.gibbsRdFull_unconditional.toDiffusionTriple :=
  gibbsRdFull_bridge_of_feller G hF hac (fun x f => gibbsRdFull_hinit G hV hF x f)

end Gibbs

section Ell

variable {d : ℕ} (E : EllData d) (R : Riemannian.RiemData d)

theorem fullU_isFellerC0_iff_decay :
    IsFellerC0 E.fullU.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (f : C_c(Rd d, ℝ)) (g : C(Rd d, ℝ)),
      (E.fullU.toDiffusionTriple.semigroup t (ccL2 E.fullU.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[E.fullU.toDiffusionTriple.μ] g → Tendsto g (cocompact (Rd d)) (𝓝 0) :=
  rd_isFellerC0_iff_decay E.fullU rfl rfl

theorem riemFull_isFellerC0_iff_decay :
    IsFellerC0 R.riemFull_unconditional.toDiffusionTriple ↔ ∀ (t : ℝ≥0) (f : C_c(Rd d, ℝ)) (g : C(Rd d, ℝ)),
      (R.riemFull_unconditional.toDiffusionTriple.semigroup t
        (ccL2 R.riemFull_unconditional.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[R.riemFull_unconditional.toDiffusionTriple.μ] g → Tendsto g (cocompact (Rd d)) (𝓝 0) :=
  rd_isFellerC0_iff_decay R.riemFull_unconditional rfl rfl

theorem fullU_semigroup_cc_exists_cont (t : ℝ≥0) (f : C_c(Rd d, ℝ)) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∃ g : C(Rd d, ℝ), (∀ x, |g x| ≤ C) ∧
      (E.fullU.toDiffusionTriple.semigroup t (ccL2 E.fullU.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[E.fullU.toDiffusionTriple.μ] g :=
  rd_semigroup_cc_exists_cont E.fullU rfl rfl t f hC

theorem riemFull_semigroup_cc_exists_cont (t : ℝ≥0) (f : C_c(Rd d, ℝ)) {C : ℝ} (hC : ∀ y, |f y| ≤ C) :
    ∃ g : C(Rd d, ℝ), (∀ x, |g x| ≤ C) ∧
      (R.riemFull_unconditional.toDiffusionTriple.semigroup t
        (ccL2 R.riemFull_unconditional.toDiffusionTriple f) : Rd d → ℝ)
        =ᵐ[R.riemFull_unconditional.toDiffusionTriple.μ] g :=
  rd_semigroup_cc_exists_cont R.riemFull_unconditional rfl rfl t f hC

end Ell

end MarkovTriple.Stochastic.R30T
