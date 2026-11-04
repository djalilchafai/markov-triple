import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWCut
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWHardy
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWHess

/-!
# `Core2` and the unconditional converse of BGL Prop. 3.3.17 on `ℝ^d` under `GrowHess3` (R19, Stream A5, targets C3, C5)

Statements: `STATEMENTS_R19_Core2Rd.md`.  Hypotheses: `Hess V ≥ ρ` (any `ρ`, the curvature condition `CD(ρ,∞)` of the converse) and
`GrowHess3` (`|∂²V|, |∂³V| ≤ C(1 + |∇V|₁`); NO bound on `∂²V`, `∂³V`, no growth restriction on `∇V` (e.g. `V = Σ xᵢ⁴/4 + xᵢ²/2`).
Proof: resolvent solution `v` (R18), `∇v ∈ L²` (R18 Caccioppoli), `Hess v ∈ L²` (`memLp_hess_resolvent_free`, cut-off Bochner `Γ₂ ≥ ρΓ`),
the Hardy weighted jets (`memLp_V_mul_of_hardy`) and the weighted cut-off commutators (`cutoff_ZL_w`).
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.BGL (FullTriple DiffusionTriple pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- **C3**: the weighted jets of `v` lie in `L²(μ)` (`GrowHess3`): `∂ₖV v`, `∂ₖV ∂ᵢv`, `∂ⱼV (∂ₖV v)`. -/
theorem resolvent_weighted_L2 (hgr : G.GrowHess3) {v : Rd d → ℝ} (hv : Sm v) (h0 : MemLp v 2 G.toEll.μ)
    (h1 : ∀ i, MemLp (pderiv v i) 2 G.toEll.μ) (h2 : ∀ i j, MemLp (pderiv (pderiv v i) j) 2 G.toEll.μ) :
    (∀ k, MemLp (fun x => pderiv G.V k x * v x) 2 G.toEll.μ) ∧
    (∀ k i, MemLp (fun x => pderiv G.V k x * pderiv v i x) 2 G.toEll.μ) ∧
    (∀ j k, MemLp (fun x => pderiv G.V j x * (pderiv G.V k x * v x)) 2 G.toEll.μ) := by
  obtain ⟨B, hB⟩ := hgr.laplace_le
  have hΔ : ∀ x, ∑ i, pderiv (pderiv G.V i) i x ≤ Gr G.V G.V x / 4 + B := fun x => by
    simpa [Gr, sq] using hB x
  obtain ⟨C2, hC2⟩ := hgr.hess
  have W1 : ∀ k, MemLp (fun x => pderiv G.V k x * v x) 2 G.toEll.μ := fun k =>
    G.memLp_V_mul_of_hardy hv h0 h1 hΔ k
  have W2 : ∀ k i, MemLp (fun x => pderiv G.V k x * pderiv v i x) 2 G.toEll.μ := fun k i =>
    G.memLp_V_mul_of_hardy (hv.pderiv i) (h1 i) (h2 i) hΔ k
  refine ⟨W1, W2, fun j k => ?_⟩
  have hf : Sm (fun x => pderiv G.V k x * v x) := (G.smooth.pderiv k).mul hv
  have hf1 : ∀ i, MemLp (pderiv (fun x => pderiv G.V k x * v x) i) 2 G.toEll.μ := by
    intro i
    have e : pderiv (fun x => pderiv G.V k x * v x) i =
        fun x => pderiv (pderiv G.V k) i x * v x + pderiv G.V k x * pderiv v i x :=
      funext fun x => pderiv_mul' (G.smooth.pderiv k) hv i x
    rw [e]
    exact (memLp_mul_growth ((G.smooth.pderiv k).pderiv i).continuous.aestronglyMeasurable
      (fun x => hC2 x k i) h0 W1).add (W2 k i)
  exact G.memLp_V_mul_of_hardy hf (W1 k) hf1 hΔ j

/-- **C5 (main)**: `Core2` for the Gibbs Full Markov triple on `ℝ^d` under `Hess V ≥ ρ` and `GrowHess3`. -/
theorem gibbsRd_core2_w {ρ : ℝ} (hρ : HessGe G.V ρ) (hgr : G.GrowHess3) :
    G.gibbsRdFull_unconditional.Core2 := by
  intro a
  have ha : a.1 ∈ A₀ d := a.2
  obtain ⟨v, hv, hv2, hL⟩ := G.exists_resolvent_smooth ha
  have h1 := fun i => G.memLp_grad_resolvent hv ha hv2 hL i
  have h2 := fun i j => G.memLp_hess_resolvent_free hv ha hv2 hL hρ i j
  obtain ⟨W1, W2, W3⟩ := G.resolvent_weighted_L2 hgr hv hv2 h1 h2
  have haL : MemLp a.1 2 G.toEll.μ := ha.1.continuous.memLp_of_hasCompactSupport ha.2
  have hLvf : Lr G.V v = fun x => v x - a.1 x := funext hL
  have hLa : Lr G.V a.1 ∈ A₀ d := by
    have := G.toEll.L_mem ha
    rwa [G.toEll_L ha.1] at this
  have hLaL : MemLp (Lr G.V a.1) 2 G.toEll.μ := hLa.1.continuous.memLp_of_hasCompactSupport hLa.2
  have hLv : MemLp (Lr G.V v) 2 G.toEll.μ := by rw [hLvf]; exact hv2.sub haL
  have hLLvf : Lr G.V (Lr G.V v) = fun x => (v x - a.1 x) - Lr G.V a.1 x := by
    funext x
    have e : Lr G.V v = fun y => v y + (-1 : ℝ) * a.1 y := by rw [hLvf]; funext y; ring
    rw [e, Lr_add_smul hv ha.1 (-1) x, hL x]; ring
  have hLLv : MemLp (Lr G.V (Lr G.V v)) 2 G.toEll.μ := by
    rw [hLLvf]; exact (hv2.sub haL).sub hLaL
  have hLv1 : ∀ i, MemLp (pderiv (Lr G.V v) i) 2 G.toEll.μ := fun i => by
    have e : pderiv (Lr G.V v) i = fun x => pderiv v i x - pderiv a.1 i x := by
      funext x
      rw [hLvf]
      exact pderiv_sub' hv ha.1 i x
    rw [e]
    exact (h1 i).sub ((A₀.pderiv_mem ha i).1.continuous.memLp_of_hasCompactSupport (A₀.pderiv_mem ha i).2)
  have hWL : ∀ k, MemLp (fun x => pderiv G.V k x * Lr G.V v x) 2 G.toEll.μ := fun k => by
    have e : (fun x => pderiv G.V k x * Lr G.V v x) =
        fun x => pderiv G.V k x * v x - pderiv G.V k x * a.1 x := by
      funext x; rw [hLvf]; ring
    rw [e]
    have hVa : MemLp (fun x => pderiv G.V k x * a.1 x) 2 G.toEll.μ :=
      ((G.smooth.pderiv k).continuous.mul ha.1.continuous).memLp_of_hasCompactSupport ha.2.mul_left
    exact (W1 k).sub hVa
  exact G.core2_of_ZL hv hL (cutoff_ZL_w hgr hv hv2 h1 h2 hLv hLLv hLv1 W1 W2 W3 hWL)

/-- **C5: the converse of BGL Prop. 3.3.17 (p. 162), unconditional for Gibbs triples on `ℝ^d` with `GrowHess3`**
(any `ρ ∈ ℝ`; no bound on `∂²V`, `∂³V`). -/
theorem gibbsRd_mem_domain_of_Γ₂_w {ρ : ℝ} (hρ : HessGe G.V ρ) (hgr : G.GrowHess3) {f : Rd d → ℝ}
    (hf : f ∈ G.gibbsRdFull_unconditional.A) (hf2 : MemLp f 2 G.toEll.μ)
    (hG : Integrable (FullTriple.G G.gibbsRdFull_unconditional f f) G.toEll.μ)
    (hG2 : Integrable (G.gibbsRdFull_unconditional.toDiffusionTriple.Γ₂ f f) G.toEll.μ) :
    ∃ hF : hf2.toLp f ∈ G.gibbsRdFull_unconditional.toDiffusionTriple.generator.domain,
      ((G.gibbsRdFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 G.toEll.μ) :
        Rd d → ℝ) =ᵐ[G.toEll.μ] G.gibbsRdFull_unconditional.L f :=
  FullTriple.mem_domain_of_Γ₂ (G.gibbsRdFull_CD_unconditional hρ) (G.gibbsRd_core2_w hρ hgr) hf hf2 hG hG2

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
