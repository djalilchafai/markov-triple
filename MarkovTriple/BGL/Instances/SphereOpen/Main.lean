import Mathlib
import MarkovTriple.BGL.Instances.SphereOpen.Full
import MarkovTriple.BGL.Instances.SphereOpen.Support
import MarkovTriple.BGL.Theory.Interp.ExtMain

/-!
# Finite-`n` logarithmic Sobolev inequality on a non-compact state space (R17 Noncompact, N7-N9)

`oFull` (Full triple on `ZonO = (-1,1)`, not compact, finite measure) satisfies `CD(2,3)` (`oFull_CD`);
BGL Thm 5.7.4 (`FullTriple.logSobolev_dim_unconditional`, no compactness) then gives `LS(1/3, 0)`,
`C = (n-1)/(ρ n) = 1/3 < 1/ρ = 1/2`.  Statements: `STATEMENTS_R17_Noncompact.md`.
-/

open MeasureTheory Real Set Filter Topology
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)

namespace MarkovTriple.BGL.Instances.SphereOpen

open MarkovTriple.BGL.Instances.Sphere

/-- **N7**: the named input `FiniteDimInterpolation (ρ n/(n-1))` of Thm 5.7.4 is a theorem on `oFull`. -/
theorem oFull_finiteDimInterpolation :
    oFull.FiniteDimInterpolation (2 * ((3 : ℝ≥0∞).toReal / ((3 : ℝ≥0∞).toReal - 1))) :=
  oFull.finiteDimInterpolation_of_CD oFull_CD (by norm_num) (by norm_num) (by simp)

/-- **N8: BGL Thm 5.7.4 on a non-compact state space.**  `LS(1/3, 0)`: `Ent(f²) ≤ (2/3) ∫ Γ(f)` for
`f ∈ 𝒜₀` on the open zonal sphere `(-1,1)` (`CD(2,3)`, constant `(n-1)/(ρ n) = 1/3`). -/
theorem oFull_LS : oFull.toDiffusionTriple.LS (1 / 3) 0 := by
  have h := oFull.logSobolev_dim_unconditional (n := 3) (ρ := 2) (by norm_num)
    (by norm_num) (by simp) oFull_CD
  have e : MarkovTriple.BGL.dimLSConst 2 3 = 1 / 3 := by
    unfold MarkovTriple.BGL.dimLSConst
    rw [ENNReal.toReal_inv]
    norm_num
  rwa [e] at h

/-- the improvement over the `n`-independent constant `1/ρ = 1/2` of Prop. 5.7.1. -/
theorem oFull_LS_dim_lt : (1 / 3 : ℝ) < 1 / 2 := by norm_num

/-- **N9 (non-degeneracy)**: `Γ ≠ 0` a.e.: the witness `f(x) = x` has `Γ(f) = 1 - x² > 0` everywhere on
`(-1,1)`, so `Γ(f) =ᵐ 0` fails (`μO` is a probability measure). -/
theorem oFull_Γ_ne_zero :
    ∃ f ∈ oFull.A₀, ¬ (oFull.Γ f f =ᵐ[oFull.μ] 0) := by
  have hf : (fun x : Zon => x.1) ∈ AZ := by
    show Sm (Sphere.ext (fun x : Zon => x.1))
    exact (by simpa [Sphere.ext, cosZ] using contDiff_cos : Sm fun θ => cos θ)
  refine ⟨(fun x : Zon => x.1) ∘ jO, comp_mem_AO hf, fun h => ?_⟩
  obtain ⟨x, hx⟩ := h.exists
  have e : Sphere.ext (fun x : Zon => x.1) = cos := by funext θ; simp [Sphere.ext, cosZ]
  have hx' : GZ (fun x : Zon => x.1) (fun x : Zon => x.1) (jO x) = 0 := by
    have h1 : GO ((fun x : Zon => x.1) ∘ jO) ((fun x : Zon => x.1) ∘ jO) x = 0 := hx
    rwa [GO_comp hf hf] at h1
  have hlt : -1 < (x : Zon).1 ∧ (x : Zon).1 < 1 := x.2
  simp only [GZ, Sphere.mk, dG, e, Real.deriv_cos] at hx'
  have hs : 0 < sin (arc (jO x)) := by
    have : sin (arccos (x : Zon).1) = √(1 - (x : Zon).1 ^ 2) := Real.sin_arccos _
    show 0 < sin (arccos (x : Zon).1)
    rw [this]
    apply Real.sqrt_pos.2
    nlinarith [hlt.1, hlt.2]
  nlinarith [mul_pos hs hs]

/-- **N9 (full support)**: every non-empty open subset of `(-1,1)` has positive `oFull.μ`-measure. -/
theorem oFull_μ_pos_of_open {U : Set ZonO} (hU : IsOpen U) (hne : U.Nonempty) : 0 < oFull.μ U :=
  μO_pos_of_open hU hne

end MarkovTriple.BGL.Instances.SphereOpen
