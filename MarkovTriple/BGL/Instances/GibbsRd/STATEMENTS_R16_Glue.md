# STATEMENTS R16 Glue (Armstrong): proof of `EllData.EllReg` for all d (written BEFORE proofs)

File `EllRegProof.lean`, namespace `MarkovTriple.BGL.Instances.GibbsRd`.

G1 `EllData.veryWeakSol_of_mu {u h} (hu : MemLp u 2 E.μ ...)`: if `∀ a ∈ A₀ d, ∫ u·L a dμ = ∫ h·a dμ` then `E.VeryWeakSol u h`
   (`μ = Z⁻¹ w dx`, `integral_μ`; multiply by `Z`).
G2 `EllData.chain_sobolev`: for a chain as in `EllReg` (length n), `∀ j k, k + j ≤ n → Sobolev j (x k)`
   (j=0: `locL2_of_memLp`; j=1: Friedrichs `sobolev_one_of_veryWeak`; j→j+2: `interior_sobolev` with `h = x_k − x_{k+1}`).
G3 `EllData.ellReg : E.EllReg` (n := m + d; Sobolev embedding `sob_contDiff_rep` via `sobolev_iff_hasSobL2`, `HasSobL2.toL1`;
   a.e. volume ⇒ a.e. μ by `withDensity_absolutelyContinuous`).
G4 `EllData.weakHypo_unconditional : E.WeakHypo`, `EllData.f8_unconditional : E.F8`.
No change to `EllReg`/`WeakHypo`/`F8` definitions.
