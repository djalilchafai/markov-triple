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

## (vi) Unconditional corollaries (files `GibbsRd/Unconditional.lean`, `Riemannian/Unconditional.lean`)
Gibbs (`G : GibbsRdData d`, `HessGe G.V ρ`): `gibbsRd_poincare_unconditional (0<ρ) : PI (1/ρ)`, `gibbsRd_spectralGap_unconditional`,
`gibbsRd_expDecay_unconditional`, `gibbsRdFull_unconditional : FullTriple (Rd d)`, `gibbsRdFull_CD_unconditional : CD ρ ∞`,
`gibbsRdFull_poincare_unconditional`, `gibbsRdFull_logSobolev_unconditional (0<ρ) : LS (1/ρ) 0` (via `FullTriple.logSobolev_unconditional`),
`gibbsRdFull_gradient_bound_noHyp (0 ≤ ρ)`, `gibbsRdFull_hasGradientBound_unconditional`.
Riemannian (`R : RiemData d`, `R.Curv ρ`): `riem*_unconditional` same list; `confRiem_*_unconditional` with ρ = 2
(PI (1/2), spectral gap 2, exp decay 2, CD 2 ∞, LS (1/2) 0, HasGradientBound 2).
