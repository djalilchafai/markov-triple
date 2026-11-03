# AUDIT R16 Glue (self-attack, Armstrong method)

Target: `EllData.ellReg : E.EllReg` for every `d` (`EllRegProof.lean`), then `weakHypo_unconditional`, `f8_unconditional`, and
`Unconditional.lean` files (Gibbs `ℝ^d`, Riemannian chart, `confRiem`).  Statements fixed in `GibbsRd/STATEMENTS_R16_Glue.md` before the proofs;
no erratum was needed (statements unchanged).  `EllReg`/`WeakHypo`/`F8` definitions untouched.

## Attacks
1. Non-vacuity of `EllReg`: quantifier order `∀ m ∃ n ∀ chain`.  Chains exist (constant chain `x_k = c` satisfies the weak equations for
   `c` constant only if `L a` integrates to 0, which holds by symmetry; the F8 reduction in `RegReduction.lean` produces real chains from
   `R^k Φ`).  `n := m + d` depends on `m` and `d` only (not on the chain).  Proof uses only `x_0..x_n`.
2. `Z` factors: `veryWeakSol_of_mu` multiplies the `μ`-equation by `Z` using `integral_μ` (`μ = dens dx`, `dens = w/Z`); `Z>0` is proved in `Ell.lean`.
3. Representative: the Sobolev embedding gives a.e.-`volume` equality; transferred to `μ` by `μ ≪ volume` (`withDensity_absolutelyContinuous`).
   `ContDiff ℝ m` as demanded, exactly as in `EllReg`.
4. `d = 0`: `n = m`; the proof is uniform (Friedrichs/E3 statements hold for `d=0`); `ellReg_of_dim_zero` also exists and is consistent.
5. Induction bookkeeping: `Sobolev j (x k)` for `k + j ≤ n`; base `j=0` (L2loc from `MemLp`), `j=1` (Friedrichs, needs `LocL2 h`, `h = x_k - x_{k+1}`),
   step `j+2` from `j` via `interior_sobolev j` with `h ∈ H^j` (both `x_k, x_{k+1} ∈ H^j` as `k+1+j ≤ n`).  At `k=0, j=n=m+d`: `HasSobL2 (m+d)`.
6. `LocL2` is `MemLp f 2 (volume.restrict K)`, requiring a.e.-measurability w.r.t. `volume`; obtained from `MemLp … E.μ` via `μ`-vs-Lebesgue
   comparison in `locL2_of_memLp` (existing, audited by E-agents).
7. The hypotheses of `interior_sobolev` (`hg`, `hgL`) come from `Sobolev 1 (x k)` (weak derivatives with `LocL2`).

## Attack surface (for the hostile auditor)
* `Sobolev` / `WeakDeriv` / `VeryWeakSol` definitions (EllipticDefs/EllipticWeakForm): is `VeryWeakSol` the right equation (`∫ u L a w = ∫ h a w`)? is `L a` for `a ∈ A₀` the right adjoint-form (symmetry of `L` w.r.t. `w dx`)?
* `A₀ d` = smooth compactly supported test functions: matches the `a ∈ A₀` in `EllReg`.
* Correctness of `interior_sobolev` (E3C) and `sobolev_one_of_veryWeak` (Friedrichs) — proved by other agents, trusted here (axioms checked).
* `sobolev_iff_hasSobL2`, `sob_contDiff_rep_L2` embedding order `m + d`.
* Unconditional corollaries only reuse conditional theorems with `weakHypo_unconditional`, `f8_unconditional`; LSI via `FullTriple.logSobolev_unconditional` (needs `IsProbabilityMeasure`, supplied by `EllData` instance).
* Name `gibbsRdFull_gradient_bound_noHyp` (the name `..._unconditional` was already taken by the version with explicit WeakHypo/F8).
