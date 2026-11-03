# STATEMENTS_R16_Ext -- the extension step `ext` of BGL Thm 5.7.4 (p. 272)

Status: PROVED as stated (E1-E7; Lean names: `Bdd.domain`, `Bdd.integrable_Γ₂`, `Bdd.integrable_ΓΓ`, `Bdd.comp`, `integral_exp_L_Γ_bdd`, `integral_exp_sq_L_bdd`, `integral_exp_Γ₂_ge_bdd(')`, `finiteDimExt`, `finiteDimInterpolation_of_CD`, `logSobolev_dim_unconditional`).  Changes only via a logged erratum in `ERRATA.md`.
Files: `Theory/Interp/Ext*.lean`.  Source: BGL p. 272, "by Proposition 3.3.6 and Lemma 3.3.16, (5.7.12) extends to
functions f in A which are bounded, together with Gamma(f) and Lf (such functions belong to D(L))".
Frozen target (NOT modified): `FullTriple.FiniteDimInterpolation T kappa` (Theory/LogSobolevDim.lean).

Standing hypotheses of every statement below: `T : FullTriple E`, `[IsFiniteMeasure T.mu]`, `hCD : T.CD rho n`,
`1 < n`, `n != infinity` (n finite, kappa = rho * (n.toReal/(n.toReal-1)) the book's constant).

## E1 (domain, BGL Prop 3.3.6(i)) `Bdd.memDomain`
`Bdd T h` := `h in T.A`, and exist `K B` with a.e. `|h| <= K`, `Gamma h <= B`, `|L h| <= B`.
For `Bdd T h`: `h in L^2`, `[h] in D(L)`, `Gamma h`, `Gamma_2 h` in `L^1`, `int Gamma_2 h = int (L h)^2`
(Prop 3.3.17 second paragraph, existing `integrable_Gamma2_of_domain`; needs `CD`).

## E2 (stability) `Bdd.comp`
`Bdd T h`, `psi : R -> R` smooth  ==>  `Bdd T (psi o h)`.

## E3 (5.7.7 for bounded g) `integral_exp_L_Gamma_bdd`
`Bdd T g` ==> `e^g Gamma(g,Gamma g)` integrable and
`int e^g Lg Gamma(g) = - int e^g Gamma(g,Gamma g) - int e^g Gamma(g)^2`.

## E4 (5.7.8 at a = 1/2) `integral_exp_sq_L_bdd`
`Bdd T g` ==> `int e^g (Lg)^2 = int e^g Gamma_2(g) + 3/2 int e^g Gamma(g,Gamma g) + int e^g Gamma(g)^2`.

## E5 (5.7.12 for bounded g) `integral_exp_Gamma2_ge_bdd`
`Bdd T g` ==> `kappa * int e^g Gamma(g) <= int e^g Gamma_2(g)`   (and the (5.7.11) form with the extra
`(4n-1)/(4(n+2)^2) int e^g Gamma(g)^2`).

## E6 (the field `ext`) `finiteDimExt`
Exactly the frozen field `ext` of `FiniteDimInterpolation T kappa`, for `kappa = rho * (n.toReal/(n.toReal-1))`
(the two integrability hypotheses of the field are not needed; they are consequences of E1/E3).

## E7 (headline) 
`FullTriple.finiteDimInterpolation_of_CD` (`0 <= rho`): `T.FiniteDimInterpolation (rho*(n/(n-1)))`.
`FullTriple.logSobolev_dim_unconditional` (`IsProbabilityMeasure`, `0 < rho`):  `T.LS (dimLSConst rho n) 0`
for every FullTriple (no compactness).

Not claimed: `rho < 0`; infinite measure; n = 1; n < 1.
