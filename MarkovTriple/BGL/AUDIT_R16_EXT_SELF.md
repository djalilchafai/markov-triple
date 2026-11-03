# AUDIT_R16_EXT_SELF -- self-attack on the extension step `ext` (BGL Thm 5.7.4, p. 272)

Statements: `Theory/Interp/STATEMENTS_R16_Ext.md` (written before the proofs; E1..E7 all proved as stated).
Files: `Theory/Interp/ExtBdd.lean`, `ExtChain.lean`, `ExtMain.lean`, `ExtAxiomCheck.lean`.

## 1. What was proved
* `Bdd T h` (h in A, |h|, Gamma h, |L h| essentially bounded); finite measure, CD(rho,n):
  `Bdd.domain` ([h] in D(L), via `mem_domain_of_ESA` = Prop 3.3.6(i)); `Bdd.integrable_Γ₂` (`integrable_Γ₂_of_domain`);
  `Bdd.integrable_ΓΓ` (reinforced inequality (3.3.6) `reinforced_cd`); `Bdd.comp` (smooth post-composition).
* `integral_exp_L_Γ_bdd` (5.7.7), `integral_exp_sq_L_bdd` (5.7.8, a=1/2), `integral_exp_Γ₂_ge_bdd` (5.7.11), `integral_exp_Γ₂_ge_bdd'` (5.7.12).
* `finiteDimExt` = the frozen field `ext`; `finiteDimInterpolation_of_CD`; `logSobolev_dim_unconditional`.
Route = the book's: for bounded f in A, [f] is in D(L), Gamma_2 is integrable with int Gamma_2 = int (Lf)^2 (Prop 3.3.17), and the
chain (5.7.6)-(5.7.12) is re-run with Green's formula `ibp_of_domain` instead of F7 on A_0.  No non-book idea was needed: the only
point the book leaves implicit is that the test function `e^g Gamma(g)` of (5.7.7) lies in D(E); it does, because
Gamma(Gamma g) <= 4 (Gamma_2(g) - rho Gamma(g)) Gamma(g) is integrable (book (3.3.6), p. 156).

## 2. Self-attack
* Vacuity of `ext`: the quantification is over all f in A with eps <= f <= eps+M, Gamma f <= B, |Lf| <= B (non-constant examples exist,
  e.g. 2 + sin on Gibbs/OU); nothing is assumed beyond the frozen field.  The conclusion was PROVED, not assumed.
* The two integrability hypotheses of the frozen field are not used (they are consequences of the proof); the theorem is therefore
  stronger than the field requires.  Cut Lambda: arbitrary `BE.Cut eps M`; only `Lambda smooth` (for `Bdd.comp`) and `Lambda = log` on the range
  (for `e^{Lambda f} = f`) are used.
* kappa above the true rate: kappa is exactly `rho n/(n-1)`; the theorem is not stated for other kappa.  `rho >= 0` is NOT needed for `ext`
  (only for the field `bdd`, via `entropyInterpolation`); positivity `rho > 0` is only for the LSI headline.
* n edge cases: `1 < n < infinity` only.  n = 1 (torus) and n = infinity are not covered here (n = infinity is `logSobolev_unconditional`).
* `IsFiniteMeasure`: required (bounded functions in L^2).  `FiniteDimInterpolation` is stated for arbitrary T; we prove it for finite
  mu only; infinite mu not claimed.
* a.e. vs. pointwise: `Pw g 1 (1/2)` is used as the representative of `e^{g/2}`; `integrable_Γ₂_of_domain` is applied to it with
  `Bdd` data obtained from `Bdd.comp`; `e^{Lambda f} = f` only a.e. and the final conversion uses `integral_congr_ae`.
* `Bdd.comp` bounds use the compact interval `[-K,K]` and a.e. membership; `K < 0` / measure zero are harmless (statements are a.e.).
* Copy of the algebra of `integral_exp_Γ₂_ge` (text-substituted copy, `ExtMain.lean`): same pointwise inequality `hpt` with the same coefficients.

## 3. Open / not done
`rho < 0`, infinite measure, n = 1.  Gibbs (R^d) LSI with n finite is not instantiated (no CD(rho,n) with n finite for Gibbs).

## 4. Attack surface for the independent hostile audit
1. `Bdd` definition (statement fidelity): "|L h| <= B" and "Gamma h <= B" share one constant B (harmless, but check `Bdd.bounds`).
2. `Bdd.integrable_ΓΓ`: the final chain of inequalities with `4 (Γ₂ - ρΓ) Γ <= 4 (|Γ₂| + |ρ|Γ) |B|` (sign of `Γ₂ - ρΓ` is not assumed).
3. `integral_exp_L_Γ_bdd`: `Γ(k)` bound via `Γ_prod_le`; `ibp_of_domain` hypotheses (`hQk` from `memQ_of_bdd`, proof irrelevance of `MemLp`).
4. `integral_exp_sq_L_bdd`: `integrable_Γ₂_of_domain` for `Pw g 1 (1/2)` (domain via `Bdd.comp`), coefficients `1/4, 1/8, 1/16` (identical to the A_0 proof).
5. `integral_exp_Γ₂_ge_bdd`: textual copy of `integral_exp_Γ₂_ge`; check the substitution `M_comb' / int_comb'` only.
6. `finiteDimExt`: matching with the frozen field (`ΓA` vs `G` is an abbreviation), `exp (Λ f) = f` a.e.
7. `logSobolev_dim_unconditional`: composes `logSobolev_dim_of_ext` (hypotheses: probability measure, rho > 0, 1<n<infty, CD).
