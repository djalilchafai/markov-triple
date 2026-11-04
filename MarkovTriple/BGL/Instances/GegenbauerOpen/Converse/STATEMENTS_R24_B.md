# STATEMENTS R24-B -- converse of BGL Prop. 3.3.17 for `goFullTriple` (non-complete, CD(3,4))

Frozen BEFORE proofs.  Lean statements: `Converse/Statements.lean` (Prop-valued defs `R24B_memLp_L`, `R24B_converse`, `R24B_go_statement`).
Proofs: `Converse/Main.lean`.

## Question
Does "`f in A`, `f in L^2`, `Gamma(f), Gamma_2(f) in L^1`, CD  ==>  `[f] in D(Lbar)`, `Lbar[f] = [Lf]`" need completeness (Def. 3.3.9)?
R20: `FullTriple.mem_domain_of_Gamma2_direct` assumes completeness; `goFullTriple` is not complete (R23).

## Answer plan (route (a), elementary, no ESA/Core2/Weyl-regularity beyond F10 already in the structure)
CD(rho,n) with n < infinity says `Gamma_2(f) >= rho Gamma(f) + (1/n)(Lf)^2`, so `(Lf)^2 <= n (Gamma_2(f) - rho Gamma(f))` in L^1: `Lf in L^2`
directly.  Then F10 (ESA) + maximal-domain lemma (`mem_domain_of_maximal`) gives the domain.  Completeness is only needed for `n = infinity`.

* (S1) `R24B_memLp_L T`: `n != oo`, `CD rho n`, `f in A`, `Gamma f, Gamma_2 f in L^1`  ==>  `Lf in L^2`.   (every FullTriple)
* (S2) `R24B_converse T`: the full converse (same conclusion as `mem_domain_of_Gamma2_direct`).        (every FullTriple)
* (S3) `R24B_go_statement`: S2 for `goFullTriple` using `goFullTriple_CD` (n = 4).  Hence no counterexample (option (b)) exists.

Proof statements: `theorem FullTriple.memLp_L_of_Gamma2_finite : R24B_memLp_L T`, `theorem FullTriple.mem_domain_of_Gamma2_finite : R24B_converse T`,
`theorem goFullTriple_mem_domain_of_Gamma2 : R24B_go_statement`.

## DIFFERENCE FROM BGL
BGL Prop. 3.3.17 (converse) is stated for CD(rho, infinity) with ESA/ergodicity and tacitly uses Core2 (ERRATA R15-1).  For finite n the
dimensional term gives `Lf in L^2` pointwise, so neither Core2 nor completeness nor ergodicity is needed (ESA = F10 only).  BGL's hypotheses
are not wrong but the statement is stronger than needed in finite dimension.  For `n = infinity` without completeness the question remains open here
(`goFullTriple` has finite n, so it does not bear on it).  No gap in BGL's hypotheses is exposed by `goFullTriple`: the converse HOLDS there.
