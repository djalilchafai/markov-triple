# Hostile audit, Round 29 Stream Q (Gegenbauer Frobenius / L2 exponents)

Verdict: **ACCEPT** (as a small, honest, parametric lemma package; the stream's headline goals are correctly reported as NOT done).

Method: merged worktree-agent-a73acabef25cce57a (c29ce8c, dc44f6c) on f0edf3a; read Frobenius.lean in full; hand-checked; `lake build` (whole repo, success, 0 warnings in log, 9536 jobs); `check_frozen.py` OK; `#print axioms` on all seven theorems (all `propext, Classical.choice, Quot.sound`, no `sorryAx`); grep for `sorry|set_option|native_decide` in the two Lean files: none.

## (a) Correctness / faithfulness
* `gL_pow` by hand: with t=1-x, f'=-r t^(r-1), f''=r(r-1)t^(r-2); (1-x²)f'' = r(r-1)(1+x)t^(r-1); -(2λ+1)x f' = (2λ+1)x r t^(r-1). Sum = r t^(r-1)((r-1)(1+x)+(2λ+1)x). Matches. Indicial bracket at x=1: 2(r-1)+2λ+1 = 2r+2λ-1. Matches.
* Symmetry: L_λ = (1-x²)f'' - (2λ+1)x f' = ρ^{-1}(ρ(1-x²) f')' with ρ=(1-x²)^(λ-1/2): ρ(1-x²)=(1-x²)^(λ+1/2), derivative = -(2λ+1)x(1-x²)^(λ-1/2). Correct, so ρ_λ is the Gegenbauer weight. `gL_three_halves` (proved, uses `ring`) gives gL(3/2)=goL, and weight (1-x²)^1 is the library's (1-x²) up to the constant 3/4. Consistent.
* L2 criterion: integrand (1-x)^(2r)(1-x)^(λ-1/2)(1+x)^(λ-1/2); (1+x)^μ bounded above and below on (0,1) (proved for both signs of μ); integrable iff 2r+λ-1/2>-1 iff 2r+λ+1/2>0. Correct.
* Non-vacuity: `pow_sq_integrable_iff` is stated with `IntegrableOn ... (Ioo 0 1)` (genuine integrability, not a Bochner integral value, no junk-value triviality). Proof goes through `intervalIntegral.integrableOn_Ioo_rpow_iff` with reflection and two-sided comparison. Restriction to (0,1) is the right near-endpoint formulation (x=-1 is symmetric; the interior is a bounded-weight region). Minor: the statement is for the half interval (0,1) not for "near 1" via a filter, but equivalent for this purpose.
* `exponent_*` theorems are pure linear arithmetic (`linarith`) restating inequalities; true but nearly trivial, and `exponent_regular_L2` takes the literal exponents 0 and 1. They are not linked formally to `gL_pow` (that 1/2-λ is a root of r(2r+2λ-1) is not a theorem; `gL_pow_indicial` is just `ring`).

## (b) Honesty of "not done"
* Verified: `Instances/GegenbauerOpen` (3295 lines total: Basic 249, Diffusion 142, Full/PreFull 352, Full/RegLocal 452, ESA/Prim 287, ESA/Weyl 280, ESA/Regularity 237, ...) is hard-wired to λ=3/2 (Basic header states "λ = 3/2"; constants 3/4, 4x, explicit primitives). The stream did not give up too early on a cheap route; the claim is true. The "about 4000 lines" figure includes Riemannian/R24/Go*; the GegenbauerOpen directory alone is 3.3k.
* Recommendation on a follow-up stream: parametrising in λ is feasible but LARGE and risky. Estimate: (i) Basic/Diffusion/Curvature parametric DiffusionTriple (weight (1-x²)^(λ-1/2), normalisation via Beta function): 2-3 streams-days, medium; (ii) PreFull/RegLocal/Sem/ESA for general λ>-1/2 (explicit primitives and the R24 series aa_n must be replaced by Gegenbauer polynomial / Frobenius series arguments): ~3-4k lines, high effort; (iii) positive Core2 for λ>=7/2 needs a new fourth-order weak regularity + Weyl argument (genuinely new maths, high risk); (iv) negative half for 3/2<λ<7/2 needs an explicit deficiency pair w (a pair of L2 local solutions at each endpoint glued, with log-resonance cases at half-integers), also new. Suggested staging: launch ONE follow-up limited to (i)+(negative half at a single convenient λ, e.g. λ=2 or 5/2, where the explicit solutions are elementary, e.g. algebraic in (1-x), avoiding logs), reusing Core2Q.gL_pow as the ingredient. Do not launch the full parametrisation of ESA/Full unless the threshold theorem is deemed a priority; the 7/2 positive half is the hard part and its value is uncertain (the heuristic could have caveats, see R26-I).
* The negative-half single-λ route avoids the FullTriple entirely if the Core2 statement can be phrased on the DiffusionTriple (check `core2_iff_orth` hypotheses first); this is the cheapest high-value follow-up.

## (c) The "4, 3, 2 L2 exponents" claim
* NOT a Lean theorem: only the per-exponent criteria are theorems. The counts, the identification of the Frobenius exponents of (1-L)²u=0 as {0,1,1/2-λ,3/2-λ} (a fourth-order equation; gL_pow handles one factor and only the leading term), and the log resonances (λ half-integer: differences between exponents integral) are prose. GAPS line 403 said "formalises exactly the exponent count"; that overstated. FIXED (relabelled, original text kept in spirit): GAPS now says the totals, identification and Frobenius theory are prose only. STATEMENTS_R29_Q.md already says "Only the action of one factor L and the L2 criterion are claimed formally, NOT the Frobenius theory", fine. The not-formalised wording elsewhere in GAPS (R26-I) is accurate.
* Note the exponent 1 in "0, 1 analytic" is a regular-series exponent, not an indicial root of L; correct as used.

## (d) Git history / freeze
* c29ce8c contains only STATEMENTS_R29_Q.md and the manifest entry; no Lean. Good. Manifest diff vs f0edf3a is only the own entry. check_frozen.py OK.
* LOW finding: the manifest sha256 was re-stamped in dc44f6c (758e...->b92f...) because a "Status (after proof)" section was appended to the frozen file after the freeze. Statement blocks are unchanged (diff confirms append-only), so no semantic weakening, but strictly the frozen hash no longer equals the freeze-commit hash. Left as is (not a doc relabel; noted for the record; status "proposed" entries tolerate this).
* Theorem statements in the Lean file equal the frozen statements (checked by eye, all seven).

## Findings by severity
* MEDIUM (fixed): GAPS wording "formalises exactly the exponent count" overstated; relabelled.
* LOW: manifest hash re-stamp after append of status section (see d).
* LOW: exponent_* theorems are trivial arithmetic and not formally tied to gL_pow roots; statement is on (0,1), not an explicit near-1 filter.
* INFO: ERRATA R29-Q-1/2 accurate; R29-Q-2 correctly says OPEN.
