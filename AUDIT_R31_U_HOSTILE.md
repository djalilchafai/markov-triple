# Hostile audit, Round 31 Stream U (merged f9b7c25 / 5494537 / baa149b)

Verdict: **ACCEPT**

## Checks
1. `lake build` (full, 9586 jobs): success, 0 warnings, 0 errors, 0 sorry in the log; all 19 `#print axioms` lines of `AxiomCheckR31U.lean`
   (every declaration listed: int3_le ... riemFull_bridge_of_feller_U) report exactly `[propext, Classical.choice, Quot.sound]`.
2. grep of `Stochastic/R31U/*`: no `sorry`, `set_option`, `native_decide`, `axiom`; no `hac` (R30T absolute-continuity hypothesis) anywhere.
   `python3 scripts/check_frozen.py`: OK.
3. History: f9b7c25 touches only `STATEMENTS_R31_U.md` and `frozen-manifest.json`; the manifest diff vs main is exactly one added entry
   (R31U statements file). Later commits touch the statements file only by appending the Status section (re-hashed own entry; check_frozen OK).
   Frozen statement bodies are unchanged.
4. Soundness.
   - U1 `reverse_poincare_sup`: finite mu, CD 0 inf, f in A0, |f|<=C a.e.; conclusion `2 t ΓA(Pt f)(Pt f) <= C^2` a.e. Sup-form only, consistent
     with the claim of the docs. Proof via the interpolation `Theta`, no extra hypotheses beyond the instance arguments.
   - U2/U3: hypotheses finite mu, IsOpenPosMeasure, hA, hA0, CD 0 inf, hell, and for U3 `hF : IsFellerC0`. U3's statement does not assume absolute
     continuity nor `hac`; its proof goes `kernel_null_compact` (cut-offs, L^2 contraction, Chebyshev with U2 Lipschitz bound, full support) then inner
     regularity. Not circular.
   - U4: instance theorems use `rd_kernel_ac` with `rfl rfl` (A = Afull, A0 = A0 d), `*_CD` (from hV / Curv 0), `gibbsRdFull_hell` / `ellData_hell`
     (R30T theorems, not assumptions) and probability measure instances (`G.toEll.μ`, `E.μ` are `IsProbabilityMeasure`, so finite; full support
     instances already exist since R29). `IsFellerC0` enters only via the explicit `hF`; no instance/def supplies it silently (grep: no occurrence
     other than `hF`).
   - Satisfiability: the hypotheses are the same as those of R30T (CD 0 inf, Hess V >= 0, Curv 0 are satisfied e.g. by the Gaussian case, where
     IsFellerC0 is available via the R30 decay criterion); not vacuous. Whether IsFellerC0 holds for a given non-Gaussian convex V remains open
     (item (a)), as honestly stated.
   - (d) pointwise initial condition: the bridges reuse R30T `*_bridge_of_feller_ac`, whose `hinit` comes from `rd_initial_condition` (theorem under
     CD 0 inf + hell); not assumed.
5. Deviations: ERRATA R31-U-3 discloses that instance `*_kernel_ac` carry `hV`/`hC` and `hF`. These are needed for the statement to typecheck
   (`fellerKernelInf hF ...` requires `hF`) and for CD(0,inf); they make the theorems more conditional than the frozen informal listing, but the
   frozen text listed those theorems only parenthetically without hypotheses, so this is a clarification, not a weakening of any displayed statement.
   Minor wording nit: ERRATA says hF is "needed for CD(0,inf)"; accurately hF is needed to form the kernel, hV/hC give CD(0,inf). Left as is.
6. Honesty: GAPS/ERRATA/Status state no unconditional MarkovProcessBridge for these triples (R31-U-2), only the sup-form of the reverse Poincare
   (R31-U-1), finite mu, CD(0,inf) only, 1-d gibbsFull not covered. No overclaim found.

## Findings
- INFO: wording nit on hF in R31-U-3 (above). No doc edits made.
- INFO: `reverse_poincare_sup` is an a.e. statement for A0 data; the Lipschitz consequence is obtained through hell + continuity, as documented.
- No LOW/MEDIUM/HIGH findings.
