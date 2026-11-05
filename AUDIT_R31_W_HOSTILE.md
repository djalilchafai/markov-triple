# Audit R31 Stream W (hostile): Core2 negative half at lam = 2

Audited: merge of `worktree-agent-aecd6400ef5bf36bf` (freeze aa14fad, proofs a5b7e29) onto the R30 base 5e96709.

## Verdict: ACCEPT

## Checks
1. `lake build` (cached main build copied in, packages symlinked): exit 0, 1916 log lines, 0 occurrences of warning/error/sorry.
2. `grep sorry|set_option|native_decide|axiom` over `Core2/W/*.lean`: only the word "axioms" in `#print axioms` lines. `#print axioms` for `not_core2L_of_pair`, `deficiency_pair_two`, `not_core2L_two`, `lipschitz`, `ode_series_cc`: propext, Classical.choice, Quot.sound only. `scripts/check_frozen.py`: OK.
3. Git history: aa14fad touches exactly `STATEMENTS_R31_W.md` + `frozen-manifest.json` (+5 lines, one new `proposed` entry). a5b7e29 only rehashes that same entry (manifest diff vs main = that single entry). The Status section was appended in the proof commit (10 lines, frozen part unchanged). Frozen names/statements match the delivered code verbatim (W1-W4).
4. Soundness.
   * `Core2L lam` vs `FullTriple.Core2` (Converse.lean:237): same quantifier structure (for each a in A0 there are b_n in A0 with (1-L)b_n -> a and L(1-L)b_n -> La in L2). `LLₗ T b` = `Lcls (L b)`, i.e. L(L b): matches `gL lam (gL lam b)`. Lp convergence of `cls`/`Lcls` is equivalent to eLpNorm -> 0 of the pointwise difference. `gL (3/2) = goL` is proved (`gL_three_halves`); 2*lam+1 = 4 matches. goA0 is the same A0 as goFullTriple. The constant factor 3/4 (unnormalised weight) only rescales every eLpNorm, so convergence is unaffected; harmless. The identification `Core2L (3/2) <-> goFullTriple.Core2` is not formalised (stated honestly by the authors).
   * Non-vacuity: `Core2L lam` is not definitionally false (a = 0 is witnessed by b = 0; nothing degenerate in gL, which uses `deriv` on smooth functions). The negation is derived from a genuine pair, so no trivialisation. Re-derived on paper: for b in A0, c = (1-L)b in A0, pairing (c, g = w - Lh) + (Lc, h) = int c w - int c Lh + int Lc h = int c w (symmetry of L between compactly supported c and smooth h, via cut-off; Lean `key`) = int b w - int Lb w = int b w - int b Lw = 0 (Lw = w on supp b). Passing to the limit by Cauchy-Schwarz gives int a w = 0 for every a in A0, contradicting the test function from `exists_test` (w != 0). Only g, h in L2 are used (a w is compactly supported). Symmetry `sym_A₀L` is proved for every real lam with weight (1-x^2)^(lam-1/2).
   * lam = 2 construction on paper: L_2 = s f'' - 5x f' (s = 1-x^2); indicial exponents at x = 1 from `gL_pow`: r(2r+3) = 0, i.e. 0 and -3/2. w = s^(-3/2) A with (1-x^2)A'' + xA' + 2A = 0, A(0)=1, A'(0)=0 gives Lw = w; recurrence cc_{n+2} = cc_n (n^2-2n-2)/((n+1)(n+2)) consistent; |cc_n| = O(n^(-5/2)) so A is Lipschitz at +-1. w^2 rho_2 = s^(-3/2) A^2 is not integrable (w not in L2, consistent with limit-point at lam = 2). h = -(A(1)/2) s^(-1/2): h^2 rho_2 = c^2 s^(1/2) bounded; w - L_2 h = (A - A(1)) s^(-3/2) + (3A(1)/2) s^(-1/2) weighted-bounded (the s^(-3/2) singularity cancels). w(0) = 1 so w != 0. Consistent with the heuristic 3/2 <= lam < 7/2 and with the existing `goFullTriple_not_core2` at 3/2 (same mechanism, parametric version of `go_not_core2_of_pair`).
5. Honesty: STATEMENTS "SCOPE"/"NOT claimed", GAPS "Round 31, Stream W", ERRATA R31-W-1/2/3 all state that there is no FullTriple for lam = 2, that `Core2L` is a transcription and not `FullTriple.Core2`, that ESA at lam = 2 is not proved, and that the 3/2 <= lam < 7/2 threshold and the positive half remain unproved. No overclaim found.

## Findings (severity ranked)
* HIGH / MEDIUM: none.
* LOW-1: `Core2L (3/2) <-> goFullTriple.Core2` is not a Lean theorem; the link to the 3/2 result rests on inspection (done above). Documented by the authors.
* LOW-2: module docstrings call `Core2L` "the literal statement of FullTriple.Core2"; with the recorded caveats this is acceptable (literal for the operator, not the structure). No change made.
* INFO: GAPS wording "first non-3/2 instance of the heuristic" is correct and scoped to lam = 2.
* INFO (process): my first background build attempt, before the cache copy, began materialising packages in the worktree; it was stopped, the partial `.lake` removed and replaced by the cached build. No repo effect.

No doc changes were needed.
