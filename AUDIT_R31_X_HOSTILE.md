# Hostile audit, Round 31 Stream X (merge of worktree-agent-aef56ec53167685f6; freeze 9844663, proofs d505ab4)

## Verdict: ACCEPT

## Checks
1. `lake build` (full, from copied main build): success, 9581 jobs, 0 warnings, 0 errors in the whole log.
2. R31X files: no `sorry`, `set_option`, `native_decide`, `axiom` (only the word in `#print axioms`). Axioms for all 4 theorems: propext, Classical.choice, Quot.sound. `scripts/check_frozen.py`: OK.
3. History: 9844663 touches only STATEMENTS_R31_X.md and frozen-manifest.json (one entry, +5 lines); no Status section before proofs. d505ab4 adds Status, re-hashes only its own entry (manifest diff vs main: only the R31X entry, status proposed). Statements text between commits changed only by appended Status.
4. Soundness of `rd_isFellerC0_iff_cutoff`: proof is positivity (`semigroup_mono`) + squeeze |P_t f| <= C P_t phi, built on R30T `rd_isFellerC0_iff_decay`. No circularity (R31X imports R30T; R30T does not import R31X). Hypotheses `S.A = Afull d`, `S.A₀ = A₀ d` are non-vacuous: the three instance corollaries discharge them by `rfl` and compile. Existence of a continuous representative (so that the quantification over g is not vacuous) is supplied by R30T `rd_semigroup_cc_exists_cont`, used in the proof. The statement is an iff with the genuine R30T decay property, so it is neither weaker nor trivially true.
5. Paper check of the V = e^{x^2} claim (d=1, L = f'' - V' f'): V'' = (2+4x^2)e^{x^2} >= 2. Scale density s' = e^{V}, so s(infinity) = infinity (not attracting); speed density m' = e^{-V}. Feller/Karlin-Taylor: with s(infinity) = infinity, infinity is an entrance boundary iff int^infty s(y) m(dy) < infinity; s(y) ~ e^{V}/V', so this is int^infty dy/V'(y) = int e^{-y^2}/(2y) dy < infinity. Correct. For an entrance boundary the process can be started from infinity, so P_t f(x) tends to int f dnu_t (an entrance law, positive for f >= 0 nontrivial) as x -> infinity, i.e. decay fails (and the diffusion is still conservative). The reasoning is sound. GAPS and ERRATA R31-X-1 label it "informal / heuristic / not formalised / no formal proof claimed"; it is not presented as a theorem. The frozen text says "indicates ... FALSE" and "NO formal proof of the failure is claimed". OK.
6. Beyond-proved claims: none found.

## Findings
- LOW: GAPS/ERRATA say a growth hypothesis on grad V "would be needed" (e.g. Lipschitz). This reads as necessity; only sufficiency-flavoured plausibility is supported (Lipschitz grad V gives int 1/V' = infinity, excluding entrance, but decay is not proved). Hedged by "e.g."; no change made.
- LOW: the frozen text gives the three instance corollaries only schematically (the explicit statements appear in Cutoff.lean); they follow by `rfl` from the generic theorem, so no deviation.
- LOW: the delivered result is a reduction only; decay / IsFellerC0 for strongly convex V remains open and is honestly recorded as such.

No CRITICAL, HIGH or MEDIUM findings. No doc edits needed.
