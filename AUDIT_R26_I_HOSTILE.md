# AUDIT R26 Stream I (hostile) -- VERDICT: ACCEPT

Scope: `Theory/Extension/R26/{Core2Eigen,AxiomCheckR26I}.lean`, `Instances/Sphere/R26Core2.lean`, `STATEMENTS_R26_I.md`, ERRATA R26-I-1/2, GAPS R26-I.
Merged `worktree-agent-ab044be4375696fd4` (base 4aa67cd already present). Full `lake build` succeeded: 9487 jobs; no warnings seen in tail; grep: no `sorry`, `set_option`, `native_decide` in the R26 I files. `#print axioms` (own run via build output): all four theorems `propext, Classical.choice, Quot.sound`. `scripts/check_frozen.py`: OK.

## Findings (severity ranked)
* LOW-1 (doc). `core2_of_eigen'` is not in the frozen text (327e8a2). Disclosed in the Status section of STATEMENTS and in ERRATA R26-I-1 ("additive"). Sound: it is a trivial choice-wrapper of the frozen `core2_of_eigen`. OK.
* LOW-2 (doc). The "holds for lambda >= 7/2" half of the Gegenbauer heuristic is closer to a sketch than a guess, but the GAPS wording was terse ("plus 3/2-lambda from the inhomogeneous equation", omitting the analytic exponents 0,1 and the global gluing argument), and the Gamma-bounded-implies-bounded reason for non-completeness is loose. Fixed by an appended, clearly labelled auditor note in GAPS (heuristic status kept).
* LOW-3 (doc). Frozen statement file hash changed between 327e8a2 and 5bc377b, but only by 14 inserted lines (Status section), no deletion of frozen text; manifest entry updated accordingly, status "proposed". Acceptable.
* INFO. "Circle and ouBFull not done": true (no Core2 theorem for `circleFull` / `ouBFull`; `OU/Core2.lean` already proves `ouFull.Core2`, a different triple, so no overclaim). Location deviation (`Theory/Extension/R26/` instead of brief's `BGL/Extension/R26`) is disclosed at the top of STATEMENTS.

## Checks
(a) `Core2` (Converse.lean:237) is the real notion (b_n in A0 with (1-L)b_n -> a, L(1-L)b_n -> La). `core2_iff_orth` is the correct orthogonality form via `core2_iff_dense` (imported from R24). `core2_of_eigen` hypotheses are satisfiable (verified by `sFull_core2`) and non-contradictory; the proof computes Psi phi = (1+c)^2 [phi] genuinely. `sFull` is the real FullTriple (Compact.lean:75) on `Zon` with `AZ`, eigenfunctions `UZ k in AZ` (`UZ_mem`), `LZ (UZ k) = -k(k+2) UZ k` (`LZ_UZ`), density `dense_span_eZ`; the sphere is zonal S^3 (Gegenbauer lambda = 1). The conclusion `sFull.Core2` is nontrivial: `sFull` has A0 = AZ (smooth zonal), a genuine instance.
(b) Disclosed (LOW-1).
(c) 327e8a2 touches only STATEMENTS_R26_I.md and frozen-manifest.json; 5bc377b holds proofs/docs; hash current; no duplicate manifest entry.
(d) As above.
(e) Frobenius: L ~ 2t d^2 + (2lambda+1)d at x=1, L t^r = r(2r+2lambda-1)t^(r-1); (1-L)^2 u = 0 has exponents 0,1,1/2-lambda,3/2-lambda; t^r in L^2(t^(lambda-1/2)dt) iff 2r+lambda+1/2>0: r=1/2-lambda iff lambda<3/2, r=3/2-lambda iff lambda<7/2. So lambda in [3/2,7/2) gives 3 L^2 local solutions per endpoint in a 4-dim space => nonzero global L^2 solution w, i.e. non-Core2 by `core2_iff_orth` (consistent with the proved `goFullTriple_not_core2` at lambda=3/2, where the 3/2-lambda exponent is 0 with a log). For lambda >= 7/2 only analytic solutions are L^2, and integration by parts gives w=0. The threshold 7/2 is plausible and correct at sketch level; labelled heuristic: appropriate. Note lambda<3/2 also fails (even L is not ESA), not contradicting the text.
(f) Honest.

Verdict: ACCEPT. Only doc edit: GAPS.md auditor note.
