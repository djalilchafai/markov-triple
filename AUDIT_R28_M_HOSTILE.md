# AUDIT R28 Stream M (hostile, independent)

Target: merge of `worktree-agent-a17737caac06f1d52` (3 commits, tip 50ef7aa, base ee1c0fb). Verdict: **ACCEPT** (0 HIGH, 0 MEDIUM, 3 LOW/INFO doc items; one fixed here).

## Verification performed
* Merge fast and clean; `.lake/build` copied, packages symlink to absolute mathlib path; `lake build` succeeds (9518 jobs), whole log grepped: 0 "warning", 0 "sorry". (Pre-existing modules were cached; the 9 R28 modules plus AxiomCheck and root were rebuilt.)
* grep of `R28/*.lean`: no `sorry`, `set_option`, `native_decide`, `axiom` declarations (only `#print axioms` and a comment).
* `#print axioms` (AxiomCheckR28M, 19 lines, which cover `goMarkovProcessBridge`, `goKernelI_add`/`_zero`/`_bind`/`_isMarkov`, `goI_isFeller`, `goSG_one`, `goSemigroupI_restr`, `goKernel_rep`, `goMarkovProcessBridge_isMarkov/_support/_kernel_of_mem/_not_mem`, `ouBMarkovProcessBridge`, `goFull_bridge`, `lebesgueRdFull_bridge`, `sFull_bridge`, `circleFull_bridge`, `ouFull_bridge`): all exactly `propext, Classical.choice, Quot.sound`.

## (a) Is the bridge real and non-circular?  YES
* `goMarkovProcessBridge : MarkovProcessBridge goFullTriple.toDiffusionTriple` is the genuine structure of `MarkovProcessInterface.lean` (fields: kernel, measurable_kernel, kernel_zero, kernel_add, isSubMarkovKernel, rep, invariant). All proved, none by `sorry`/assumption.
* `rep` is stated against `goFullTriple.toDiffusionTriple.semigroup t (hL.toLp g)` for ALL bounded measurable `g ∈ L²(goμ)`; proof `goKernel_rep` transfers via `goRestr` and `goSemigroupI_restr` (a.e. transfer `ae_goμ_iff` along the measurable embedding). `kernel_zero`, `kernel_add`, `isSubMarkov` are exact pointwise for every `x ∈ ℝ` (case split `x∈[-1,1]` / frozen `δ_x`; checked the `goKernel_add` off-interval case: `δ_x.bind κ_t = κ_t x = δ_x`). Invariance proved by pulling back through `map_gj`.
* Not a tautology: kernels are `sgKernel goI_isFeller t` = Riesz-Markov measures of the continuous representatives `sgOp` of `P_t[f]`, which exist only because `goI_isFeller` holds. `goI_isFeller` is proved via `isFellerSG_of_dense` with polynomials dense (Weierstrass, `polynomialFunctions_closure_eq_top`) and `go_semigroup_poly_cls` (R27) mapping polynomials to polynomials; the conjugation `goRestr_polyι` identifies classes. Mass one comes from `goSG_one`, derived from `standardSemigroup_one_fin` (S11) via `goRestr_one2`. No hypothesis is smuggled; `goKernelI_rep` uses nothing but `sgKernel_rep`.
* `SGData` faithfully restates R16's needs (zero, add, strong continuity, self-adjoint, positivity, `P_t u ≤ 1` for `u ≤ 1`, contraction); `goSG` fields are all proved from the original triple, nothing weakened (all hypotheses present are discharged, not dropped). `DiffusionTriple.toSGData` is supplied. Necessity: R16/R17 layer is typed on `DiffusionTriple X`, and no `DiffusionTriple` on `[-1,1]` exists.

## (b) Deviation R28-M-1: confirmed real and honest
Frozen line `kernel t x = (goKernelI t (goRetr x)).map val` for all `x : ℝ` contradicts `kernel_zero` (forces `kernel 0 x = δ_x`) for `|x|>1` since the RHS at t=0 is `δ_{clamp x}`. So the frozen text was false; the replacement `_of_mem` / `_of_not_mem` (+ `_support`, `_isMarkov`) is the only consistent statement and is proved. Recorded as HIGH in ERRATA: appropriate. (Mild remark: it is a bridge whose kernels from outside `[-1,1]` are frozen; since that set is `goμ`-null this is harmless for `rep`/`invariant`, and is stated openly.)

## (c) Process defect R28-M-5: confirmed
* `frozen-manifest.json` vs ee1c0fb (compared structurally): only one entry added (`R28/STATEMENTS_R28_M.md`, status `proposed`); no other entry changed or removed; `STATEMENTS_R22_E4.md` appears exactly once now (the duplicate added in 43b2050 was removed in 50ef7aa). `python3 scripts/check_frozen.py` prints OK; sha256 of the file matches the manifest.
* `STATEMENTS_R28_M.md` was committed in 43b2050 (and extended with M4 in ea6644d) before any `R28/*.lean` file (first appear in 50ef7aa): freeze-before-proof holds. Caveats (INFO): the manifest hash is that of the final file including the Status section appended after the proofs, so the manifest does not pin the pre-proof text (git history does). The frozen M2 line was wrong (see b) and was kept in the file with a status note rather than silently edited. Acceptable.

## (d) Build / hygiene: clean (see above).

## (e) Survey table
* Real theorems: every `has bridge` row names an existing def in `R28/Survey.lean` / `OUB.lean` / `GoBridge.lean` typed against the correct triple (`.toDiffusionTriple` of the Standard/Full/Compact instance); these compile and have standard axioms. The Standard/Full/Compact variants are definitional restatements of existing bridges (`ouMarkovProcessBridge`, `circleMarkovProcessBridge`, `sphereMarkovProcessBridge`, `brownianBridgeRd`), not new mathematics; the table says so. `ouBMarkovProcessBridge` is genuinely new (Mehler kernels, `PtB_mehler` + `KernelBridge.ofTestClass`), correctly claims no identification with `ouDiff.semigroup`.
* My grep of all `StandardTriple/FullTriple/CompactTriple` definitions found one real omission: **`gaussRdFull d`** (Gaussian on `Rd d`, `LebesgueRd/Full/GaussFinite.lean`), which has no bridge in the library. FIXED (LOW, doc): row added to the GAPS table, relabelled as added by this audit, with a note on the hypothesis-parametrised families (`goStandard/goFull`, `gibbsStandard/gibbsFull`, `gibbsRdFull`, `riemFull`, `EllPI.standard/full`) that were implicitly covered by their `_unconditional` instances. All other instances (ou*, ouB*, circle*, s*, o*, lebesgueFull, lebesgueRdFull, go, gibbs*_unconditional, gibbsRdFull_unconditional, fullU, riemFull_unconditional, trivialCompact) are in the table. Claim "Product/Laguerre/Jacobi not in the library": consistent with my grep.
* `oStandard/oFull` "no bridge because only an a.e. statement": the table and ERRATA R28-M-4 say "not proved, not refuted"; correct as stated. It should not be read as a proven obstruction. The wording `kernel_null_ae` (a.e. transfer) is plausible; I did not re-derive the mathematical reason, and the claim is only a not-done statement.

## (f) Honesty of not-done: good
NOT-done lists (no `DiffusionTriple`/`FullTriple` on `[-1,1]`, no kernel uniqueness statement for `goKernelI`, no heat-kernel densities, oFull/lebesgueFull/Gibbs/Riemannian) are explicit.

## Findings ranked
* LOW (code): ~570 lines of R16/R17 compact Feller layer (`FellerSG.lean`, `FellerSGMeasurable.lean`) duplicate `FellerKernel.lean`/`FellerMeasurable.lean` (633 lines) for `SGData`. Justified (R16 typed on `DiffusionTriple`; refactor of audited code avoided) but is a maintenance debt: a refactor deriving the `DiffusionTriple` version from `toSGData` would remove it. Flagged, not blocking.
* LOW (doc, FIXED): `gaussRdFull` missing from survey table.
* INFO: manifest hash pins the post-proof statement file (see c); `goFull_bridge` etc. are aliases (definitional restatements), so "N instances have bridges" counts aliases, not N independent constructions.
* INFO: the build log re-verified only the uncached modules; no warnings/sorry in what was rebuilt, and no `sorry`/`set_option` in the R28 sources.

No HIGH/MEDIUM issue found. **Verdict: ACCEPT.**
