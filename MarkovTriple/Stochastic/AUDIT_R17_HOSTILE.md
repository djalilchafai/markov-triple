# Round 17 Stream E: independent hostile audit (commit 43e9f18)

Auditor method: Armstrong style; author's claims not trusted.  Audited commit `43e9f18` (branch `worktree-agent-a16b84c2a2cdad257`).
Verdict: **no soundness defect, no vacuity, no overclaim of substance.**  Findings are documentation/naming only.

## Verification performed
* `lake build` of the worktree was NOT used (it started rebuilding Mathlib inside the worktree because package builds are not part of
  `.lake/build`; I was not permitted to kill that stray process).  Instead the four new modules were compiled directly with `lean`
  against the main repo's read-only olean tree (`LEAN_PATH` = main `.lake/build` + `.lake/packages/*`; dependencies symlinked into a scratch dir):
  `FellerMeasurable`, `FellerProcessBridge`, `ExactCK`, `AxiomCheckR17` all compile with **no output at all (0 errors, 0 warnings)**.
* `grep -n "sorry\|set_option\|axiom\|native_decide"` on the three Lean files: no hit.
* `#print axioms` (AxiomCheckR17, 19 declarations, re-run by me): every one is `[propext, Classical.choice, Quot.sound]`.
* `python3 scripts/check_frozen.py` prints `OK`; `sha256sum STATEMENTS_R17.md` = `26a7f0189fdcf80001701908514af4ccd83f0ed28b57b1d527260b096a8598d1`
  = the `proposed` entry in `frozen-manifest.json`.
* Probe file (scratchpad, not committed) importing the new modules plus `CircleFeller`/`SphereFeller` compiled and checked:
  * `circleMPB : MarkovProcessBridge Circle.cT := fellerMarkovProcessBridge circle_isFeller (fun t => Circle.semigroup_one t)` typechecks
    (axioms standard), and `circleMPB.kernel = Circle.circleKernel` is proved from `circle_fellerKernel_eq'`.  So the hypotheses
    (finite full-support `mu`, `IsFeller`, conservativity) are satisfiable for the circle and, via `sphereMarkovProcessBridge`, for zonal `S^3`.
  * `sphereMarkovProcessBridge.kernel = fellerKernel sphere_isFeller := rfl`; `.invariant` gives `mu.bind (kernel t) = mu`.
  * `rieszKernel_exists_exact_ck Circle.cT (Set.range ((↑) : ℚ≥0 → ℝ≥0)) (Set.countable_range _)` typechecks (the rational-times instance);
    the conclusion has the expected shape (conull measurable `G`, closedness, CK with `s+t` arbitrary, `kappa_0 = dirac`).

## Checks of the questions asked
1. **Statements vs. frozen file / BGL.**  Lean statements of `measurable_of_integrals_param`, `isClosed_fellerOp_ball`, `measurable_fellerOp_time`
   (into `C(X,R)` with Mathlib's Borel structure = Borel of the sup-norm topology on compact `X`), `measurable_fellerOp_joint`,
   `fellerKernel_measurable_joint` (measurability w.r.t. `Borel(R>=0) (x) Borel(X)`, the right sigma-algebra: it is the one required by
   the `measurable_kernel` field), `exists_exact_ck`, `rieszKernel_exists_exact_ck` are textually those of `STATEMENTS_R17.md`.
   No weakened or unsatisfiable hypotheses (see probes).  `exists_exact_ck` is non-vacuous when `mu != 0` (and for `mu = 0` it is trivially true,
   as any such statement is; the Riesz corollary does not assume `mu != 0`; harmless).  `S` need not be closed under addition (stronger than needed).
   Mathematical argument (L^2-strong continuity + order-closed `L^2` + full support => lower semicontinuity of `t -> ||P_t f - g||_inf`) is correct
   and is what the file does.
3. **`fellerMarkovProcessBridge` is the genuine bridge.**  It is `(fellerBridge hF hcons).toMarkovProcessBridge (fellerKernel_measurable_joint hF)`;
   all five data fields (`kernel`, `measurable_kernel`, `kernel_zero`, `kernel_add`, `isSubMarkovKernel`) plus `rep`, `invariant` come
   field by field from the R16 `fellerBridge` (kernel = Riesz measure of the unique continuous representative, characterised by
   `integral_fellerKernel`); `fellerMarkovProcessBridge_kernel` is `rfl`.  Not defined by an unrelated choice.

## Findings (severity-ranked)

### F1 (LOW, doc/process): frozen text and Lean names differ; erratum R17-1 handles it but the frozen file was not amended
`STATEMENTS_R17.md` freezes `fellerMarkovProcessBridge_toKernelBridge_kappa` (statement `(..).kappa = fellerKernel hF`) and
`sphereMarkovProcessBridge_kappa`; neither exists.  The code has `fellerMarkovProcessBridge_kernel` / `sphereMarkovProcessBridge_kernel`
(field is `kernel`, not `kappa`; content identical and `rfl`), recorded as R17-1.  Also `STATEMENTS_R17.md` puts `sphereMarkovProcessBridge` in
`MarkovTriple.Stochastic` but it lives in `MarkovTriple.Stochastic.Sphere` (the frozen text writes `Sphere.sT`, ambiguous), and `clsC_le_iff`,
`fellerMarkovProcessData`-level names beyond the frozen list (`clsC_le_iff`, `ae_measure_eq_of_forall`, shrink lemmas, `sphereMarkovProcessBridge_isMarkov`)
are additional (harmless).  The frozen-vs-code deviation is documented honestly in ERRATA (R17-1); no weakening.  The name in R17-1 is accurate.

### F2 (LOW, stale text): R16 audit files still say joint measurability / `MarkovProcessBridge` for Feller kernels is NOT proved
`MarkovTriple/Stochastic/AUDIT_R16_SELF.md` lines 37-40 ("NOT proved jointly measurable ... no `MarkovProcessBridge` for `fellerKernel` is claimed")
and `AUDIT_R16.md` line 8 ("no joint measurability in t (so no `MarkovProcessBridge` for these kernels)") are now false as present-tense statements.
They are historical and superseded by ERRATA R17-2, but carry no forward pointer in the files themselves.  Suggest a one-line "superseded by R17-2" note.

### F3 (INFO, scope; correctly disclosed): what is NOT delivered
(a) the plain Riesz kernels get exact CK only on a conull set for countably many times; no `KernelBridge` for them; (b) the Feller hypothesis stays
explicit; (c) (iii) non-compact extension not attempted.  AUDIT_R17.md, GAPS.md and ERRATA R17-3/R17-4 state exactly this; I found no overclaim.
One wording nit: GAPS says "exact CK ... on a conull properly exceptional set for any COUNTABLE set of times" which is accurate; the module-doc of
`ExactCK.lean` correctly says no `KernelBridge`.

### F4 (INFO, hygiene): `lake build` in a fresh worktree rebuilds Mathlib
Copying only top-level `.lake/build` is insufficient (`.lake/packages/*/.lake/build` are separate); a stray `lake build` of mine is still running in this
worktree and could not be killed by me.  Not a repository defect.

## Not found
No `sorry`, no `set_option`, no new axioms, no warnings, no overclaims about joint measurability for the non-Feller Riesz kernels (AUDIT/STATEMENTS
say explicitly it is not claimed), no vacuous hypotheses, no mismatch between the manifest hash and the file.
