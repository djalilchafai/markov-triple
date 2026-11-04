# Hostile audit, R24 Stream C (implementation HEAD 495d928, base 6bff800)

Verdict: **ACCEPT** (0 HIGH, 0 MEDIUM, 3 LOW doc).

## (a) Statements and manifest
* Frozen statements commit 45ce17d precedes all proof commits (c4fd975, 2349c6d, 6a189aa, 495d928). The diff 45ce17d..495d928 of
  `STATEMENTS_R24_C.md` is purely additive (43 lines of Status appended, no line removed): the frozen part is unchanged.
* `frozen-manifest.json`: exactly one entry for `R24/STATEMENTS_R24_C.md`, status `proposed`, sha256 e58e4276...48a5 equals the actual
  file hash (refreshed after the Status section was appended; legitimate since only text was appended). `check_frozen.py`: OK.
* `IsFellerC0` is neither trivially true nor false: it requires every `C_c` class to be sent by `P_t` to a class of a `C_0` function.
  True for OU (proved), reduces to `IsFeller` in the compact case (`isFellerC0_of_isFeller`).
* Hypotheses satisfiable: `ou_isFellerC0 : IsFellerC0 ouDiff` is proved from the real Mehler kernel and the existing OU semigroup
  (`ou_rep_full`), with genuine decay at +-infinity (`ou_C0`, dominated convergence, `cocompact = atBot ⊔ atTop`). Genuinely non-compact.

## (b) Construction
Qop (continuous C_0 representative, unique by `IsOpenPosMeasure`) -> `lam` positive linear functional -> `RealRMK.rieszMeasure` -> mass <= 1
(inner regularity + Urysohn). Kernel measurability via `measurable_of_integrals_cc`. Exact CK (`fellerKernelInf_add`) by `ext_of_integral_cc`
using `Kernel.integral_comp`, the C_0 extension of the representation and `Qop_add_time` (two continuous functions equal a.e. are equal
by full support). The semigroup law enters only there, not through kernel CK: not circular. `hM` is an explicit hypothesis used only in
`fellerKernelInf_bind` and the bridge; the OU instance discharges it from `measure_univ` of the Mehler Gaussian. Honest.

## (c) Build and axioms
Full `lake build` succeeds (9448 jobs); Exact, Compact, OU, Bridge re-elaborated with `lake env lean`: no warnings. No `sorry`,
`set_option` or `axiom` in `R24/*.lean`. `#print axioms` (AxiomCheckR24C, all key theorems incl. `fellerKernelInf_add`, `_unique`,
`weakFeller_add`, `ou_isFellerC0`, `ouMarkovProcessBridgeInf`): only propext, Classical.choice, Quot.sound.

## (d) GAPS honesty and `feller_exact_ck_unique`
The frozen item was a comment-style statement (two weakly continuous families coincide; hence exact-CK one unique). It is realised as
`weakFeller_kernel_unique` (pointwise uniqueness), `weakFeller_zero`, `weakFeller_add` (exact CK for EVERY weak-Feller representing family).
Both clauses are covered: a refinement, not a weakening. The GAPS Round 24 paragraph matches the code and lists the open items (no
infinite-mu instance, hM, non-full-support, non-Feller exact semigroup).

## (e) ERRATA rows R24-C-1..3
Accurate against the code (conditionality, OU the only non-compact instance, hM needed, characterisation under compact + full support).

## Findings
* L1 (LOW, doc): "Feller extension for infinite mu" has no infinite-mu witness (OU has finite mu). Disclosed in Status and GAPS.
* L2 (LOW, doc): the frozen name `feller_exact_ck_unique` is not a declaration (disclosed as deviation (a)); R24-C-3 "kernels unique" should
  read "unique among weakly continuous families". ERRATA not edited.
* L3 (LOW, doc, FIXED): GAPS line 296 earlier OPEN list still presented the Feller extension for infinite mu as open; annotated.
