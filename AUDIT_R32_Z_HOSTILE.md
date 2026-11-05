# Hostile audit, Round 32 Stream Z (Gegenbauer Core2L at lam = 5/2)

Verdict: **ACCEPT-WITH-DOC-FIXES** (doc fixes applied in this commit; no proof/statement change).

## Checks performed
1. `lake build` (full, merged branch dde64c7): "Build completed successfully (9600 jobs)", log has 0 occurrences of warning/error/sorry. `#print axioms` for `deficiency_pair_five_halves`, `not_core2L_five_halves`, `lipschitz`, `ode_series_cc`: only propext, Classical.choice, Quot.sound.
2. grep of `Core2/Z/*.lean` for sorry/set_option/native_decide/axiom: only the `#print axioms` lines. `check_frozen.py`: OK.
3. History: daddd1e touches exactly `STATEMENTS_R32_Z.md` and `frozen-manifest.json` (+5 lines, one new `proposed` entry). `git diff main HEAD -- frozen-manifest.json` is only that entry. The proof commit re-hashes only that entry (1 line) after appending the Status section, as permitted. The statements in Main.lean are textually identical to the frozen ones.
4. Soundness, re-derived by hand:
   - `L_lam f = (1-x²)f'' - (2lam+1) x f'`, weight `(1-x²)^(lam-1/2)` are the Gegenbauer ones; lam=5/2 gives `(1-x²)f'' - 6x f'`, weight `s²`, `s = 1-x²` (`gρ_five`).
   - `L(s^r A) = s^r[(-2r + (4r(r-1)+12r) x²/s)A + (-4r-6) x A' + sA'']` (matches `gL_five_mul_sp`). At r=-2 the x²/s coefficient is 24-24 = 0, the rest `4A + 2xA' + sA''`; so `Lw = w` iff `sA'' + 2xA' + 3A = 0`. Series: `(n+1)(n+2)c_{n+2} = (n²-3n-3)c_n` (matches `cc_rec`, c0=1, c1=0). Indicial exponents of `L` at ±1 are r = 0, -2 (r(2r+4)); for A at 1, 0 and 2. Ratio `c_{n+2}/c_n ~ 1 - 6/n`, so `c_n ~ n^-3`; the proved bound n^-5/2 gives `Σ n|c_n| < ∞`.
   - The "no logarithm needed" claim is NOT inconsistent: w is built from the power series at 0 (an honest analytic solution of `Lw = w` on (-1,1)); whether A has a `t² log t` term at ±1 only affects regularity of A at the endpoints, and only Lipschitz-ness (proved) is used.
   - `r=-1`: `L(s^-1) = s^-1(2 - 4x²/s)`, `Lh = α s^-2 (2-6x²)`, `w - Lh = s^-2 (A - Λ) - 6α s^-1` with `α = -Λ/4` (Λ = A(1)); the s^-2 cancellation needs `A(1)+4α = 0`: true. Then `|w - Lh| ≤ (C1 + 3|Λ|/2) s^-1`, weighted square bounded by const (`g_bound`); `h² s² = α²` (`h_bound`). `w(0)=1 ≠ 0`. `w` and `h` smooth on (-1,1) (power series with |c_n| ≤ 3/2, derivative bounds via `D_bound`).
   - `not_core2L_of_pair` (R31-W, audited) is applied with all hypotheses discharged by actual proofs (hw, hh, hwL, hh2, hg2, hne); `MemLp` obtained through `Core2W.memLp_muL` from continuity plus the weighted bound. No hypothesis is assumed vacuously. Note Λ may be 0 only trivially (h=0); that is still a legitimate pair as long as w ≢ 0, no issue.
5. Honesty: docs claim no `FullTriple.Core2` at lam=5/2, no threshold theorem, no positive half; "NOT claimed" and ERRATA R32-Z-2/-4 say so. ERRATA R32-Z-3 correctly records that the R31-W log prediction was too pessimistic (the Lean proof indeed never constructs a log; `cc_decay` for n>=3 and bound 3/2 are accurate: cc_2 = -3/2).

## Findings
- LOW (doc, fixed): GAPS R32-Z said the log term "is exactly what prevents A from being smooth" as if proved; it is only a heuristic from `cc_n ~ n^-3` (Lean proves n^-5/2). Relabelled in GAPS as heuristic/not formalised.
- LOW (doc, fixed): the superseded R31-W GAPS line (other lam, "log would have to be redone") was not annotated in place; an in-place SUPERSEDED annotation was added (nothing deleted).
- INFO: STATEMENTS text says "actually ~ n^-3" and "heuristic: Core2L fails for 3/2 < lam < 7/2"; both are unproved heuristics, correctly flagged as such in NOT claimed. GAPS "same mechanism for any lam where cc_n = O(n^{-3/2-eps})" is likewise speculative, and labelled not formalised.
- INFO: `Core2L` is a transcription, not a FullTriple statement (honestly stated everywhere).
