# Hostile audit: round 16, interior elliptic regularity through H² (Evans §5.8.2, §6.3.1 Thm 1), branch HEAD dc2ef84

Independent auditor. **Result: no soundness defect, misformalization or vacuity.** `WeakDeriv` uses `((⊤:ℕ∞):WithTop ℕ∞)` test functions (R16-E1; all 6 ContDiff occurrences checked), is non-vacuous (`weakDeriv_of_smooth`, a.e. uniqueness `WeakDeriv.unique`);
`LocL2`, `Sobolev k` standard; `eLpNorm_dq_le` (Evans Thm 3(i)), `weakDeriv_of_bounded_dq`, `norm_le_of_dual_bound` (needs 0 ≤ M, R16-E2), `moll_tendsto`, `weakForm_extend`, E1 (`weak_caccioppoli`, constants −2 and 4 re-derived by hand) and E2 (`interior_H2`, constants fixed before t) checked.
SATISFIABILITY of H: the auditor proved in a scratch Lean file that for ANY `E : EllData d`, smooth u with `E.L u = h` satisfies `E.VeryWeakSol u h`, and that `interior_H2` applies to it: `VeryWeakSol` conventions are consistent with L = w⁻¹ div(w a ∇), H is non-trivially satisfiable.
Structural: frozen OK, additive diff, 15 Elliptic modules recompiled from scratch (0 errors/warnings), axioms standard. Not re-derived line by line: `pw_main`, `pw_R2`, `final_arith` (kernel-checked).
Findings: documentation only (ERRATA R16-Elliptic-audit). Scope: E3, the Friedrichs step and the link to `EllReg` were not in this stage.
