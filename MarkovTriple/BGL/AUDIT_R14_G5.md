# Hostile audits: round 14/15, BGL Sect. 3.3 operator-level stage (Props 3.1.5, 3.3.5, 3.3.6, 3.3.16, 3.3.17 forward)

Two independent audits (the code was not written by the auditors).

## Audit 1 (branch tip 6cc98e9): no soundness defect, no vacuity, no cheat.
Structural checks pass (frozen OK, additive diff, no sorry/axiom/native_decide/set_option, 16 modules recompiled from scratch, 33 axiom lines all standard).
Smoke test: `hessE_eq_Hess'`, `gamma2E_mulE`, `integrable_Γ₂_of_domain`, `mem_formDomain_of_ESA` elaborate against `ouFull` (a non-compact triple with
A0 strictly inside A and A ∩ D(L) strictly bigger than A0), so the statements are not trivially true. Declared deviations E2, E3, E4 and the
Riesz variant of 3.3.6 (ii) were judged equivalent to the book. Findings: (1) MEDIUM coverage: 3.3.16 (iv) and (v) 2nd/3rd statements, and bilinearity/bounds
for hessE/gamma2E/gammaE, were not yet proved; (2) LOW: STATEMENTS_R14.md status table stale/inconsistent. Both closed by the next stage (ERRATA E5).

## Audit 2 (branch commit 5b1f517, gap closure): no soundness defect, misformalization or vacuity.
Linearity in each slot, boundedness (`hessE_bound`), continuity (`hessE_tendsto_left`, `hessE_tendsto_mid`, valid for general filters), bilinear
`gamma2E` (symmetry, bound, `Γ₂_ext_eq_gamma2E` linking to the quadratic Γ₂), `gammaE_cs` (Cauchy-Schwarz via nested subsequences), `gammaE_bound` re-derived and found
correct; 5 modules recompiled from scratch, 22 axiom lines standard. Notes (no statement change): `hessE_bound` is `∀h ∃C` (explicit h-dependence not
given; legitimate reading of the garbled book (iv)); L² versions of (v) 2nd/3rd and joint continuity not stated (the book's statements are L¹); the name
`hess2_eq_hessE` occurs only in a docstring.

Open at this point: the converse of Prop 3.3.17 (see STATEMENTS_R15_Converse.md / Core2).
