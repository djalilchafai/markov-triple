# Hostile audit: round 16, Jensen step and weak gradient bound (BGL Cor 3.3.19), branch commit ec13831

Independent auditor. **Result: no soundness defect, misformalization or vacuity.** `jensen_sq` takes exactly the hypotheses supplied by `semigroup_nonneg` and `semigroup_le_one` (no extra boundedness; infinite mu allowed; P1 never used);
the conclusion of `gradient_bound_unconditional` is syntactically identical to the conditional `gradient_bound`; `hasGradientBound_unconditional` has the frozen quantifier structure; `conservative_of_complete_unconditional` is the existing conditional theorem
applied to the new bound. The algebra P Z = P W − 2q P B + q² P S, the rational-q density argument, the L² convergence B_n → w and the squaring step were re-derived for all rho ≥ 0. The statements file (written after the first draft, ERRATA R16-J1) was compared with the final Lean statements: identical and natural.
Structural: frozen OK; 4 modules recompiled from scratch (0 errors/warnings); axioms standard. Findings: documentation only (the 'w in L^4 implicitly' remark; no Gibbs instance of mass conservation added, honestly stated).
Not done by the auditor: re-audit of the inherited strong bound (audited in round 15), reading the book pages. Open: rho < 0, G1 (not a book statement), G3, G3'.
