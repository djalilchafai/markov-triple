# Hostile audit: round 15, converse of BGL Prop 3.3.17 and `Core2` (branch tip ea75ac3, contains 177e0e4)

Independent auditor. **Result: no soundness defect, misformalization, vacuity or cheat.**
`Core2` means exactly '(1-L)A0 is a core for L|A0' (dense range of (1-L)^2 on A0); the book's p.162 argument, re-read independently, does identify l_f(h) = ∫(Lf+ρf)Lh only for h in A0, so the step to f in D(L*) = D(L)
needs the bound on a core of L, i.e. Core2; no book route avoiding it was found (P_t, ergodicity, the rho >= 0 remark do not touch this step). The substitute route (v = b - Lb, `bound_fLv`) was re-derived:
`ell_sq_le` (discriminant), the constant M, `exists_rep` (kernel containment handled, no injectivity needed), final adjoint step. `ouFull_core2` (Hermite basis + graph-norm cut-offs, `LoLo_mul` eight terms)
and `lebesgueFull_core2` (resolvent solution, `LL_mul` coefficients 1,4,6,4,1, `cutoff4_tendsto`) are genuine density arguments; `ouFull_CD` and `lebesgue_CD` are existing theorems so the hypotheses are consistent;
`CompactTriple.mem_domain_of_A` is faithful but trivial (A = A0). Structural: frozen OK; new modules recompiled from scratch (0 errors/warnings); all new axiom lines standard.
Findings (documentation): (1) the claim 'ESA of L does not imply ESA of L^2 on the same domain' was uncited: softened in `Converse.lean`; (2) 'the book needs Core2' is an accurate diagnosis, not a proof that no route exists (statement kept as 'we found none');
(3) only the direction `core2_of_dense` of the equivalence Core2 <=> dense (1-L)^2 A0 is a Lean theorem. S10 is not used in the substitute route (still a field of FullTriple).
Open: Core2 for an arbitrary FullTriple and for the Gibbs triple.
