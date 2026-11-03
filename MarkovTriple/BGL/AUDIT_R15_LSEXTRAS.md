# Hostile audit: round 15, LS => PI, optimality, n = 1 case, circle instance (branch commit f02035f)

Independent auditor. **Result: no soundness defect, misformalization or vacuity.** The algebra of `integral_exp_Γ₂_ge_one` (a = 1/3 and a = 1/2 steps,
claims (i) and (ii)) was recomputed by hand against BGL pp. 272-273; `log_sq_lower` was checked numerically on 2e6 points of [-1/2, 1/2]; the LS => PI
argument (BGL Prop 5.1.3) has the right orders and constants; the circle Wirtinger constant 1/(4 pi^2) on R/Z, the Fourier-mode derivative formula and
the sharpness eigenfunction cos 2 pi . were verified; the zonal S^3 eigenvalue k(k+2) = 3 and 'no LS(c,0) for c < 1/3' match the book's optimality claim.
`FiniteDimInterpolation (1/c)` is proved (not assumed) for compact triples, so the earlier 'vacuous above the true rate' caveat does not bite here.
Documentation / scope notes (no change to any statement): sphere results are for the ZONAL triple `sCompact`; `PI_of_LS` needs `1 in A0` (unconditional only on
compact triples); circle constants are for period 1, not the book's 2 pi-torus; four proofs are textual copies of the CD-based originals (refactor possible).
Structural: frozen OK; 5 new modules recompiled from scratch, 0 errors/0 warnings; axioms only propext/Classical.choice/Quot.sound.
