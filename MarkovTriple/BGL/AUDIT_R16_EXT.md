# Hostile audit: round 16, field `ext` of `FiniteDimInterpolation` proved; finite-n log-Sobolev for finite-measure FullTriples (branch HEAD c55918b)

Independent auditor. **Result: no soundness defect, misformalization or overstatement.** `finiteDimExt` is exactly the frozen field `ext` (same quantifiers; the two integrability hypotheses are unused because `Bdd` gives them: the theorem is stronger than needed);
the coefficients 1/4, 1/8, 1/16 of (5.7.8) at a = 1/2 and the constant (4m−1)(m−1)/(4(m+2)²) = (1−a)² − m a² at a = 3/(2(m+2)) were re-derived by hand; `Bdd.integrable_ΓΓ`, `integral_exp_L_Γ_bdd`, `Bdd.comp`, `ibp_of_domain` hypotheses checked; `LS (dimLSConst ρ n) 0` is the same predicate as in `logSobolev_of_CD_dim`; κ is pinned so the earlier κ-too-large caveat does not apply.
Structural: frozen OK; no conflict markers anywhere; Ext modules recompiled from scratch (0 errors/warnings); axioms standard.
SCOPE FINDING (INFO): no non-compact finite-n ρ>0 instance exists in the library (see ERRATA R16-Ext-audit and the GAPS scope note); every known finite-n CD witness is compact. Doc findings fixed. Open: ρ<0, infinite μ, n = 1.
