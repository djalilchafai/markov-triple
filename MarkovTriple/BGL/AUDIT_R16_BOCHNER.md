# Hostile audit: round 16, Bochner's formula for the weighted Riemannian chart (branch commit e412918)

Independent auditor. **Result: no soundness defect, misformalization or vacuity.** `riem_bochner` (BGL (1.16.4), Thm C.3.3) is a genuine proof chain (`L_eq_hess`, `pderiv_GamF`, `hess_GamF`, `pderiv_L`, `cov3_ricci`, `riem_antisymm`, `curv_part`, `alg_assemble`); Γ₂ is the library's ½(LΓ−2Γ(f,Lf)).
The auditor transcribed the Lean definitions into sympy and verified `Γ₂ = ‖Hess f‖² + (Ric + Hess W)(∇f,∇f)` at random points / symbolically for round S² (Ric = +g), hyperbolic disc (Ric = −g), S³ (Ric = 2g), a generic non-conformal 2-d metric, a generic 3-d metric, and `confRiem`; `confRiem`: K = −2e^{−|x|²}, Ric = −2δ, ∇∇W = 4e^{|x|²}(1+|x|²)δ, `Curv 2` holds; all RiemData fields proved.
Structural: frozen OK (manifest diff = one added proposed entry); 12 modules recompiled from scratch; axioms standard.
Findings (ERRATA R16-Bochner-audit): `set_option linter.unusedSimpArgs false` suppressed 13 warnings (removed, arguments dropped); only one direction of (1.16.8) proved; stale docstring in `Riemannian/Main.lean`.
Scope (honest): single global chart R^d with bounded co-metric; sphere and hyperbolic plane are not `RiemData` (unbounded co-metric); WeakHypo/F8 remain hypotheses for the Poincaré/CD statements of `confRiem`.
