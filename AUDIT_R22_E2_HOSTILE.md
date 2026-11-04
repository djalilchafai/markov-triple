# AUDIT R22-E2 (hostile): zonal Gegenbauer lambda = 3/2 on (-1,1), A0 = C_c^inf((-1,1))

Audited commit eaec74b (merged into this branch). Files: `Instances/GegenbauerOpen/{Basic,Diffusion,NotComplete,Curvature,AxiomCheckR22E2}.lean`, `STATEMENTS_R22_E2.md`.

## Verdict
No HIGH, no MEDIUM finding. The claims S1, S2a, S2b are faithful and proved; S3 is honestly reported as not attempted. Two LOW doc inaccuracies (recorded here; implementer files untouched).

## Mechanical checks (all OK)
* `lake build ...GegenbauerOpen.AxiomCheckR22E2`: success. `lake env lean` on each of the 5 files: 0 warnings, 0 errors.
* `#print axioms` on goA₀_dense, goDiff, integral_go_L, integral_go_L_self, go_le_of_Γ, go_not_complete, go_ΓA, go_Γ₂_eq, goDiff_CD: only propext, Classical.choice, Quot.sound (9 outputs).
* grep: no `sorry`, no `set_option` in the directory.
* `scripts/check_frozen.py`: OK. `git diff b44dbee..eaec74b -- frozen-manifest.json`: exactly one added `proposed` entry (STATEMENTS_R22_E2.md); no fenced file touched; lakefile/manifest/toolchain untouched; only new files plus that manifest entry.

## Math recomputed by hand
* Normalisation: int_{-1}^{1}(1-x^2)dx = 4/3, so (3/4)(1-x^2)dx is a probability measure (Basic.lean 53-72 matches).
* Generator: with w = 1-x^2, (w^2 f')' = w^2 f'' - 4x w f' = w * Lf for Lf = w f'' - 4x f'. Hence int g Lf dmu = (3/4) int g (w^2 f')' = -(3/4) int g' w^2 f' = -int Gamma(f,g) dmu with Gamma = w f'g' (Diffusion.lean 62-95 is exactly this; compact support of g in the open interval kills boundary terms; restriction of the measure to (-1,1) harmless since integrands vanish off it, `integral_goμ`). Weight is the true Gegenbauer weight (1-x^2)^(lambda-1/2) for lambda = 3/2, and L has coefficient (2lambda+1)=4, n = 2lambda+1 = 4 (S^4 zonal). Consistent.
* Gamma2: independently recomputed Gamma2 f = (1/2)L(w f'^2) - Gamma(f,Lf) with (Lf)' = w f''' - 6x f'' - 4f'; result w^2 f''^2 - 2x w f' f'' + (3+x^2) f'^2. Matches `go_Γ₂_eq` and the Bochner form ((w f'' - x f')^2 + 3x^2 f'^2 + 3 w f'^2) (expanded, equal).
* CD: Gamma2 - 3 Gamma - (1/4)(Lf)^2 = (3/4) w^2 f''^2 >= 0 (cross and f'^2 terms cancel exactly). So CD(3,4) = CD(n-1,n) for S^4, and CD(rho,n) for rho<=3, n>=4 (since 1/n <= 1/4, rho Gamma <= 3 Gamma on |x|<=1). For c = 1/n > 1/4 the quadratic form in (w f'', x f') is (1-c)B^2 - 2(1-4c)BA + 4(1-4c)A^2, whose A^2 coefficient is negative: CD(3,n) FAILS pointwise for n<4 at x != 0 (take f''=0). So the doc's "expected to fail, not checked in Lean" is correct and in fact true (not proved in Lean). n = infinity: (inf^-1).toReal = 0, fine. GoCD matches FullTriple.CD's body.
* Non-completeness: `IsComplete` (Frozen/Complete.lean 28-31) is satisfiable in this library (gibbsDiff_isComplete, Gibbs/Diffusion.lean), so the non-vacuity of the property is fine. The proof: Gamma zeta <= c^2 everywhere (a.e. to everywhere by continuity, correct: also handles off-(-1,1) where zeta' = 0) gives zeta' <= c/sqrt(1-t^2), c*arcsin - zeta monotone from -1, zeta(x) <= c(arcsin x + pi/2) <= c*pi. Then zeta_k(x) <= pi/(k+1) -> 0 contradicts zeta_k -> 1 a.e. Uses only Gamma = (1-x^2) f'g', so the obstruction int dx/sqrt(1-x^2) = pi (Riemannian diameter of (-1,1) is finite) holds for EVERY lambda (weight changes only the measure, not Gamma; mu has full support in (-1,1)). Verified.
* Limit-point: Lf = 0 has solutions 1 and f with f' = C (1-x^2)^(-(lambda+1/2)), f ~ (1-x)^(-(lambda-1/2)) at 1; |f|^2 (1-x^2)^(lambda-1/2) ~ (1-x)^(-lambda+1/2), non-integrable iff lambda >= 3/2 (lambda = 3/2: ~ (1-x)^(-1), log-divergent). So both endpoints limit-point iff lambda >= 3/2, limit circle for 1/2 < lambda < 3/2: consistent with ERRATA R21-4 and with the doc's "(1-x)^{-1}" for lambda = 3/2.
* Converse theorem: `FullTriple.mem_domain_of_Γ₂_direct` (Theory/Extension/ConverseDirect.lean 295) takes `hC : T.toDiffusionTriple.IsComplete`; `go_not_complete` makes it inapplicable to any FullTriple over `goDiff` (even with S3). Claim verified. (The doc's last paragraph about testing the conclusion on f ~ (1-x)^(-1/2+eps) is speculation, flagged "not attempted"; harmless.)

## Findings
* LOW-1 (STATEMENTS_R22_E2.md, Status deviation 2): says the proof uses "Gamma2 - 3 Gamma - L^2/4 = (3/4)(a-b)^2". Wrong: the exact identity is (3/4)(1-x^2)^2 f''^2 (in the Lean names, (3/4)((1-x^2) b)^2). The Lean proof (Curvature.lean, final nlinarith hint `sq_nonneg ((1-x^2) b)`) is consistent with the correct form. No effect on correctness.
* LOW-2 (same file, S3 route (A)): "for the Hardy weight ... `∫ (1-x)^{-?}`" is a placeholder; and "CD(3,4) sharp in n" (ERRATA row R22-E2-2) is true (shown above) but not formalised; "sharp" is a hand claim. Not a Lean statement; row labelled INFO. Acceptable.
* LOW-3: `goDiff` is `@[reducible] def` (Diffusion.lean ~120); harmless but `GoCD` unfolds through it. No issue.
* INFO: `GoCD` is pointwise, not `FullTriple.CD`; honestly stated (DIFFERENCE FROM BGL 2, ERRATA R22-E2-3). Statement that it is a `DiffusionTriple` with Gamma2 etc. only (no FullTriple) is accurate; GAPS R21-4 stays open as claimed.
* Proposed ERRATA rows R22-E2-1..3 are accurate (INFO; names/files exist; counts of ranges correct).

## What I did not verify
Not re-derived the Lean proof of density (compiles, axioms clean; statement checked against `DiffusionTriple.dense` field). F8/F10 (S3) are not claimed.
