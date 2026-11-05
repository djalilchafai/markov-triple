# Audit R32 Stream Y (hostile): F8 for the sphere, `sphereF8`, unconditional `sphereFullU`

Verdict: **ACCEPT** (two stale-doc lines relabelled by the auditor; no proof or statement touched).

## Checks
1. `lake build` (merge of worktree-agent-af509ac58737f784b, last commit 8fd53eb): green, 9601 jobs, 0 warnings/errors in the log; Sup, Series, Expand, F8U also recompiled alone with `lake env lean`: no output.
2. No `sorry/set_option/native_decide/axiom` in `Full/{Sup,Series,Expand,F8U,AxiomCheckR32Y}.lean`. `#print axioms` for harm_grad_L2, harm_sup, contDiff_top_Fs, exists_expansion, sphereF8_pos, sphereF8, sphereFullU, sphereFullU_CD, sphereFullU_core2: all `[propext, Classical.choice, Quot.sound]`. `check_frozen.py`: OK.
3. Git: freeze commit 49fe22a touches only `STATEMENTS_R32_Y.md` and `frozen-manifest.json`; manifest diff vs main = only the one new entry (hash is that of the post-Status file, allowed re-hash). New modules imported in `MarkovTriple.lean`.
4. Soundness.
 (a) `SphereF8 n hn := ∀ t f(∈ A₀), ∃ g ∈ A₀S n, P_t(cls f) =ᵐ g` with `A₀S` = functions whose degree-0 extension is C^∞ off 0 (not trivial: it is the same A used by `sphereFull`). `smoothCls` is the same predicate on Lp classes; `sphereF8_iff` is `Iff.rfl`. `sphereF8` proves exactly this (t=0 by `sphereF8_zero`, t>0 by `sphereF8_pos` for ALL u ∈ L²). `sphereFull hn h8` has no other hypothesis (all fields proved in R29; `semigroup_A := h8`). No new field.
 (b) Re-derived: Γ(h)=|∇h|²−k²h² on S, ∫Γ=−∫hLh=k(k+n−2)∫h², so Σ∫(∂_ih)²=k(2k+n−2)∫h². Induction: k h=y·∇h, (kh)²≤|y|²Σ(∂_ih)²; ∂_ih harmonic homogeneous deg k−1; Σ N(∂_ih)=k(2k+n−2)N(h); factor (2k+n−2)/k ≤ n iff (k−1)(n−2)≥0. Matches `harm_sup`. Base k=0 uses probability measure. Correct.
 (c) `exists_expansion`: `IsHilbertSum.mkInternal` with orthogonality (`harm_orth`, R31) and totality (`dense_span_harm`); ‖a_k‖≤‖w‖=‖u‖ by `lp.norm_apply_le_norm` and isometry. Correct.
 (d) `summable_gauss`: uses n≥2 so λ_k=k(k+n−2)≥k², bound (c+1)^k e^{-tk·k}, eventually ≤ 2^{-k}. `contDiff_top_Fs`: derivative series ∂_iH_{k+1} stays in HCls (constant 2^{n+2}2^k from harm_grad_L2, valid), `hasFDerivAt_tsum_of_isPreconnected` on balls, induction on order. Identification: P_t u=Σ P_t a_k (continuity, `hsum.mapL`), P_t a_k = e^{-λ_k t}a_k (`sphere_semigroup_harm`), uniform convergence on S (`restrA` sup bound `harm_sup_abs`) transfers through `toLp` to the pointwise sum; `A₀S_of_contDiff` gives membership in A₀S (degree-0 extension of a restriction of a C^∞ function on ℝ^n). Correct.
 (e) n≥2 throughout (circle included; the n-dependence is only through λ_k≥k², fine). Nothing vacuous.
 (f) `sphereFullU := sphereFull hn (sphereF8 hn)`; `_CD`, `_core2` are direct applications of the previously audited `sphereFull_CD`, `sphereFull_core2`. Fields F1–F10, S10, S11 already there from R29.
5. Honesty: GAPS Round 32 section and ERRATA R32-Y-1/2 are accurate (delivered = frozen; R32-Y-2 is beyond-frozen helpers).

## Findings
* LOW (doc, fixed by auditor): ERRATA R31-V-1 and GAPS R29-N "NOT done" bullet (line ~422) still said F8 unproved/no unconditional triple without a supersede annotation although R32-Y-1 claims they were annotated. Annotated (not deleted).
* INFO (not changed, comment-only): docstring of `Full/F8.lean` ("NOT proved in general") and `STATEMENTS_R29_N.md` "NOT delivered" are historical R29/R31 text, now superseded.
* INFO: `harm_sup` constant n^k is crude; irrelevant.
* No soundness issue found.
