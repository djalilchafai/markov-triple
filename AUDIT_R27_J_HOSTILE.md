# AUDIT R27 Stream J (atlas gluing beyond d = 1): hostile audit

Verdict: **ACCEPT** (no HIGH/MEDIUM findings; 4 LOW/INFO doc-level items).
Audited: merge of `worktree-agent-a6aea83429480ea87` (e98763c freeze, 21615e6, 4a50d38, f99cde1) onto base e0d4be3.

## Checks
(a) Atlas non-vacuity. `Atlas M d` fields: `chart` (open `U`, `pt` injective on `U`, `g`, `w`, smooth, `w>0`), `cover` (every `p:M` is hit),
`τ_mem`, `overlap_open`, `τ_smooth` (C²), `τ_g` (g_b∘τ = J g_a Jᵀ) and `τ_w` (w_a=(w_b∘τ)|det J|) quantified over the overlap. These are genuine
hypotheses, not trivial: `sphereAtlas` proves them by real computation (`τ_g`: `field_simp; ring` on the explicit inverse-Jacobian; `τ_w`: uses
`det_jac_invS = -(r²)⁻²`). `S2 = {p:ℝ³ // |p|²=1}` is the actual unit sphere as a set; both charts have `U = univ`, `ptS b` injective (proved),
`cover` proved by explicit stereographic inverse, overlap proved equal to `{x≠0}` (non-empty, not a degenerate overlap). So no empty-domain/point trick.
What it establishes honestly: an algebraic atlas: two injective parametrisations of ℝ² covering the set `S²` with C² transitions and the g/w laws; no
topology on `M` (no continuity of `pt`, no Hausdorff), so "atlas of the manifold S²" is true only set-theoretically. Mild gap: `Atlas` does not require
`g` symmetric/positive-definite nor `w = det(g)^{-1/2}`; and `gS` is never proved equal to the pull-back of the ℝ³ metric. However the coordinate computations
`Γ(p_a,p_b)=δ_ab-p_a p_b` (proved) pin down the co-metric against the embedding, so the sphere identification is checked indirectly; `w=det(g)^{-1/2}` holds by hand
for the chosen data (det g = ((1+r²)/2)^4).
(b) Hand verification. Round metric 4/(1+r²)²δ, co-metric ((1+r²)/2)²δ, √det = 4/(1+r²)²: OK. τ(x)=x/r²: J=(I-2x̂x̂ᵀ)/r², J Jᵀ=I/r⁴, det J=-r⁻⁴: OK
(Lean: `-(r2 x ^ 2)⁻¹` with `r2=r²`, same). g_b(τx) = ((1+r⁻²)/2)² = ((1+r²)/(2r²))², J g J ᵀ=((1+r²)/2)² r⁻⁴: equal. Volume: w_b(τx)|det J| = 4r⁴/(1+r²)²·r⁻⁴ = w_a: OK.
Chart: (2y/(1+r²), ±(r²-1)/(1+r²)): true misses (0,0,1), false misses (0,0,-1): consistent. L p=-2p (λ₁=d=2), Γ(p_a,p_b)=δ-p_a p_b, Bochner Γ₂=|Hess|²+Ric(∇f,∇f)=2f²+(1-f²)=1+f²;
CD(1,2): Γ+½(Lf)²=1-f²+2f²=1+f²: all OK, matching the Lean statements.
(c) Piola: general `d`, genuine. Uses Jacobi (`pderiv_det` via `detRowAlternating` as continuous multilinear map), `adjugate_apply`, determinant row-swap sign against Hessian
symmetry `isSymmSndFDerivAt` (real `C²` input, `antisym_sum`). Unused `_hga,_hwa`: correct. `Lch_chart_change` is NOT true for arbitrary g,w: the laws `hg`,`hw` are
used essentially in `W_identity` (W_a = s·adj(J)(V_b∘τ)) and `hw` also yields det J ≠ 0 and the sign s; `ga,wa` smoothness is genuinely redundant because W_a is
rewritten on a neighbourhood as a function of `V_b` and `adj J` only. Not suspicious. Chart-independence proofs genuinely apply `Lch/Gch_chart_change` with laws eventually on the open overlap.
(d) Git: e98763c touches only STATEMENTS_R27_J.md + manifest. NOTE (LOW): after the freeze the file was appended (a "Status (delivered)" section, +13 lines, statements above unchanged)
and the manifest hash updated from 0752203… to 27f1088…; the present hash matches the file; `check_frozen.py` OK; manifest diff vs e0d4be3 is only the single R27 entry; no duplicates.
(e) Full `lake build`: success, 0 warnings in whole log; no sorry/set_option/native_decide/axiom in R27; `#print axioms` run by me: all 15 targets `[propext, Classical.choice, Quot.sound]`.
(f) Honesty: not-done list in GAPS/ERRATA is candid (no topology, no all-f CD(1,2), no triple/semigroup, d≥3 open). No overclaim of "S² Bochner" (equality on three coordinate functions only) or full manifold gluing.

## Findings
1. LOW (doc, fixed): GAPS annotation said "the coordinate-function part of (4)" is PROVED; the coordinate computations belong to step (3), not (4) (density/𝒜₀). Relabelled.
2. LOW (scope, already stated): `Atlas` is purely algebraic; `gS` is not proved to be the induced metric (only indirectly via Γ(p_a,p_b)); `Atlas` does not enforce `w=det(g)^{-1/2}` or symmetry/positivity of `g`. GAPS wording "genuine spheres S² ... CLOSED" should be read as set-level only.
3. LOW (process): frozen statements file modified after freeze (status section appended; manifest hash updated); the frozen statements themselves are unchanged.
4. INFO: ERRATA R27-J-1 "the theorem is in fact stronger" is accurate (hypotheses merely redundant).
