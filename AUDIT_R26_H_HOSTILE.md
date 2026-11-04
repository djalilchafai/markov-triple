# Hostile audit, R26 Stream H (atlas gluing, two-chart circle)

Verdict: **ACCEPT** (with 1 MEDIUM and several LOW findings, all doc-level or scope-disclosure).
Build: full `lake build` after merge, 9490 jobs, 0 warnings/errors (whole log grepped), no sorry/set_option/native_decide in `R26/`.
`#print axioms` (AxiomCheckR26H output in build log): all of `gamma_chart_change`, `transition_g/_w`, `integral_north/_south`,
`atlasIntegral_eq`, `atlasDiff`, `atlasDiff_Γ₂`, `atlas_CD` depend only on [propext, Classical.choice, Quot.sound].
`scripts/check_frozen.py`: OK.

## Findings

### MEDIUM-1: the "total-function equality is false off 𝒜₀" claim (ERRATA R26-H-1, STATEMENTS Status) is unsubstantiated and probably wrong
`D f p = deriv (s ↦ f (p + s)) 0`. For any f, `f∘pt = φ∘(x - x u)` with `φ s = f (pt u + s)` and `x` a local diffeomorphism, so
`deriv (f∘pt) u = D f (pt u) * x'(u)` for ALL f: if φ is differentiable at 0 this is the chain rule (I verified this branch in a scratch Lean file); if not,
both sides are the junk value 0 (non-differentiability transfers through the inverse function theorem). The same argument gives
`Chart1.Γ_eq`, `Chart1.L_eq` for all f, h (L uses the same fact applied to `D f`). Hence the frozen H5 statement
`atlasDiff.Γ = circleDiffusion.Γ`, `atlasDiff.L = circleDiffusion.L` (total) was most likely provable, and the delivered 𝒜₀-restricted version is a
(safe, honest-in-direction) weakening whose stated justification ("false") is not backed by a counterexample. I did not finish the Lean proof of the
non-differentiable branch, so this is "probably", not proved. ERRATA R26-H-1 amended accordingly. No soundness impact. The GAPS remark
"agrees with `circleDiffusion` only on 𝒜₀, so Friedrichs data not re-derived" is consequently also overstated as a reason (the true reason is that no
semigroup/FullTriple was built from the atlas).

### LOW-1: chart-independence (a) does not use the transition laws
`chart_transition`, `glueΓ_indep`, `glueL_indep` are proved by `Γ_eq`/`L_eq` (both charts equal the library `Gc`/`Lc`), i.e. through the global intrinsic
objects. The transition laws `transition_g/_w`, `north_south_pt` are proved but used nowhere (grep: no use outside AxiomCheck). `gamma_chart_change`
(the genuine pushforward-law statement) is also unused by the 1-d development. So it is chart independence by "all charts agree with the intrinsic
operator", which is legitimate here because the chart datum `g = x'^-2`, `w = x'` is built from the lift `x` of the standard circle; it is not a gluing of
independently given local data via cocycle conditions. Positive: `glueΓ/glueL` ARE defined from chartwise data only (`Classical.choose` of the cover), and
the identification with `Gc/Lc` is a theorem (`glueΓ_eq`, `glueL_eq`), not a definition. Docs ("chartwise Γ, L ... transition laws") slightly oversell the role of the laws.

### LOW-2: `atlasDiff` is largely `circleDiffusion` in disguise
Only `μ, Γ, L` are replaced; `A₀, measurable, bounded, memLp, dense, comp_mem, exhaustion` are copied from `cD`, and D1–D8 for glueΓ/glueL are proved by rewriting
to `Gc/Lc` and invoking `cD`'s proofs. Disclosed in the docstring ("inherited"). `atlasDiff.μ := μ₀` by definition; `atlasIntegral_eq` is not used to construct it
(disclosed in STATEMENTS as the fallback/by-design). `atlasDiff_Γ₂`, `atlas_CD` are computed via `circle_Γ₂` after identification, not an independent chartwise computation. CD(ρ≤0,n≥1) is the trivially flat case.

### LOW-3: `atlasIntegral_eq` partition of unity is weak
`integral_chart` shows each chart integral over ℝ already equals ∫ dμ₀ (each chart covers 𝕋 minus one null point), so the PoU step is just `ρN+ρS=1`.
Support properties of ρN, ρS are not used (and not proved). Unused hypotheses `_hF` (disclosed). Genuine change of variables (`integral_image_eq_integral_abs_deriv_smul`, ranges `(-1/2,1/2)`, `(0,1)`) is real.

### LOW-4: frozen file edited after freeze
`STATEMENTS_R26_H.md` hash in the manifest was updated from the freeze commit e0df331 (45d5444…) to 73a2b2d… when a "Status" section was appended in 665b0f0. Frozen
statements themselves unchanged (append-only diff, 6 lines). e0df331 touched only the statements file + manifest entry. No duplicates. Hash current.

## Checks that passed
(c) Hand verification: x_N = arctan t/π, x_S = x_N + 1/2; for t>0, arctan(-1/t) = arctan t - π/2 so x_S(-1/t) = x_N(t) (t<0 differs by 1, i.e. 0 in 𝕋). x' = 1/(π(1+t²)) = w,
g = x'^-2 = π²(1+t²)². τ' = 1/t²: g_S(τ) = π²(1+t²)²/t⁴ = τ'² g_N; w_S(τ)|τ'| = 1/(π(1+t²)) = w_N. Total volume ∫ dt/(π(1+t²)) = 1 = |circle of length 1|. Consistent (and `north_total`).
(f) Honesty of non-done: GAPS and ERRATA R26-H-2 explicitly list d≥2, Piola identity, S^d, general manifold atlas, FullTriple/semigroup from atlas, as NOT done/OPEN; GAPS title "first verified step"; no overclaim of atlas gluing as closed.
