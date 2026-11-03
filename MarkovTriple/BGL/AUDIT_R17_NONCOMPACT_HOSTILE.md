# HOSTILE AUDIT, Round 17 Stream D ("Noncompact", `Instances/SphereOpen/*`), audited commit b04fe42

Auditor method: Armstrong (author's claims not trusted). Rebuilt SphereOpen modules from scratch (olean/ilean/hash/trace deleted), 0 errors, 0 warnings
(diagnostics other than `#print axioms` infos: none). The BGL book PDF could NOT be located on this machine (`find` for *bakry*/*bgl*/*markov* pdfs
found only unrelated papers), so every book numbering below (Def. 3.3.26, Thm 5.7.4, p. 272, Bonnet-Myers numbering) is UNVERIFIED here, as in the author's audit.

## Verdict
No soundness defect, no vacuity, no `sorry`/`set_option`/axiom, no frozen file touched. The Lean content is a faithful, correct unitary transport of the
compact zonal S^3 triple to the conull open subset (-1,1). BUT the headline "finite-n LSI on a NON-COMPACT state space" is cosmetic at the level of
the formalised theorem, and several docs overstate (see F1-F4). Mathematical value: small (a consistency exercise), not a new instance.

## Checks performed (all pass)
1. Statements N1-N9 vs Lean: `not_compactSpace_ZonO`, `μO` + `IsProbabilityMeasure`, `restrL p` (surjective isometry, all p), `oT`, `RO_restrC`/`PO_restrC`,
   `oFull`, `oFull_CD : oFull.CD 2 3`, `oFull_finiteDimInterpolation`, `oFull_LS : oFull.LS (1/3) 0`, `oFull_Γ_ne_zero`, `oFull_μ_pos_of_open` all present with the
   frozen shapes (cosmetic renames `restrLp -> restrL`, `mu_O -> μO`, `Zon/ZonO` as `abbrev ... : Type`). Probe: `#check @oFull_CD : oFull.CD 2 3`, `@oFull_LS : oFull.LS (1/3) 0`.
2. `oFull` genuine: `oT.μ = μO` (comap of μZ), `A₀ = {f∘val | f ∈ 𝒜_Z}`, `Γ`/`L` defined through the unique lift `liftO` (uniqueness by density + continuity, `eq_of_comp_eq`);
   junk value 0 only off `AO`, where frozen `DiffusionTriple` does not constrain Γ/L. Every D-field / F-field is a theorem about `μO`/`oT`; F8, F10, S10, S11 go through
   `RO_restrC`, `PO_restrC` (density of span of Chebyshev eigenfunctions + `R_cls_eigen`/`semigroup_cls_eigen`) i.e. about the Friedrichs semigroup OF `oT` on L²(μO), not on [-1,1].
   `FullTriple.CD` (Frozen/CD.lean) is the real CD: `∀ f ∈ A, ∀ᵐ x, ρ Γ(f) + (1/n)(Lf)^2 ≤ Γ₂(f)` with `Γ₂` from `oT.Γ₂` (ΓA/L on the test algebra), pulled back a.e. from `sphere_CD_two_three`
   through `Γ₂_O` (pointwise equality, proved). No hidden hypothesis.
3. `#print axioms` (rebuilt): `not_compactSpace_ZonO, measurePreserving_jO, restrL_surjective, oT, RO_restrC, PO_restrC, oFull, oFull_CD, oFull_finiteDimInterpolation, oFull_LS, oFull_Γ_ne_zero, oFull_μ_pos_of_open`:
   all exactly `[propext, Classical.choice, Quot.sound]`. `grep sorry|set_option|axiom` in SphereOpen: none.
4. `python3 scripts/check_frozen.py`: OK. `git diff main b04fe42 --name-only` (14 files) intersected with frozen/fenced paths of `frozen-manifest.json`:
   only the NEW `STATEMENTS_R17_Noncompact.md` entry (added as `proposed`). `MarkovTriple.lean`, ERRATA, GAPS edited (not frozen). lakefile/manifest/toolchain untouched.

## Findings (severity ranked)

### F1 (MEDIUM, conceptual/overclaim) The "non-compactness" is invisible to the formal theory; the instance exercises nothing beyond the compact case
* `FullTriple E` / `DiffusionTriple E` take only `[MeasurableSpace E]` (probe: `#check @FullTriple : (E : Type) → [MeasurableSpace E] → Type`). There is no topology, so
  "state space non-compact" is not a property of any object appearing in `oFull_CD`/`oFull_LS`. `not_compactSpace_ZonO` is a true but unrelated side lemma.
* The Lean-visible meaning of "compact" in this library is `A = A₀` (Compact Markov Triple, frozen). The author admits `oFull.A = oFull.A₀`. The only step of
  Thm 5.7.4 where compactness matters is the extension from 𝒜₀ to bounded 𝒜 (`FiniteDimInterpolation.ext`, R16). On `oFull` that step is vacuous (𝒜 = 𝒜₀), so
  `oFull_LS` already follows from the compact-case theorem of R14 (as `sphere_LS_dim` does), without the R16 `ext` machinery. So `oFull_LS` does NOT "exercise"
  `logSobolev_dim_unconditional`'s non-compact content (the R16 scope note's stated gap), contrary to the spirit of R17-1.
* Any FullTriple restricted to a conull measurable (even open) subset gives such a "non-compact" copy (remove one point from S^3-zonal, or from any compact triple).
  L²(μO) ≅ L²(μZ) unitarily; Friedrichs semigroup, Γ, L, Γ₂, LS constants are literally transported. The statement is equivalent to `sphere_LS_dim`.

### F2 (MEDIUM, doc overclaim) R17-1 and GAPS "supersedes/updates the scope note of Round 16 Ext"
* ERRATA R17-1: "Supersedes the 'no non-compact witness' scope notes" and GAPS: "This updates the scope note of Round 16 'Ext' (there was no non-compact application)".
  The R16 scope note said the NON-COMPACT CONTENT of the theorem is not exercised. After R17 it is still not exercised (F1). The R16 note should be kept, with R17 as a
  topological-only remark. (R17-2 and the GAPS "Caveat" partly mitigate, which is to the author's credit, but the "supersedes" wording is wrong.)
* Also `Main.lean` docstring "BGL Thm 5.7.4 on a non-compact state space" and statements file N8/title "on a non-compact state space" are the over-selling phrasing; qualify with "topologically".

### F3 (MEDIUM, false/overbroad math statement in docs) "the ONLY BGL examples with ρ>0, n<∞ are Jacobi/Gegenbauer on (-1,1)" and "finite-n hypotheses force compactness"
* STATEMENTS §0, AUDIT §1, ERRATA R17-3, GAPS: "ONLY ... Jacobi/Gegenbauer on (-1,1)". False as stated: BGL's finite-n CD(ρ,n), ρ>0 examples include compact
  weighted manifolds with Ric_n ≥ ρ (S^n itself, SO(n), CP^n, compact Lie groups, products with care), Jacobi with other parameters, simplex/Dirichlet-Kimura
  diffusions, etc. What is true: among the NON-COMPACT-TOPOLOGICAL-STATE-SPACE examples of the library's own families (EllData/RiemData/GibbsRdData/OU/Laguerre/Student)
  none has ρ>0, n<∞ (needs d_Γ-completeness, which Bonnet-Myers forbids). The doc conflates "state space of a Markov triple" with "support of μ".
* Bonnet-Myers: CD(ρ,n), ρ>0, n<∞ ⇒ intrinsic diameter ≤ π√((n-1)/ρ) is correct (here equality: diameter π, ρ=2, n=3). The step "complete + bounded = compact (Hopf-Rinow type)"
  is valid only for proper/locally compact length spaces (Riemannian charts); in an abstract Markov triple there is no completeness assumption (the triple only needs the
  ESA/core property), and the paper's own instance proves the finite-n LSI hypotheses do NOT force compactness of the state space: it is the open interval, incomplete
  for d_Γ, with Thm 5.7.4's hypotheses satisfied. The honest statement is: "finite-n CD with ρ>0 forces bounded d_Γ (hence compact support of μ when the state space is d_Γ-complete/proper)".
  The pre-existing `AUDIT_BE.md:39` ("finite-dimensional ρ>0 forces compactness") has the same imprecision (LOW; pre-R17).
* The ESA remark (C_c^∞(-1,1) is ESA only for Gegenbauer dimension ≥ 4) is correct (Bessel ν=(n-2)/2 ≥ 1); S^3 zonal is limit-circle at the poles, so with test algebra C_c^∞ the
  Friedrichs choice would be a genuine choice and the triple would NOT be Standard. The chosen 𝒜 (smooth up to poles) sidesteps exactly this. The docs do say so (limit 1).

### F4 (LOW, process) "Written BEFORE any proof" not verifiable
* The statements file exists in one commit only (b04fe42, together with proofs) and already contains a "Status (written after the proofs)" section; ERRATA R17-4 admits the manifest
  hash was regenerated for it. Pre-registration claim ("proposed before the proofs; N1-N9 proved as stated") rests on author's word. No weakening was found against the Lean (N1-N9 match), so
  no harm, but the sha256 in the manifest pins the post-proof file.

### F5 (LOW, doc) Book numbering unchecked
* "Def. 3.3.26 (Compact Markov Triple)", "Sect. 5.7 p. 272", "Thm 5.7.4 applies to S^n", Bonnet-Myers location are cited from memory/repo notes; neither author nor I could check the book. The ERRATA/AUDIT say so
  (good), but STATEMENTS_R17 and `Main.lean` cite them as facts.

## Mathematical value, honestly
* New: none analytically. A correct Lean proof that the library's Full-triple/CD/LSI pipeline is insensitive to deleting a conull open set, and one more `FullTriple` inhabitant
  (L²-transport lemmas `restrL`, `RO_restrC`, `PO_restrC` are reusable for any conull-restriction).
* It does not respond to the real question "is there a Thm 5.7.4 application where compactness is genuinely absent (𝒜 ≠ 𝒜₀, unbounded functions, incomplete-vs-complete issues)". By Bonnet-Myers
  (diameter bound) that cannot happen for d_Γ-complete spaces; the only room is incomplete-d_Γ spaces with 𝒜 ⊋ 𝒜₀, e.g. test algebra C_c^∞(-1,1) with n ≥ 4 (genuinely ESA, genuinely different 𝒜₀ ⊂ 𝒜), which is NOT built.
  That would be the meaningful follow-up (Gegenbauer n≥4 with 𝒜₀ = C_c^∞(-1,1), 𝒜 = smooth up to boundary).
* Therefore: keep the result as "sanity/consistency, topological only"; do not cite as a non-compact application.

## Required doc edits (not applied; auditor does not fix)
1. R17-1 / GAPS: replace "supersedes/updates the R16 scope note" by "R16 scope note stands; R17 adds a topologically non-compact (A = A₀) instance, which does not exercise the ext step".
2. Replace "ONLY BGL examples ρ>0,n<∞ are Jacobi/Gegenbauer on (-1,1)" by the restricted claim in F3; drop "force compactness" (also AUDIT_BE.md:39).
3. State in STATEMENTS/AUDIT that `FullTriple` has no topology, so "non-compact" is not a hypothesis/conclusion of any formal statement.
