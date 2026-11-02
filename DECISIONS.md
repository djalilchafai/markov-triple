# Decisions (taken by following the recommendations of PLAN.md §7)

1. Name: repository `markov-triple`, Lean namespace `MarkovTriple`.
2. `MarkovTriple E` is a `structure` (several triples per space are common).
3. `L` and `Γ` are both fields, tied by the POINTWISE carré-du-champ identity
   `Γ f g x = (L (f*g) x - f x * L g x - g x * L f x) / 2` for f g in A₀.
   Integration by parts `∫ g * L f ∂μ = -∫ Γ f g ∂μ` is a field too (or a derived lemma if provable).
4. Curvature is `CD ρ n` with `n : ℝ≥0∞`; the first theorems only use `n = ∞`.
5. `MarkovProcess` (Armstrong) is NOT a dependency of the core; only an optional `Bridge` lean_lib.
6. Time type `ℝ≥0`; kernels are `ProbabilityTheory.Kernel`; real Lᵖ.
7. Pin: Lean/Mathlib `v4.35.0-rc2` (`065356127b1d`).

# Working rules (Armstrong method)

- Statements are FROZEN before proofs: one declaration per file under `MarkovTriple/Frozen/`, listed in
  `frozen-manifest.json` with a SHA-256 of the file; `scripts/check_frozen.py` fails if a hash changes.
- A frozen statement is written by a drafter, attacked by a hostile auditor (who tries to show it is
  vacuous, false, or not BGL's definition, e.g. by exhibiting a degenerate instance or a counterexample), then
  approved by the author. Until the author approves, status is `proposed`.
- A prover never certifies its own work. A separate hostile auditor tries to refute each proved result
  (checks `#print axioms`, vacuity, hypotheses that are secretly contradictory).
- No `sorry` outside `Challenge`-style files, no `axiom`, no `maxHeartbeats` increase, files <= 1500 lines.
  Only `propext`, `Classical.choice`, `Quot.sound` allowed.
- `ERRATA.md` records every flaw found; `CORRESPONDENCE.md` maps BGL numbered results to Lean names + status.

# Amendment (author decision, round 2): follow BGL closely

8. μ is σ-FINITE (not necessarily finite): Lebesgue measure on ℝⁿ must be admissible. Local functional inequalities
   are in scope later. PI/LSI/Ent-type statements keep `IsProbabilityMeasure` where mathematically required.
9. The test class A₀ is NOT required to contain constants (non-unital). Follow BGL Def. 3.1.1–3.1.9 / §3.3–3.4:
   A₀ ⊂ ⋂_{p<∞} Lᵖ(μ) is stable under composition with smooth ψ with ψ(0)=0 (the "diffusion algebra" hypothesis),
   Γ, L are defined and satisfy the chain rule on A₀, and the EXTENDED algebra A (contains constants and A₀,
   stable under all smooth ψ) carries the Γ-calculus in `FullMarkovTriple`. Constants belong to A, not to A₀.
   `ibp` is symmetric (both directions) on the appropriate classes. Positivity of P_t must then be DERIVED
   (ψ_ε(f)=√(f²+ε²)−ε argument), so `IsMarkovianForm` should become a theorem for full triples.
10. Concrete test classes: circle → C^∞(𝕋); OU/Gibbs → smooth functions with polynomial-growth derivatives
    (or C_c^∞); Lebesgue on ℝⁿ → C_c^∞ (this is the new infinite-measure sanity instance).
11. Numbering of BGL results in docstrings is unverified unless checked against the book; never claim otherwise.
12. (round 3) Keep `comp_mem` for all smooth ψ (BGL-faithful). Consequence: A₀ is of bounded type; Gaussian/Gibbs/OU instances use C_c^∞ or Schwartz-type classes (density in Lᵖ still holds).
13. `Wip/` holds work-in-progress files that may contain `sorry`; it is never imported by the root and must be empty of `sorry` before any release.

# Amendment (author decision, round 5): realign to BGL D1–D9, S10–S11, F1–F10

14. The canonical surface is `MarkovTriple/BGL/Frozen/` (namespace `MarkovTriple.BGL`), realigned to the book's hypothesis
    list. The first surface (`MarkovTriple/Frozen/`, fields `ibp_AA`, `IsSemigroupOf`, `BEStable`, split `CD`/`CDFull`,
    range-criterion `esa`) is legacy: not extended, kept for reused analysis. Do not add theorems to the legacy surface.
15. The book's own route (Props 3.3.16–3.3.17, Thm 3.3.18, Thm 3.3.23) replaces `ibp_AA`/`BEStable`. Gradient bound and LSI are
    proved from named regularity structures (`GradientInterpolation`, `EntropyInterpolation`) which are discharged per instance.
16. The book's PDF is reference material only: it must never be committed or quoted (`.gitignore` has `*.pdf`).
17. (legacy removal) The first surface is DELETED: `MarkovTriple/Frozen/`, `Sanity/`, `FunctionalInequalities/` and the
    legacy-structure part of `Hilbert/` (`TripleForm`, `Bridge`, `Closure`, `FullBridge`, `MarkovCriterion`/`SubMarkov`
    remainders, `Sanity`, `AxiomCheck`), together with the legacy audit probes (`MarkovTriple/Audit/*` except the
    Divergences and `HilbertDiagonal` ones).  What `BGL/` still used was PORTED to `MarkovTriple/BGL/Analysis/`, statements
    unchanged, namespaces kept (`MarkovTriple.Hilbert`, `MarkovTriple.Sanity.OU`, `MarkovTriple.Sanity.Circle`, `MarkovTriple.BE`)
    so that declaration names do not change:
    * `Analysis/Hilbert`: Friedrichs extension, resolvent, generator, CFC semigroup, spectral gap, `Existence` (these are
      the fenced definitions of `BGL/Frozen/Semigroup.lean`), `GapFromSquare`, Beurling–Deny / `DirMerge` / `DirBridge`,
      `Contraction` (`exists_contraction_of_approx`, `resolvent_pairing_nonpos`), `Truncation` (smooth `√(t²+δ²)−δ`, smooth clip,
      closedness of `{w ≤ 1}`).
    * `Analysis/OU`: Hermite/Mehler/Gaussian calculus and the abstract semigroup smoothing (`eigen_hL`, `smoothing_ou`, `mehler`).
    * `Analysis/Circle`: Fourier modes, `IsSG`, circle smoothing.  `Analysis/BE`: Grönwall/cut-off lemmas, `tendsto_Ent_add`
      (now stated with `BGL.Ent`).
    Dropped with the legacy structures (nothing in `BGL/` used them): `ouTriple`, `ouFull` (legacy), `ou_CD`, `ou_ergodic`,
    `ou_poincare`, `ou_semigroup_stable`, `mehler_ae` (BGL has `mehler_of_sg`), `ouFull_BEStable`, the legacy `ou_lsi`,
    `circleTriple/circleFull`, `circle_semigroup_stable`, `Hilbert.poincare_of_CD_infty` (legacy; the BGL theorem of the same name
    remains), `BE.logSobolevIneq_of_CD`, `BEStable`, `isMarkovianForm`/`tripleSemigroup` (BGL has its own, `BGL/Semigroup/Markov.lean`),
    legacy Lebesgue sanity.  The `ou_lsi` ⇔ `ouFull_LS` equivalence of `BGL/Audit/LSIUnfold.lean` was dropped; `concrete_lsi` (the
    unfolded Gaussian LSI) is kept.  `Divergences/Entropy.lean` now defines `MarkovTriple.Ent` itself (same formula as `BGL.Ent`)
    instead of importing the legacy `Frozen/Ent.lean`.  `MarkovTriple.pderiv` (legacy) is replaced by the identical `BGL.pderiv`.
    `frozen-manifest.json` lists only `BGL/Frozen`; its `fenced` list is the (renamed) Hilbert files plus `BGL/FormData.lean`, `BGL/Basic.lean`;
    the import-closure check of `scripts/check_frozen.py` still guarantees that every project file the frozen surface
    imports is hashed (the only edits to frozen/fenced files were import lines).

# Amendment (round 11): audit R2 fixes and Thm 3.3.23

18. D1 "good": `DiffusionTriple` gets a field `good : IsGoodMeasure μ` WITH A DEFAULT PROOF (`IsGoodMeasure.of_countablyGenerated`), the most faithful non-breaking encoding (no instance edit; the sphere/Jacobi instance, built concurrently, is covered by the default). Frozen files changed: `Frozen/DiffusionTriple.lean` (field, docstring, import), docs-only edits of `CD`, `CompactTriple`, `StandardTriple`, `Energy`, `Ent`, `Fisher`, `Poincare`, `LSI`; new frozen files `GoodMeasure.lean`, `Complete.lean` (status proposed). Manifest regenerated with `scripts/check_frozen.py --update`.
19. Completeness (Def. 3.3.9) is a predicate on a `DiffusionTriple` (`DiffusionTriple.IsComplete`), not a field. Thm 3.3.23 is proved over `ExtendedAlgebra D A` (a `Prop` bundling the used part of F1–F8) because S11 is a field of `StandardTriple`/`FullTriple` (Thm 3.3.23 would be vacuous there). The gradient bound enters as the hypothesis `HasGradientBound D A ρ`.

# Amendment (round 12): strong gradient bound, completeness of Lebesgue/OU, Γ₂ extension

20. No frozen file was changed (check_frozen OK).  Thm 3.3.18 is proved with `CD ρ n` (book: CD(ρ,∞)), `ρ ≥ 0`, from the
    Prop-structure `StrongInterpolation` (analytic regularity only; the reinforced CD (3.3.6) is proved, not assumed).  It is
    discharged for all `CompactTriple`s and OU; Lebesgue by the explicit heat kernel (Jensen).  Strong bound `ρ < 0`, the
    Hessian part of Props 3.3.16 and Prop 3.3.17, and a generic non-compact discharge are documented gaps (`Theory/GAPS.md`).

# Closure of the PLAN.md §7 open decisions (round 13)

Each entry records what the implemented canonical surface `MarkovTriple/BGL/Frozen/` already commits to, or, where the
code is silent, a recommendation.  Entries marked "recommended, pending author approval" are the author's call; nothing
was renamed.

21. Structure vs class: DECIDED = `structure` (confirms 2).  `DiffusionTriple`, `StandardTriple extends DiffusionTriple`,
    `FullTriple extends StandardTriple` and `CompactTriple` are all `structure`s taking `E` and `[MeasurableSpace E]`
    only (`BGL/Frozen/DiffusionTriple.lean:44`, `StandardTriple.lean:31`, `FullTriple.lean:26`); they are passed explicitly
    (`T : FullTriple E`), e.g. `FullTriple.CD`, `FullTriple.poincare_of_CD_dim`.  Several triples on one space occur
    in the code (circle/OU/sphere/Lebesgue instances, the OU Gibbs variants `ouBCompact`).
22. L and Γ: DECIDED = both are fields (confirms 3, with a CORRECTION to 3).  `DiffusionTriple` has `Γ` and `L` as fields
    and is tied by D5, the integrated identity `ibp : ∫ g * L f ∂μ = -∫ Γ f g ∂μ` for `f g ∈ A₀`, plus `integral_L`,
    `Γ_symm`, `Γ_add`, `Γ_smul`, `Γ_nonneg`, `diffusion` (`DiffusionTriple.lean:70-96`).  The POINTWISE carré-du-champ identity
    stated in 3 is NOT a field; it is derived (`fundamental_identity`, `chain_rule_L`, BGL (3.1.1)/(3.1.8)).  Both
    `Γ` and `L` are total functions `(E → ℝ) → (E → ℝ)` with junk off `A₀`; `ΓA`/`Γ₂` are defined on the extended algebra
    (`Frozen/GammaA.lean`, `Gamma2.lean`).  Decision 3's pointwise wording is superseded by this entry.
23. Finite-dimensional CD(ρ,n): DECIDED = in scope (confirms 4).  `FullTriple.CD (T) (ρ : ℝ) (n : ℝ≥0∞)` is
    `1 ≤ n ∧ ∀ f ∈ A, Γ₂ f f ≥ ρ Γ f f + n⁻¹ (L f)²` a.e. (`BGL/Frozen/CD.lean:20`); `n = ∞` is the BGL CD(ρ,∞).
    Finite n is used by the proved results `poincare_of_CD_dim` (Lichnerowicz, `Theory/Poincare.lean`), `sphere_CD_two_three`
    (zonal S³, CD(2,3)), `sphere_PI`, `sphere_LS`, `sphere_gradient_bound` (`Instances/Sphere/Consequences.lean`).
    Theorems needing only ρ use `n = ∞`/any n (e.g. Thm 3.3.18 takes `CD ρ n`, see 20).  Remaining gaps (Hessian part of
    Prop 3.3.16, Prop 3.3.17, strong bound for ρ<0, generic non-compact discharge) are in `Theory/GAPS.md`, not scope questions.
24. MarkovProcess dependency: DECIDED = no dependency (confirms 5).  `lakefile.toml` requires only Mathlib
    (`v4.35.0-rc2`) and declares a single `lean_lib MarkovTriple`; no `.lean`, `lakefile.toml` or manifest entry refers to
    `MarkovProcess`.  The semigroup is built inside the repository (`BGL/Analysis/Hilbert`: Friedrichs extension, resolvent,
    CFC semigroup; `BGL/Semigroup`).  The optional bridge is NOT implemented; if written later it must live in a separate
    `lean_lib` (e.g. `MarkovTripleBridge`) so that the core stays independent.
25. Repository / library / namespace name: STATE = `markov-triple` (repo), `MarkovTriple` (lean_lib; lakefile package
    name `markovTriple`), `MarkovTriple.BGL` (canonical namespace), `MarkovTriple.Hilbert/.Sanity/.BE` (ported
    analysis, namespaces kept by 17), `MarkovTriple.Ent` (Divergences).  This is what all ~hundreds of files, the
    frozen manifest hashes, `CORRESPONDENCE.md` and the audit documents use.
    DECIDED (author, 2026-11-03): keep these names as they are (repo `markov-triple`, library `MarkovTriple`, namespace
    `MarkovTriple.BGL`; no rename of the `BGL` sub-namespace).  Rationale recorded before the decision: (a) `MarkovTriple` is the Armstrong-style
    descriptive name already used in docs and by the statement `structure`s; (b) the library contains Divergences and
    non-BGL analysis, so a narrower name like `BakryEmery` would be misleading, while a broader one like
    `DiffusionOperators` collides in scope with the book's subject; (c) a rename touches every frozen/fenced file and
    forces a manifest regeneration, which is wasteful before the author has approved any frozen statement.  Caveat for
    the author: the namespace `MarkovTriple.BGL` bakes the book's initials into declaration names; if the library is ever
    submitted to Mathlib or Reservoir, a rename of `BGL` (e.g. to `BakryEmery`) is a mechanical, one-time change, best done
    BEFORE author approval freezes the hashes.  (Caveat retained for the record; the author chose not to rename.)
