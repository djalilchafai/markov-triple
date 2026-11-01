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
