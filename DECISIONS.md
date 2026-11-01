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
