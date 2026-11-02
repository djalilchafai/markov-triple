# markov-triple

A Lean 4 / Mathlib library for the Bakry–Émery theory of Markov triples
(Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators*, Ch. 3).

Pinned to Lean `v4.35.0-rc2` / Mathlib `v4.35.0-rc2` (`065356127b`). No `sorry`, no custom axioms;
every public theorem depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Layout

* `MarkovTriple/BGL/` — **the canonical development** (namespace `MarkovTriple.BGL`), aligned with the book's
  hypotheses D1–D9, S10–S11, F1–F10 (`BGL/Frozen/`: `DiffusionTriple`, `StandardTriple`, `FullTriple`, `CompactTriple`,
  `CD`, Poincaré, log-Sobolev, …). See `MarkovTriple/BGL/FROZEN_REVIEW_BGL.md` for every field's book label and our choice.
  * `BGL/Calculus`, `BGL/Semigroup` — fundamental identity, chain rule, positivity, sub-Markov, conservativeness, ESA.
  * `BGL/Theory` — integrated Γ₂ identity, Poincaré / Lichnerowicz, finite-measure mass conservation, gradient bound and
    log-Sobolev from CD(ρ,∞) (under named regularity structures, discharged for the instances below).
  * `BGL/Instances` — circle (`CompactTriple`), Brownian motion on ℝ (Lebesgue), Ornstein–Uhlenbeck; all hypotheses proved.
  * `BGL/Analysis` — analysis ported from the removed first surface (statements unchanged): `Hilbert` (Friedrichs form →
    resolvent → generator → CFC semigroup, spectral gap, Beurling–Deny contraction criterion, truncations), `OU`
    (Hermite/Mehler, semigroup smoothing), `Circle` (Fourier modes, smoothing), `BE` (Grönwall/cut-off, entropy limit).
* `MarkovTriple/Divergences` — entropy/total variation/Wasserstein (independent of `BGL/`).
* The legacy first surface (`MarkovTriple/Frozen`, `Sanity`, `FunctionalInequalities`) was removed (DECISIONS 17).
* `MarkovTriple/Audit`, `MarkovTriple/BGL/Audit` — hostile-audit probes (not imported by the root).

## Method (Armstrong style)

Statements are frozen before proofs (`frozen-manifest.json`, checked by `scripts/check_frozen.py`, which also fences the
definitions the frozen statements depend on). Each stage is attacked by an independent hostile auditor
(`AUDIT_*.md`, `MarkovTriple/BGL/AUDIT_*.md`); findings are in `ERRATA.md`. **All frozen statements are still `proposed`
(not author-approved).**

See `PLAN.md`, `DECISIONS.md`, `CORRESPONDENCE.md`.
