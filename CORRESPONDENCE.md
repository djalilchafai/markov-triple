# Correspondence with Bakry–Gentil–Ledoux (paraphrased; labels are the book's §3.4 labels)

Status: **proved** = Lean theorem, no extra hypothesis beyond the stated ones; **cond.** = proved from a named regularity structure.

| Book | Lean (namespace `MarkovTriple.BGL`) | Status |
|---|---|---|
| D1–D8, Def 3.1.1 | `DiffusionTriple` | structure (frozen, proposed) |
| D4, (3.1.1), (3.1.8) | `exists_bound_D4`, `fundamental_identity`, `chain_rule_L` | proved |
| D7, D9 | `DiffusionTriple.semigroup/.generator`, `generator_iff_form` | defined / proved |
| positivity, sub-Markov (Prop 3.1.6-type facts) | `semigroup_nonneg`, `semigroup_le_one` | proved |
| S10 ergodic | `StandardTriple.ergodic`; `ergodic_iff_energy` | field / proved equivalence |
| S11 conservative; Def 3.1.12 | `StandardTriple.conservative`; `conservative_all`, `conservative_iff_semigroup_one` | field / proved transfer |
| mass conservation, finite μ | `Theory/ESAOne`: `conservative_of_esa` | proved (ESA alone) |
| F1–F10, Def 3.3.1, 3.3.25 | `FullTriple` | structure (frozen, proposed) |
| Def 3.3.26 compact; ESA automatic | `CompactTriple`, `esa_auto` | proved |
| Def 3.3.12, 3.3.14 | `Γ₂`, `FullTriple.CD` | defined |
| Prop 3.3.16–3.3.17 (integrated) | `Theory/Gamma2Integral` | proved (operator-level extension not done) |
| Poincaré, Lichnerowicz | `poincare_of_CD_infty`, `poincare_of_CD_dim` | proved |
| Thm 3.3.18 (weak form) | `gradient_bound` | cond. on `GradientInterpolation` (discharged: OU) |
| log-Sobolev from CD(ρ,∞) | `logSobolev_of_CD_infty` | cond. on `EntropyInterpolation` (discharged: OU) |
| Thm 3.3.23, infinite μ | — | not done (needs completeness, Def 3.3.9) |
| Instances | `Circle.circleCompact`, `Lebesgue.lebesgueFull`, `OU.ouFull` | proved |
| Gaussian PI / LSI | `OU.ouFull_LS`, `ouFull_gradient_bound` | proved, unconditional |
| Friedrichs extension, resolvent, generator, CFC semigroup (D7/D9 machinery) | `MarkovTriple.Hilbert.FormData.*` in `BGL/Analysis/Hilbert/` (fenced by `check_frozen.py`) | proved |
| Hermite / Mehler analysis behind OU | `MarkovTriple.Sanity.OU.*` in `BGL/Analysis/OU/` (namespace kept from the removed legacy surface) | proved |

Note: the legacy first surface (`Frozen/`, `Sanity/`, `FunctionalInequalities/`) no longer exists; see DECISIONS 17. All names above
live in `MarkovTriple/BGL/`.
