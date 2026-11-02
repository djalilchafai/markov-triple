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
| Prop 3.3.16–3.3.17 (integrated) | `Theory/Gamma2Integral` | proved |
| Prop 3.3.16 (i)–(iii), operator level (`Γ`, `Γ₂` on `𝒟(L)`, `L¹`) | `FullTriple.gamma_limits` (`Theory/Extension/`) | proved; Hessian (iv)–(viii) and Prop 3.3.17 open |
| (3.3.4) Hessian product rule; (3.3.6) reinforced CD | `FullTriple.Γ₂_mul_left`, `FullTriple.reinforced_cd` (`Theory/Strong/`) | proved |
| Poincaré, Lichnerowicz | `poincare_of_CD_infty`, `poincare_of_CD_dim` | proved |
| Cor 3.3.19 (weak form) | `gradient_bound` | cond. on `GradientInterpolation` (discharged: compact, OU); Lebesgue: `Lebesgue.lebesgue_hasGradientBound` |
| **Thm 3.3.18 (strong form)** | `FullTriple.strong_gradient_bound` | cond. on `StrongInterpolation`, `ρ ≥ 0` (discharged: `CompactTriple.strongInterpolation`, `ouFull_StrongInterpolation`); `compact_strong_gradient_bound`, `ouFull_strong_gradient_bound`, `circle_/ouBCompact_/sphere_strong_gradient_bound`, `lebesgue_strong_gradient_bound` |
| log-Sobolev from CD(ρ,∞) | `logSobolev_of_CD_infty` | cond. on `EntropyInterpolation` (discharged: OU) |
| Def 3.3.9 completeness, Lebesgue / OU | `lebesgueDiffusion_isComplete`, `ouDiff_isComplete` | proved |
| Thm 3.3.23, infinite μ | `ExtendedAlgebra.conservative_of_complete`, `isFiniteMeasure_of_complete`; non-compact applications `lebesgue_conservative_of_complete`, `ouFull_conservative_of_complete` | proved (cond. on weak gradient bound, available for compact, OU, Lebesgue) |
| Instances | `Circle.circleCompact`, `Lebesgue.lebesgueFull`, `OU.ouFull`, `Instances.OUCompact.ouBCompact`, `Instances.Sphere.sCompact` (zonal `S³`, compact `[-1,1]`, `CD(2,3)`: `sphere_CD_two_three`; `sphere_PI'`, `sphere_LS`, `sphere_gradient_bound`, `sphere_fisher_decay`) | proved |
| Gaussian PI / LSI | `OU.ouFull_LS`, `ouFull_gradient_bound` | proved, unconditional |
| Gibbs `e^{-V}dx` on ℝ (partial); finite-state obstruction | `Instances.Gibbs.GibbsData.gibbsDiff` (`DiffusionTriple`, D1–D8), `gibbsDiff_isComplete`, `gibbsDiff_Γ₂_ge` (`Γ₂ ≥ ρΓ` for `V'' ≥ ρ`), `Gibbs.gibbs_convex`, `ouData_μ` (V=x²/2 gives γ); `Discrete.finite_Γ_ae_zero`, `finite_L_ae_zero`, `finite_standard_const` | proved; Standard/Full/Compact Gibbs triple NOT built (needs S10, S11, F8, F10 for general V); finite-state generators are not diffusions |
| Gibbs Poincaré / ESA / S10 (Prop 3.2.1, 3.3.10, 4.8.3 route), Full triple | `GibbsData.gibbsDiff_esaProp`, `gibbsDiff_ergodic`, `gibbs_poincare`, `gibbs_spectralGap`, `gibbs_expDecay`, `gibbsFull`, `gibbsFull_CD` (`Instances/Gibbs/Funct*.lean`) | proved under the explicit hypotheses `WeakHypoEllipticAt 0/1` (BGL Def 3.3.8) and, for `gibbsFull`, `F8`; LSI/gradient bound: cond. on `EntropyInterpolation`/`GradientInterpolation` |
| Friedrichs extension, resolvent, generator, CFC semigroup (D7/D9 machinery) | `MarkovTriple.Hilbert.FormData.*` in `BGL/Analysis/Hilbert/` (fenced by `check_frozen.py`) | proved |
| Hermite / Mehler analysis behind OU | `MarkovTriple.Sanity.OU.*` in `BGL/Analysis/OU/` (namespace kept from the removed legacy surface) | proved |

Note: the legacy first surface (`Frozen/`, `Sanity/`, `FunctionalInequalities/`) no longer exists; see DECISIONS 17. All names above
live in `MarkovTriple/BGL/`.
