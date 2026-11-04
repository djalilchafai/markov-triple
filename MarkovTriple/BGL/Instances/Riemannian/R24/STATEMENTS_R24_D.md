# STATEMENTS R24-D: `Core2` (ESA of `L²` on `𝒜₀`) via the BGL / Bakry route; obstruction where it fails

Statements fixed BEFORE the proofs (Armstrong method).  Files: `R24/Core2Criterion.lean`, `R24/GoCore2.lean`,
(`R24/GoSeries*.lean`, `R24/GoPair.lean` if reached), `R24/HypStatus.lean`, `R24/AxiomCheckR24D.lean`.

## Mathematical analysis (what BGL gives, what hypotheses hold where)

* BGL does not treat `Core2` (ERRATA R15-1).  The route "Γ₂ ≥ ρΓ + completeness ⇒ Γ-cut-off ⇒ Core2" is the library's
  `CutFamily` route: `Core2` follows from `Curv ρ` + a cut-off family with bounded `Γχ, Lχ, L²χ, Γ(Lχ), Γ₂χ`.
  `Curv ρ` alone controls only `Γ₂χ` from below through the Bochner formula; the errors `[L,χ_n]v` need `Lχ_n, L²χ_n` bounded,
  and `Γ₂ ≥ ρΓ` gives nothing on `Lχ_n`.  There is no abstract implication "complete + CD(ρ,∞) ⇒ Core2" in the book.
* Available for `hypRiem` (hyperbolic plane with weight `W = 2 cosh d`): `Curv 1`, `CD(1,∞)`, Poincaré `PI 1`, completeness,
  the converse of Prop. 3.3.17 WITHOUT `Core2` (R20).  NOT available: `CoreCut` (by hand, AUDIT_R19 §6), `RadialJets` for `V`,
  `log(1+V)` (R22-E4: `hyp_not_radialJets_*`, `L V = -V² + 2V + 4`).  (The weight makes the Bakry-Emery curvature `+1`, not `-1`: the
  unweighted hyperbolic plane, `W = 0`, is not an `EllData`/`FullTriple` in the library, R22-E4 part N.)
* `Core2` for the abstract class "F1–F10 + CD" is FALSE (new, part B): `goFullTriple` (non-complete).

## Targets

### Part A (abstract, any `FullTriple`)  [PROVED, `Core2Criterion.lean`]
```lean
namespace MarkovTriple.BGL.FullTriple
theorem core2_orth {T : FullTriple E} (hC : T.Core2) (g h : Lp ℝ 2 T.μ)
    (hb : ∀ b : T.A₀, inner ℝ (T.toDiffusionTriple.cls b - T.toDiffusionTriple.Lcls b) g +
      inner ℝ (T.toDiffusionTriple.Lcls b - LLₗ T b) h = 0) (a : T.A₀) :
    inner ℝ (T.toDiffusionTriple.cls a) g + inner ℝ (T.toDiffusionTriple.Lcls a) h = 0
theorem core2_iff_dense {T : FullTriple E} : T.Core2 ↔ Dense (Set.range (Ψₗ T))
```

### Part B (counterexample to `Core2` for a non-complete triple satisfying F1–F10 and `CD(3,4)`)
```lean
namespace MarkovTriple.BGL.Instances.GegenbauerOpen
-- B1 [PROVED, GoCore2.lean]: a deficiency pair refutes Core2
theorem go_not_core2_of_pair (w h : ℝ → ℝ)
    (hw : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1))
    (hh : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1))
    (hwL : ∀ x ∈ Ioo (-1 : ℝ) 1, goL w x = w x)
    (hh2 : MemLp h 2 goμ) (hg2 : MemLp (fun x => w x - goL h x) 2 goμ)
    (hne : ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0) : ¬ goFullTriple.Core2
-- B2 [ATTEMPT]: the pair exists (even power-series solution of L w = w, h = α log(1-x²))
theorem go_deficiency_pair : ∃ w h : ℝ → ℝ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w (Ioo (-1 : ℝ) 1) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h (Ioo (-1 : ℝ) 1) ∧ (∀ x ∈ Ioo (-1 : ℝ) 1, goL w x = w x) ∧
    MemLp h 2 goμ ∧ MemLp (fun x => w x - goL h x) 2 goμ ∧ ∃ x ∈ Ioo (-1 : ℝ) 1, w x ≠ 0
-- B3 [ATTEMPT]: Core2 fails for goFullTriple
theorem goFullTriple_not_core2 : ¬ goFullTriple.Core2
-- B4 [ATTEMPT]: hence F1–F10 + CD do not imply Core2
theorem exists_fullTriple_cd_not_core2 : ∃ T : FullTriple ℝ, T.CD 3 4 ∧ ¬ T.Core2
```

### Part C (hyperbolic plane; packaging, `HypStatus.lean`)
```lean
theorem hyp_core2_route_status :
    hypRiem.Curv 1 ∧ hypRiem.riemFull_unconditional.CD 1 ∞ ∧
    (∀ α β : ℝ → ℝ, ¬ RadialJets hypRiem.toEll Hyp.V α β) ∧ (∀ α β : ℝ → ℝ, ¬ RadialJets hypRiem.toEll Hyp.psi α β)
```
NOT targeted: `hypRiem.riemFull_unconditional.Core2`, `hypRiem.toEll.CoreCut`, `Core2` for general smooth `V`, `Core2` for a COMPLETE
triple with CD (neither proved nor refuted; by hand it is expected to be true for `hypRiem`, see GAPS).

## DIFFERENCE FROM BGL
BGL (p. 161-162) uses `Core2` tacitly (R15-1).  Parts A/B are not in the book: A is the dual (Hahn-Banach) form of `Core2`;
B is a counterexample in the library's framework showing the tacit step is not a consequence of Def. 3.3.x + CD, so
the book's converse proof of Prop. 3.3.17 is incomplete for non-complete triples (it is rescued by completeness, R20).

## Status
All targets A1, A2, B1, B2, B3, B4, C1 PROVED as stated (statement section unchanged; the `[ATTEMPT]` tags of B2-B4 were resolved positively).
Names as proved (axioms: only propext, Classical.choice, Quot.sound; `AxiomCheckR24D.lean`; no sorry, no set_option, 0 warnings):
`MarkovTriple.BGL.FullTriple.{core2_orth, core2_iff_dense}` (`Core2Criterion.lean`, plus helpers `inner_cls_f, inner_Lcls_f, inner_LL_f`);
`MarkovTriple.BGL.Instances.GegenbauerOpen.{go_not_core2_of_pair, go_deficiency_pair, goFullTriple_not_core2, exists_fullTriple_cd_not_core2}`
(`GoCore2.lean`, `GoPair.lean`; helpers in `...GegenbauerOpen.R24` : power-series calculus `GoSeries.lean` (`hasDerivAt_P`, `contDiffOn_P`, `ode_series`),
`holder`, `g_bound`, `memLp_go`, `s_log_sq_le`); `MarkovTriple.BGL.Instances.Riemannian.hyp_core2_route_status` (`HypStatus.lean`).
Extra (not in the statement list, logged as a deviation): `hyp_core2_of_coreCut : hypRiem.toEll.CoreCut → hypRiem.riemFull_unconditional.Core2` (a one-line instance of R19 `riem_core2`).

### The counterexample, mathematically (B2/B3)
`goFullTriple` = zonal Gegenbauer `λ = 3/2` on `(-1,1)`, `L = (1-x²)∂² - 4x∂`, `μ = (3/4)(1-x²)dx`, `𝒜₀ = C_c^∞((-1,1))` (non-complete, `CD(3,4)`, F1-F10).
`w = Σ aa_n xⁿ` solves `L w = w` (`aa_0 = 1, aa_1 = 0, aa_{n+2} = aa_n (1 - 1/((n+1)(n+2)))`, so `w` is even, `w(0) = 1`);
`(1-x²) w = A(x) = Σ dd_n xⁿ`, `|A(x) - Λ| ≤ C₀ √(1-x²)` (`dd_n = O(n⁻²)`), `Λ = A(±1)`; `h = (Λ/4) log(1-x²)` has `L h = (Λ/4)(6x²-2)/(1-x²)`,
so `g = w - L h` satisfies `(1-x²) g² ≤ (C₀ + 6|Λ|/4)²` (bounded), hence `g, h ∈ L²(μ)`.  The functional `ℓ(c) = ⟨c,g⟩ + ⟨Lc,h⟩` vanishes on `(1-L)𝒜₀` (integration by parts,
`Lw = w`) and equals `∫ a w dμ` on `a ∈ 𝒜₀`; it is `L`-graph-continuous, so `Core2` (`(1-L)𝒜₀` is graph-dense, i.e. `(1-L)b_n → a`, `L(1-L)b_n → La`) would force `∫ a w = 0` for all `a ∈ 𝒜₀`,
contradicting `w ≢ 0`.  This is the classical "borderline" mechanism: the singular solution `(1-x)^{-1}` of `L u = su` is not in `L²(μ)` (so `L` is e.s.a., F10) but the
combination `w - L h` (a difference of two singular solutions at different spectral parameters, with `log` corrections) is, so the deficiency space of `L²` is non-trivial.

## Proposed ERRATA rows (applied in ERRATA.md)
R24-D-1 .. R24-D-4 (see ERRATA.md).

