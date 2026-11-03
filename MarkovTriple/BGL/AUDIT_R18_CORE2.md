# AUDIT R18 Stream A2: `Core2` for 1-D Gibbs triples WITHOUT bounded `V'` (hostile self-audit, Armstrong method)

Statements fixed BEFORE the proofs in `Instances/Gibbs/STATEMENTS_R18_Core2.md` (registered `proposed` in `frozen-manifest.json`;
three logged generalisations R18-D1..D3 in its Status section, no weakening; ERRATA R18-1..R18-4).
Files: `Instances/Gibbs/{Core2Weighted,Core2WCut,Core2WMain,Core2WExample,AxiomCheckR18Core2}.lean` (R17 files untouched).
Reference: BGL (PDF found: `Bakry & Gentil & Ledoux - Analysis and Geometry of Markov Diffusion Operators.pdf`, Jeanne/bibliographie backup),
Prop. 3.2.1 (ESA by Caccioppoli with the cut-offs `ζ_k`, `Γ(ζ_k) ≤ 1/k`), Def. 3.3.9, Prop. 3.3.17 p. 161-162 (the converse needs `Core2`, ERRATA R15-1).

## The obstacle and how it is removed
R17 needed `V', V'', V'''` bounded; `V' ` bounded contradicts `V'' ≥ ρ > 0` (ERRATA R17-M1), so the R17 converse was vacuous for `ρ > 0`.
The R17 cut-off scheme is kept (`b_n = χ_n v`, `v = (1-L)^{-1}a`, commutators `L(χv) - χLv`, `L²(χv) - χL²v` = `Σ_j χ^{(j)} × (jet of v)`,
`j = 1..4`) but the *coefficients* are no longer bounded: they are `χ_n^{(j)}` (bounded, `Good`) times *weighted jets*
`W ∈ {v, V'v, (V'V''-V''')v, (V'²-2V'')v, v', V''v', V'v', v'', V'v'', v''', V'Lv}` that must lie in `L²(μ)`.  Two integral estimates, both with
cut-offs and the exact IBP `∫(P' - V'P)dμ = 0`, `P = η²V'f²` (`hardy_ibp`; this is `ibp_master` for the test function `x ↦ x`), give them:

* **(BE)** `memLp_of_BE`: `f ∈ L²`, `f' - V'f ∈ L²`, `V'' ≥ -Cw(1+|V'|)` ⇒ `V'f ∈ L²`.  The 1-D Bochner mechanism: with `t = ηV'f`,
  `t² = H - η²V''f² - 2η'ft - 2tηq` (`H = P' - V'P`, `∫H dμ = 0`, `q = f' - V'f`) and the lower bound on `V''` (`Γ₂(f) = f''² + V''f'² ≥ ρf'²`)
  absorbs everything; only `|η'| ≤ K` (cut-off gradient, BGL Def. 3.3.9) appears, never `Lη`, `V'η'`.  Used for `f = v'` (`f' - V'f = Lv = v - a`) and `f = v''`
  (`f' - V'f = v' - a' + V''v'`).
* **(Hardy)** `memLp_of_hardy`: `f, f' ∈ L²`, `V'' ≤ V'²/4 + B` ⇒ `V'f ∈ L²` (`∫V'²f²dμ = ∫V''f²dμ + 2∫V'ff'dμ`).  Used for `f = v`, `f = V'v`.
* `memLp_mul_growth`: `|c| ≤ C(1+|V'|)`, `g, V'g ∈ L²` ⇒ `cg ∈ L²`.

Hypothesis `GibbsData.GrowHess`: `∃ C, ∀ x, |V''| ≤ C(1+|V'|) ∧ |V'''| ≤ C(1+|V'|)`.  It implies `V'' ≥ -C(1+|V'|)` (BE) and `V'' ≤ V'²/4 + C + C²`
(Hardy).  `BddHess` (`V'', V'''` bounded) implies `GrowHess`; `BddJet` implies `BddHess`.

## What is proved (names in `MarkovTriple.BGL.Instances.Gibbs`, all with axioms `propext`, `Classical.choice`, `Quot.sound` only)
* `GibbsData.hardy_ibp`, `memLp_of_BE`, `memLp_of_hardy` (`Core2Weighted.lean`), `GibbsData.BddHess`, `GibbsData.GrowHess`, `BddHess.growHess`, `BddJet.bddHess`.
* `GibbsData.resolvent_weighted_L2` (`hb : GrowHess`): `V'v`, `V'(V'v)`, `v'`, `V''v'`, `V'v'`, `v''`, `V'v''`, `v''' ∈ L²(μ)`.
* `GibbsData.cutoff_ZL_w` (`hb : GrowHess`): `χ_n v → v`, `L(χ_n v) → Lv`, `L²(χ_n v) → L²v` in `L²(μ)`.
* **`GibbsData.gibbsFull_core2_of_growHess (hb : G.GrowHess) : G.gibbsFull_unconditional.Core2`** and the corollary `gibbsFull_core2_of_bddHess`.
* **`GibbsData.gibbs_mem_domain_of_Γ₂_growHess`** / `_bddHess`: the converse of BGL Prop. 3.3.17 (p. 162), no `Core2` hypothesis, hypotheses
  `GrowHess`, `∀ x, ρ ≤ V''`, `f ∈ 𝒜`, `f ∈ L²(μ)`, `Γ(f), Γ₂(f) ∈ L¹(μ)`; conclusion `[f] ∈ 𝒟(L)`, `L[f] = [L f]` a.e.  `ρ` is ANY real
  (in particular `ρ > 0` is allowed, where R17 was vacuous).
* Witnesses (`Core2WExample.lean`):
  * `cosGibbs`, `V = x²/2 + ½ cos x`: `cosGibbs_bddHess` (`|V''| ≤ 3/2`, `|V'''| ≤ 1/2`), `cosGibbs_convex` (`V'' = 1 - ½cos x ≥ ½`, i.e. `CD(½,∞)`),
    `cosGibbs_not_bddJet` (`V' = x - ½ sin x` unbounded: the R17 theorem did not apply), `cosGibbs_core2`, `cosGibbs_mem_domain_of_Γ₂` (instance of the
    converse with `ρ = ½ > 0`).
  * `quarGibbs`, `V = x⁴/4 + x²/2`: `V'' = 3x²+1 ≥ 1` (`quarGibbs_convex`, `ρ = 1`), `quarGibbs_growHess` (`C = 6`), `quarGibbs_not_bddHess`
    (`V''' = 6x`), `quarGibbs_core2`, `quarGibbs_mem_domain_of_Γ₂`.

## Hostile attacks
1. *Is `Core2` the right notion?*  Unchanged definition `FullTriple.Core2` (R15), applied to the unchanged `gibbsFull_unconditional`; `core2_of_dense` not needed.
   The converse is the unchanged `FullTriple.mem_domain_of_Γ₂` with `gibbsFull_CD_unconditional`.
2. *Vacuity / contradiction of hypotheses.*  `GrowHess` is consistent with `V'' ≥ ρ > 0` (witnesses above, with explicit `ρ`).  The corresponding Lean facts are
   `cosGibbs_convex : ∀ x, 1/2 ≤ deriv (deriv V) x`, `quarGibbs_convex`.  `ContDiff` smoothness is `Sm` = `ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)` (not analytic; the
   OU `Sm` of the repository), and `V` itself is real-analytic in both examples, which is harmless here.  The converse's own hypotheses (`f ∈ 𝒜 ∩ L²`,
   `Γ(f), Γ₂(f) ∈ L¹`) are satisfied by `f ∈ C_c^∞` (not re-formalised for these `V`); they are the unchanged hypotheses of R15.
3. *Does (BE) secretly use more than the stated bounds?*  The pointwise lemmas `be_pointwise`, `hardy_pointwise` are pure real inequalities with explicit constants
   (checked by `nlinarith` with the displayed square completions); the integral step is `int_bound_aux` with `∫H = 0` from `hardy_ibp`.  The Fatou step is the R17
   `memLp_two_of_cutoff` (bounds uniform in `n`).  Sanity (hand): for `V = x²/2`, (BE) says `f ∈ L²(γ)`, `f' - xf ∈ L²(γ)` ⇒ `xf ∈ L²(γ)`, true by Hermite.
4. *Sign conventions.*  For (BE) the sign of `H` in `t² = H - ...` and for (Hardy) `t² = ... - H` were rederived; both pointwise lemmas are stated with the
   corresponding `s = 8/3` resp. `s = -4` in `int_bound_aux` and typecheck.
5. *The commutator algebra* is R17's `LL_mul_expand` (unchanged, kernel-checked) regrouped into five terms `(χ-1)LLv`, `χ''''v`, `χ'F₁`, `χ''F₂`, `χ'''F₃`
   (`F_i` explicit sums of weighted jets, `L²` by `MemLp` calculus); the regrouping is closed by `ring` after unfolding `cc0..cc4` and `Lg V χ`.
6. *Build hygiene.*  `lake build` of all new modules: 0 errors, 0 warnings, no `sorry`, no `set_option`, no new axiom.  `lakefile.toml`, `lake-manifest.json`,
   `lean-toolchain`, frozen/fenced files untouched; `scripts/check_frozen.py` OK.

## What is NOT proved (exact scope; no overclaiming)
* `Core2` / the converse for `GibbsData` outside `GrowHess`.  Examples outside: `V'' ≳ V'²/4` types such as `V = e^{x²}`-like (`V'' / |V'| ~ 2x` unbounded),
  and any `V` whose `V''` or `V'''` oscillate with amplitude not dominated by `1 + |V'|`.  For these the weights `V''v`, `V'''v`, `V''v'` are not controlled by (BE)/(Hardy).
  The gap to a full characterisation is NOT claimed to be sharp: we have neither a proof nor a counterexample for general smooth `V` (equivalent to ESA of `L²` on
  `C_c^∞`, which is a genuine extra property for wild `V`).  The Caccioppoli identity `∫χ²w² = 2∫χ(wΓ(χ,u) - uΓ(χ,w))` for an `L²` solution `u` of `(1-L)²u = 0`
  alone (R17 audit) still does not close; the route here is the direct one (resolvent + cut-off), which uses the extra growth.
* `ℝ^d` (`EllData`, `GibbsRdData`): not attempted (`d`-dimensional (BE)/(Hardy) would need `∇²v ∈ L²(μ)` and the `Γ₂(ψ,v)` commutators).
* Ergodicity of the book's proof is not used (as in R15/R17).
* ERRATA R17-M1's statement that Core2 is open for `ρ > 0` beyond OU is superseded for `GrowHess` Gibbs potentials: see ERRATA R18-1.
