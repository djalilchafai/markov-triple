# AUDIT R19 Stream A4: `Core2` for 1-D Gibbs triples beyond `GrowHess` (hostile self-audit, Armstrong method)

Statements fixed BEFORE the proofs in `Instances/Gibbs/STATEMENTS_R19_Core2.md` (registered `proposed` in `frozen-manifest.json`, no deviation;
ERRATA R19-1..R19-3).  Files: `Instances/Gibbs/{Core2PolyW,Core2PolyCut,Core2PolyMain,Core2PolyExample,AxiomCheckR19Core2}.lean`
(R17/R18 files untouched).  Reference: BGL Prop. 3.2.1 (p.142), Def. 3.3.9, Prop. 3.3.17 (p.161-162; ERRATA R15-1).

## Verdict on the goal "remove `GrowHess`, use only `V'' ≥ ρ`"
NOT achieved in full generality; precise obstruction and maximal true strengthening proved.
* Math facts (all in the plan of the statements file).  (i) e.s.a. of `L` on `C_c^∞` holds for EVERY `V` (Caccioppoli with `ζ_k(x) = ζ(x/k)`, BGL 3.2.1: in 1-D the intrinsic
  distance is Euclidean), so the difficulty is exclusively `Core2` = e.s.a. of `L²` on `C_c^∞` (4th-order limit-point condition, count `m_± = 2` of `L²` solutions of `(1-L)²u = 0`).
  (ii) `Γ₂ ≥ ρΓ` alone gives, with cut-offs, `V'^n v' ∈ L²` for all `n` (BE-w, induction) but only `V''^{1/2}f' ∈ L²` for `f = L^j v`: it never gives `V'''v`, `V'V''v`,
  which occur in `L²(χ_n v) - χ_n L²v` (`LL_mul_expand`: coefficients `V'''χ'v`, `V'V''χ'v`, `V''χ''v`, `V''χ'v'`).  The Caccioppoli identity for an `L²` solution of
  `(1-L)²u = 0`, `∫η²w² = 2∫ηη'(u'w - uw')` (`w = (1-L)u`, `Lw = w`; derived by hand, the `V'` terms disappear by one IBP) does not close either: it is consistent with `w` super-exponentially growing.
* I found NO counterexample and NO proof for general smooth `V` with `V'' ≥ ρ`: `Core2` for that class is OPEN.  Nothing here claims it is false.
* PROVED (maximal strengthening of this route): `PolyHess` (D0).  Strictly contains `GrowHess` (Lean: `GrowHess.polyHess`, `expGibbs_polyHess`, `expGibbs_not_growHess`).

## What is proved (names in `MarkovTriple.BGL.Instances.Gibbs`; axioms `propext`, `Classical.choice`, `Quot.sound` only, checked by `AxiomCheckR19Core2.lean`)
`GibbsData.PolyHess G :=` `(∃ Cw ≥ 0, ∀ x, -(Cw(1+|V'|)) ≤ V'')` ∧ `(∀ ε>0, ∃ B ≥ 0, ∀ x, V'' ≤ εV'² + B)` ∧ `(∃ C N, ∀ x, |V'''| ≤ C(1+|V'|^N))`.
* `hardy_ibp_w` (exact IBP `∫(P' - V'P)dμ = 0`, `P = η²V'ψ²f²`), `memLp_of_BE_w` (hyp. `V''ψ²+2V'ψψ' ≥ -Cw(1+|V'|)ψ²`), `memLp_of_hardy_w` (hyp. `V''ψ²+2V'ψψ' ≤ (V'²/4+B)ψ²`).
* `resolvent_pow_L2`: `∀ n, V'^n v, V'^n v' ∈ L²(μ)` (induction; the weight `ψ = V'^n` has `V''ψ² + 2V'ψψ' = (2n+1)V''V'^{2n}` (`key_pow`), the Hardy step uses `ε = 1/(4(2n+1))`).
* `abs_V2_le` (`|V''| ≤ D(1+|V'|²)` from the first two conjuncts), `memLp_mul_poly`, `resolvent_weighted_L2_poly`, `cutoff_ZL_p` (same output as R18 `cutoff_ZL_w`).
* **`gibbsFull_core2_of_polyHess (hb : G.PolyHess) : G.gibbsFull_unconditional.Core2`**; **`gibbs_mem_domain_of_Γ₂_polyHess`** (converse of Prop. 3.3.17, hyps `PolyHess`, `∀x, ρ ≤ V''`,
  `f ∈ 𝒜`, `f ∈ L²`, `Γ(f), Γ₂(f) ∈ L¹`; conclusion `[f] ∈ 𝒟(L)`, `L[f] = [Lf]`); `gibbs_mem_domain_of_Γ₂_convex` (hyps `V'' ≥ ρ`, `V'' = o(V'²)`, `|V'''| ≤ C(1+|V'|^N)`: the
  first conjunct of `PolyHess` is derived from `V'' ≥ ρ`); `gibbsFull_core2_of_growHess_via_poly` (R18 theorem as a corollary).
* Witness OUTSIDE the old class with `ρ > 0`: `expGibbs`, `V = exp(x²)` (`GibbsData`: smooth via `Real.contDiff_exp.comp`, `Sm = ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)`, i.e. NOT the analytic class;
  `e^{-V}` integrable by `e^{x²} ≥ 1+x²`).  `expGibbs_convex : ∀ x, 2 ≤ V''` (`ρ = 2`, `V'' = (2+4x²)e^{x²}`); `expGibbs_polyHess` (`Cw = 0`; `V'' = o(V'²)` with `B = (2+4M)e^M`,
  `M = max 1 (3/(2ε))`; `|V'''| ≤ 60(1+V'²)`, `N = 2`); `expGibbs_not_growHess` (at `x = |C|+2`: `V'' ≥ 4x²E`, `C(1+V') ≤ 3|C|xE`, contradiction); `expGibbs_core2`, `expGibbs_mem_domain_of_Γ₂`.
  `x⁶/6 + x²/2` is NOT a new witness: `V'' = 5x⁴+1 ≤ C(1+|x|⁵)`, it is inside `GrowHess` (all polynomials are).

## Hostile attacks
1. *Hypotheses contradictory?*  No: `expGibbs` satisfies `PolyHess` and `V'' ≥ 2 > 0` simultaneously, proved in Lean.  `V'' ≥ ρ > 0` with `V'` unbounded is also consistent with R18 witnesses.
2. *Is `PolyHess` secretly implying `GrowHess`?*  No: `expGibbs_not_growHess` (`V''/V' ~ 2x`).  Does it imply `V'' ≥ ρ`?  No (first conjunct allows `V'' ≥ -Cw(1+|V'|)`); the converse uses `∀x, ρ ≤ V''` as before.
3. *Hidden extra hypothesis?*  `resolvent_pow_L2` takes exactly the first two conjuncts; the third (`V'''`) is used only in `cutoff_ZL_p` via `memLp_mul_poly` with `(hpow N).1`.  `Core2` itself is the unchanged R15 definition
   (`FullTriple.Core2`, `Theory/Extension/Converse.lean:237`) applied to the unchanged `gibbsFull_unconditional`.
4. *Pointwise algebra.*  `be_pointwise_w`, `hardy_pointwise_w` are the R18 lemmas with `f → a = ψf`, `f' → d = ψf'`, `V''f² → S = (V''ψ²+2V'ψψ')f²`; the `H` of `hardy_ibp_w` is
   `η²S + 2ηη'V'a² + 2η²V'ad - η²V'²a²` (expanded and closed by `ring`).  Signs: BE uses the LOWER bound on `S`, Hardy the UPPER bound, as in R18.
5. *Cascade logic.*  Step `n → n+1` for `v`: Hardy-w with `f = v`, needs `V'^n v`, `V'^n v' ∈ L²` (induction hypothesis, both components); for `v'`: BE-w with `f = v'`, `q = v'' - V'v' = v - a`, needs
   `V'^n v`, `V'^n a ∈ L²` (compact support).  The two components feed each other, no circularity (the `v'` step uses the `v` component at level `n`, the `v` step uses the `v'` component at level `n`).
6. *Sanity by hand.*  `V = x²/2` (OU): `V'^n v` is the Hermite statement `x^n v ∈ L²(γ)`, true.  For `V = e^{x²}`, `L²`-weights `V'^n` are enormous but only finitely many are used (up to `N + 1`).
7. *Build hygiene.*  `lake build` of each new module: 0 errors, 0 warnings, no `sorry`, no `set_option`, no new axiom; `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, frozen and fenced files untouched
   (manifest: one new `proposed` entry); `scripts/check_frozen.py` OK.  `.lake/build` copied, `.lake/packages` symlinked.

## What is NOT proved (exact scope; no overclaiming)
* `Core2` / the converse for `GibbsData` with `V'''` not polynomially dominated by `V'` (e.g. `V'' = 1 + Σ` unit spikes of super-fast decreasing width: `V' = x + O(1)`, `V'''` arbitrarily large; the cut-off proof then lacks
  `V'''v ∈ L²`), or with `V''` not `o(V'²)` (e.g. `V'' ≳ V'²/4` types).  Whether `Core2` is TRUE there is unknown (no proof, no counterexample).
* General smooth `V` with `V'' ≥ ρ`: open.  `ℝ^d` (`EllData`, `GibbsRdData`), `RiemData`: not attempted here.
* The remark "spiky `V'''` can break (W)" is heuristic, not formalised.
