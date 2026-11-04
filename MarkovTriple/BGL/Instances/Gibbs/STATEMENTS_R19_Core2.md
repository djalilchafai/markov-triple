# Round 19, Stream A4 (Gibbs `Core2` beyond `GrowHess`): statements fixed BEFORE the proofs.

Change only by a logged deviation in a `Status` section below and an erratum in `ERRATA.md` (prefix `R19-`).
Setting: `G : GibbsData` (1-D, `μ = Z⁻¹ e^{-V}dx`, `𝒜₀ = C_c^∞`, `L f = f'' - V' f'`), `G.gibbsFull_unconditional : FullTriple ℝ`.
Predecessor: `STATEMENTS_R18_Core2.md` (`Core2` under `GrowHess`: `|V''|, |V'''| ≤ C(1+|V'|)`).

## Mathematical plan (BGL Prop. 3.2.1 cut-off/Caccioppoli, Def. 3.3.9, Bochner `Γ₂ ≥ ρΓ`, Prop. 3.3.17)

`Core2` is (R15 `core2_of_dense`) the graph-norm density of `𝒜₀` in `𝒟(L̄²)`; it reduces (R17/R18) to the cut-off
convergence `χ_n v → v` in the `L²`-graph norm for `v = (1-L)⁻¹a`, `a ∈ 𝒜₀`, i.e. to membership in `L²(μ)` of the weighted jets
(W): `v, V'v, (V'V''-V''')v, (V'²-2V'')v, v', V''v', V'v', v'', V'v'', v''', V'Lv`.  (R18 `cutoff_ZL_w` takes (W) as hypothesis,
proved from `GrowHess`.)  Observations of Round 19:

* **(BE-w)** (only `V'' ≥ -Cw(1+|V'|)`, e.g. `V'' ≥ ρ`; the 1-D `Γ₂ ≥ ρΓ`).  For a smooth weight `ψ` and `P = η² V' ψ² f²`:
  `∫(P' - V'P)dμ = 0` gives `ψ f ∈ L²`, `ψ(f' - V'f) ∈ L²`, `V''ψ² + 2V'ψψ' ≥ -Cw'(1+|V'|)ψ²` ⇒ `V' ψ f ∈ L²`.
  With `ψ = V'^n`: `V'^n v' ∈ L²` for ALL `n` (induction from `v', v'' - V'v' = v - a ∈ L²`), using nothing but `V'' ≥ -Cw(1+|V'|)`.
* **(Hardy-w)** (`V'' ≤ V'²/(4(2n+1)) + B`).  Same identity: `ψ f, ψ f' ∈ L²`, `V''ψ² + 2V'ψψ' ≤ (V'²/4 + B)ψ²` ⇒ `V'ψ f ∈ L²`.
  With `ψ = V'^n`, `f = v`: `V'^n v ∈ L²` for all `n`, provided `V'' = o(V'²)` (`∀ε ∃B, V'' ≤ εV'² + B`).
* Hence all `V'^n v`, `V'^n v'` ∈ `L²`, and the only remaining requirement for (W) is a *polynomial* domination of
  `V'''` (`V''` is automatically `≤ C(1+V'²)` from the two bounds above): `|V'''| ≤ C(1+|V'|^N)`.  `GrowHess` (`N = 1`) is the
  special case; growth `V' ~ e^{x²}` (`V''/V' ~ x → ∞`) is covered.

**Where the route stops (precise obstruction).**  In (W) the coefficient `V'''` (and `V'V''`) multiplies `v` with no
information on `V'''v` from `Γ₂`-integrated estimates: Bochner gives `∫V''(f')² ≤ ∫(Lf)²` (so `V''^{1/2}f' ∈ L²`) but never `V'''` or
`V''f'`.  For a convex `V` with `V'' ≥ ρ > 0`, `V'' ≤ 1 + (spikes of height 1)` and `V'''` rapidly oscillating (e.g. width `δ_k → 0` super-fast,
`V' = x + O(1)`), `V'''v ∉ L²(μ)` is possible, so (W) fails; but this is an obstruction of the cut-off proof, NOT a proof
that `Core2` fails (we know neither proof nor counterexample for general smooth convex `V`; `Core2` ⇔ essential self-adjointness of `L²` on `C_c^∞`,
which is a genuine 4th-order limit-point statement, strictly stronger than essential self-adjointness of `L` which holds for every `V`).

## Targets (names in `MarkovTriple.BGL.Instances.Gibbs`)
* **D0** `GibbsData.PolyHess (G) : Prop` :=
  `(∃ Cw ≥ 0, ∀ x, -(Cw * (1 + |V' x|)) ≤ V'' x)` ∧ `(∀ ε > 0, ∃ B ≥ 0, ∀ x, V'' x ≤ ε * V' x ^ 2 + B)` ∧
  `(∃ C N, ∀ x, |V''' x| ≤ C * (1 + |V' x| ^ N))`.
  `GibbsData.GrowHess.polyHess : G.GrowHess → G.PolyHess`.   (`V'' ≥ ρ` implies the first conjunct with `Cw = |ρ|`.)
* **D1** `GibbsData.memLp_of_BE_w`, `GibbsData.memLp_of_hardy_w` (weighted steps, statements above, `ψ` smooth).
* **D2** `GibbsData.resolvent_pow_L2 (hlow) (hsub) : ∀ n, MemLp (V'^n * v) 2 μ ∧ MemLp (V'^n * deriv v) 2 μ`.
* **D3** `GibbsData.resolvent_weighted_L2_poly (hb : PolyHess)`: the eight weighted jets of `resolvent_weighted_L2`.
* **D4** `GibbsData.cutoff_ZL_p (hb : PolyHess)`: the three graph-norm estimates (as `cutoff_ZL_w`).
* **D5** `GibbsData.gibbsFull_core2_of_polyHess (hb : G.PolyHess) : G.gibbsFull_unconditional.Core2`.
* **D6** `GibbsData.gibbs_mem_domain_of_Γ₂_polyHess (hb : PolyHess) {ρ} (hρ : ∀ x, ρ ≤ V'') ...`: converse of Prop. 3.3.17, no `Core2`
  hypothesis (same conclusion as `gibbs_mem_domain_of_Γ₂_growHess`).
* **D7** witness OUTSIDE `GrowHess` with `ρ > 0`: `expGibbs`, `V = exp(x²)`: `V' = 2x e^{x²}`, `V'' = (2+4x²)e^{x²} ≥ 2` (`ρ = 2`),
  `V''' = (12x+8x³)e^{x²}`.  `expGibbs_polyHess`, `expGibbs_convex : ∀ x, 2 ≤ V'' x`, `expGibbs_not_growHess`, `expGibbs_core2`,
  `expGibbs_mem_domain_of_Γ₂`.

## Not claimed
* `Core2` for `GibbsData` with `V'''` not polynomially dominated by `V'` (e.g. super-oscillating `V'''`), or `V''` not `o(V'²)`
  (e.g. `V'' ≳ V'²/4`-type).  General smooth convex `V`: open (neither proved nor refuted).
* `ℝ^d`, `EllData`, `RiemData`.

## Status
All targets D0-D7 are PROVED (build green; axioms `propext`, `Classical.choice`, `Quot.sound`; audit `BGL/AUDIT_R19_CORE2.md`).
Names as above, with: D1 `memLp_of_BE_w`, `memLp_of_hardy_w` (+ `hardy_ibp_w`); D2 `resolvent_pow_L2` (hypotheses spelled out as the first two conjuncts of
`PolyHess`); D3 `resolvent_weighted_L2_poly`; D4 `cutoff_ZL_p`; D5 `gibbsFull_core2_of_polyHess` (+ `gibbsFull_core2_of_growHess_via_poly`);
D6 `gibbs_mem_domain_of_Γ₂_polyHess` and the variant `gibbs_mem_domain_of_Γ₂_convex` (hypotheses `V'' ≥ ρ`, `V'' = o(V'²)`, `V''' ≤ C(1+|V'|^N)`);
D7 `expGibbs`, `expGibbs_polyHess`, `expGibbs_convex` (`ρ = 2`), `expGibbs_not_growHess`, `expGibbs_core2`, `expGibbs_mem_domain_of_Γ₂`.
No deviation from the statements.  The "Where the route stops" paragraph stays true: the claim there that spiky `V'''` can give `V'''v ∉ L²` is a remark about
the method (not verified in Lean), no statement relies on it.
