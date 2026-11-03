# Round 18, Stream A2 (Gibbs `Core2` without bounded `V'`): statements fixed BEFORE the proofs.

Change only by a logged deviation in the `Status` section below and an erratum in `ERRATA.md` (prefix `R18-`).
Setting: `G : GibbsData` (1-D, `μ = Z⁻¹ e^{-V}dx`, `𝒜₀ = C_c^∞`, `L f = f'' - V' f'`), `G.gibbsFull_unconditional : FullTriple ℝ`.
Predecessor: `STATEMENTS_R17_Core2.md` (`Core2` under `BddJet`: `V', V'', V'''` bounded).

## Known obstacle (ERRATA R17-M1)
`BddJet` (`V'` bounded) contradicts `V'' ≥ ρ > 0` (`V' ≥ ρ x + V'(0)` on `x ≥ 0`), so the R17 converse covers only `ρ ≤ 0`.

## Mathematical plan (BGL Sect. 3.2-3.3: Prop. 3.2.1 (cut-off/Caccioppoli proof of ESA), Def. 3.3.9, Bochner `Γ₂ ≥ ρΓ`, Prop. 3.3.17)
`Core2 ⇐ ` for `a ∈ 𝒜₀` and `v = (1-L)⁻¹[a]` (smooth, `v, Lv = v - a ∈ L²`; R17 `exists_resolvent_smooth`), the cut-offs `χ_n v`
converge to `v` in the graph norm of `L²`.  The commutators `L(χv) - χ Lv`, `L²(χv) - χ L²v` (R17 `LL_mul_expand`) are sums of
`(χ_n^{(j)}, j = 1..4) × (explicit weighted jets of v)`; by dominated convergence it suffices that the following are in `L²(μ)`:

    v, V'v, (V'V'' - V''')v, (V'² - 2V'')v, v', V''v', V'v', v'', V'v'', v''', V' Lv.        (W)

No commutator coefficient is bounded: the weights `V'`, `V'²` are controlled by two integral (Caccioppoli/Bakry-Emery) estimates, both
proved with the cut-off `χ_n` and the exact integration by parts `∫ (P' - V'P) dμ = 0`, `P = χ² V' f²`:

* **(BE)** (uses only `V'' ≥ ρ`, i.e. `CD(ρ,∞)`; this is the 1-D Bochner identity `Γ₂(f) = f''² + V''f'² ≥ ρ f'²`):
  `f ∈ L²(μ)` smooth and `f' - V' f ∈ L²(μ)`  ⇒  `V' f ∈ L²(μ)` (hence `f' ∈ L²`).  
  Applied to `f = v'` (`f' - V'f = Lv`) it gives `V'v', v'' ∈ L²`; to `f = v''` (`f' - V'f = v' - a' + V''v'`) it gives `V'v'', v''' ∈ L²`.
* **(Hardy)** (uses `V'' ≤ B`):  `f, f' ∈ L²(μ)` smooth ⇒ `V' f ∈ L²(μ)`.  Applied to `f = v` and `f = V'v` it gives `V'v`, `V'²v`.

All of (W) follow when `V''` and `V'''` are bounded (`|V''|, |V'''| ≤ B`); `V'` is NOT assumed bounded.  `V'' ≥ ρ` is then automatic
with `ρ = -B`, and `ρ > 0` is allowed (e.g. `V = x²/2 + ½ cos x`, `V'' = 1 - ½cos x ≥ ½`).
Where the plan stops: for `V` with `V''` unbounded above (e.g. `x⁴`, `V''' = 24x`) the weights `V''v`, `V'''v` are not controlled by
(BE)/(Hardy) without a growth hypothesis relating `V''` and `V'²` (`V'' ≤ ε V'² + C_ε` for every `ε`, `|V'''| ≤ ε|V'|³ + C_ε`) and further
cascades (`V'³ v`, `V'²v'`); not claimed unless proved below (see Status).  We do not know whether `Core2` fails for some `V`
with `V'' ≥ ρ`; essential self-adjointness of `L²` on `C_c^∞` is a genuine extra property for wild `V`, and no counterexample is claimed.

## Targets (names in `MarkovTriple.BGL.Instances.Gibbs`)
* **B0** `GibbsData.BddHess (G) : Prop := (∃ B, ∀ x, |V'' x| ≤ B) ∧ (∃ B, ∀ x, |V''' x| ≤ B)` (`V'' = deriv (deriv V)`, `V''' = deriv (deriv (deriv V))`).
  `BddJet → BddHess` (`GibbsData.BddJet.bddHess`).
* **B1** `GibbsData.memLp_of_BE`: `Sm f`, `MemLp f 2 μ`, `MemLp (fun x => deriv f x - deriv V x * f x) 2 μ`, `∀ x, ρ ≤ V'' x`
  ⇒ `MemLp (fun x => deriv V x * f x) 2 μ`.
* **B2** `GibbsData.memLp_of_Hardy`: `Sm f`, `MemLp f 2 μ`, `MemLp (deriv f) 2 μ`, `∀ x, V'' x ≤ B` ⇒ `MemLp (fun x => deriv V x * f x) 2 μ`.
* **B3** `GibbsData.resolvent_weighted_L2 (hb : BddHess)`: for `v` as in R17 A1 (`Sm v`, `MemLp v 2 μ`, `L v = v - a`, `a ∈ 𝒜₀`) all
  functions of (W) are in `L²(μ)`.
* **B4** `GibbsData.cutoff_ZL_w (hb : BddHess)`: the three graph-norm cut-off estimates (`χ_n v → v`, `L(χ_n v) → L v`, `L²(χ_n v) → L² v`).
* **B5** `GibbsData.gibbsFull_core2_of_bddHess (hb : G.BddHess) : G.gibbsFull_unconditional.Core2`  (**no `BddJet`; `V'` arbitrary**).
* **B6** `GibbsData.gibbs_mem_domain_of_Γ₂_bddHess` (**unconditional converse of Prop. 3.3.17** for `BddHess` Gibbs triples):
  `hb : BddHess`, `∀ x, ρ ≤ V''`, `f ∈ 𝒜`, `f ∈ L²(μ)`, `Γ(f), Γ₂(f) ∈ L¹(μ)` ⇒ `[f] ∈ 𝒟(L)` and `L[f] = [L f]` a.e.
* **B7** non-vacuity with `ρ > 0` and unbounded `V'`: `cosGibbs` (`V(x) = x²/2 + ½ cos x`) is a `GibbsData`, `cosGibbs_bddHess`,
  `∀ x, ½ ≤ cosGibbs.V'' x`, `¬ cosGibbs.BddJet` (so R17 did not apply), `cosGibbs_core2`, and a nontrivial instance of B6.

## Not claimed
* `Core2` for `GibbsData` with `V''` or `V'''` unbounded (e.g. `x⁴`), for `EllData`/`GibbsRdData` on `ℝ^d`.
* Any statement for `V''` unbounded below is vacuous here only in the sense that `BddHess` excludes it; `ρ` is arbitrary real.

## Status
All targets B0-B7 are PROVED (build green, axioms `propext`, `Classical.choice`, `Quot.sound`; audit `BGL/AUDIT_R18_CORE2.md`).
Deviations (all GENERALISATIONS, no statement was weakened; the statements above are kept and remain true as stated):
* **R18-D1** (B0/B3/B4/B5/B6 generalised).  After the bounded case was proved the weights were seen to need only a *growth* bound, so
  the proofs were done for `GibbsData.GrowHess := ∃ C, ∀ x, |V''| ≤ C(1+|V'|) ∧ |V'''| ≤ C(1+|V'|)`.  `BddHess → GrowHess`
  (`BddHess.growHess`), hence B3-B6 as stated for `BddHess` are corollaries (`gibbsFull_core2_of_bddHess`,
  `gibbs_mem_domain_of_Γ₂_bddHess` are kept with the statements above); the growth versions are `resolvent_weighted_L2`,
  `cutoff_ZL_w`, `gibbsFull_core2_of_growHess`, `gibbs_mem_domain_of_Γ₂_growHess`.
* **R18-D2** (B1/B2 signatures).  The hypotheses of the two estimates were made quantitative instead of the plain constants of the
  plan: (BE) `-(Cw (1+|V'|)) ≤ V''` (`Cw ≥ 0`; `V'' ≥ ρ` implies it with `Cw = |ρ|`), (Hardy) `V'' ≤ V'²/4 + B` (`B ≥ 0`;
  implied by `V'' ≤ B'`).  `memLp_of_BE`, `memLp_of_hardy` in `Core2Weighted.lean`.
* **R18-D3** (B7 extended).  Besides `cosGibbs` (`x²/2 + ½cos x`, `BddHess`, `ρ = ½`, `¬ BddJet`) a quartic example `quarGibbs`
  (`x⁴/4 + x²/2`, `ρ = 1`, `GrowHess`, `¬ BddHess`) is added: `quarGibbs_core2`, `quarGibbs_mem_domain_of_Γ₂`.
Still NOT claimed: `V''` or `V'''` of growth faster than `C(1+|V'|)` (e.g. `e^{x²}`-type: `V''/V' ~ 2x`; `V'' ≈ V'²`-type), `ℝ^d`.
