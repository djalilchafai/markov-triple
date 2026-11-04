# AUDIT R19 (Stream A6): `Core2` and the converse of BGL Prop. 3.3.17 for `EllData d` and `RiemData d` (hostile self-audit)

Statements: `Instances/GibbsRd/STATEMENTS_R19_Core2Ell.md` (registered `proposed` in `frozen-manifest.json` before the proofs).
The BGL PDF was not consulted for page numbers (none is needed by any proof); numbering (Prop. 3.2.1 p. 142, Def. 3.3.9,
Prop. 3.3.17 pp. 161-162, Def. 3.3.12 `Γ₂`, Def. 3.3.14 `CD(ρ,∞)`) is quoted from the repository's notes.

## 1. What is proved (namespace `MarkovTriple.BGL.Instances.GibbsRd`, Riemannian corollaries in `...Riemannian`)
| item | name | file |
|---|---|---|
| calculus: Cauchy–Schwarz for `Γ`; linearity of `L, Γ, Γ₂`; locality; **CS for `Γ₂ - ρΓ`** (`G2'_cs`); Leibniz expansions `L_cut`, `LL_cut` | `Γ_cs`, `L_lin`, `G2_quad`, `G2'_cs`, `loc_one` | `Core2EllCalc` |
| **hypothesis class `H`** | `EllData.CutFamily`, `EllData.CoreCut` (C0/C1) | `Core2EllCalc` |
| smooth resolvent solution (any `EllData`) | `EllData.exists_resolvent_smooth_ell` | `Core2EllResolvent` |
| Caccioppoli, cut-off Bochner | `cacc_ell`, `integrable_Γ_resolvent`, `integrable_G2'_resolvent` | `Core2EllEnergy` |
| the three graph-norm estimates | `ZL.of_dom`, `zl_Γ`, `zl_G2`, `cutoff_ZL_ell` | `Core2EllZL` |
| **T1 `Core2`**, **T2 converse of Prop 3.3.17** | `EllData.ell_core2`, `EllData.ell_mem_domain_of_Γ₂` | `Core2EllMain` |
| **T3** Riemannian charts | `RiemData.riem_core2`, `RiemData.riem_mem_domain_of_Γ₂` | `Riemannian/Core2RiemMain` |
| **T4** Gibbs recovered | `BddHess3.coreCut`, `gibbsRd_core2_via_ell` | `Core2EllGibbs` |
| T4' flat Riemannian | `ofGibbs_core2`, `ofGibbs_curv`, `ofGibbs_coreCut` | `Riemannian/Core2RiemMain` |
| **T5** non-vacuity, Gibbs `ρ>0` | `gaussData_ell_core2` (`ρ=1`), `cosData_ell_core2` (`ρ=1/2`) | `Core2EllGibbs` |
| **T6** radial exhaustion criterion | `RadialJets`, `EllData.RadialExh`, `radial_identities`, `radial_scalar`, `coreCut_of_radial` | `Core2EllRadial*` |
| **T5** non-vacuity, **non-flat variable metric**, `ρ = 2 > 0` | `confRiem_coreCut`, `confRiem_core2`, `confRiem_mem_domain_of_Γ₂` | `Riemannian/Core2RiemConf` |
`#print axioms` (`Riemannian/AxiomCheckR19Core2Ell.lean`): only `propext`, `Classical.choice`, `Quot.sound`.  No `sorry`, no `set_option`,
no new axiom; all new files compile with 0 warnings; full `lake build` OK; `scripts/check_frozen.py` OK.

## 2. Exact hypotheses of the final theorems
`E : EllData d` arbitrary (smooth symmetric positive definite `a`, smooth positive integrable `w`, completeness field `a_exh`), and
* `hρ : E.Curv ρ` for some `ρ ∈ ℝ` (the lower bound `Γ₂ ≥ ρΓ` on `C^∞`, Def. 3.3.14; any sign);
* `hC : E.CoreCut`, i.e. a family `χ_n ∈ C_c^∞`, `0 ≤ χ_n ≤ 1`, eventually `≡ 1` near every point, with `Γ(χ_n), Lχ_n, L²χ_n, Γ(Lχ_n), Γ₂(χ_n)`
  uniformly bounded (`Γ₂(χ_n) ≤ K` suffices: only the upper bound is used).
Nothing else (no bound on `a, ∂a, ∂²a, ∂³a, ∇log w` is assumed *separately*: they enter only through `CoreCut`, which is stated in the
`L, Γ, Γ₂` calculus; the coordinate commutators of the book are `[L,χ] = LΓ`-expressions and are never expanded).
For `RiemData R`: `R.Curv ρ` and `R.toEll.CoreCut`.

## 3. Faithfulness
* `Core2` is the repository's `FullTriple.Core2` for `E.fullU = E.full (weakHypo_unconditional) (f8_unconditional)` — the Full triple whose
  `WeakHypo` and `F8` are *theorems* (`EllData.ellReg`).  The converse is `FullTriple.mem_domain_of_Γ₂` with `full_CD`; hypotheses on `f` are the book's.
* `G2 f g := ½(LΓ(f,g) - Γ(Lf,g) - Γ(f,Lg))` agrees with the frozen `diff.Γ₂` on `C^∞` (`curv_G2` derives `ρΓ ≤ G2` from `Curv ρ` through `Γ₂_eq_comb`;
  `curv_of_G2` is the converse).  `Curv ρ` is exactly the repository's `EllData.Curv`.
* Route = BGL's: smooth resolvent solution (R16 `EllReg`), Caccioppoli cut-off (Prop. 3.2.1), cut-off Bochner = `Γ₂ ≥ ρΓ` (Prop. 3.3.17's use of CD),
  graph-norm cut-offs (the `L²`-core argument).  New feature vs R18: **no Hessian of `v`** is needed; `Γ₂(v) - ρΓ(v) ∈ L¹` replaces `∇²v ∈ L²`, and the
  cross term `Γ₂(χ,v)` is controlled by Cauchy–Schwarz for the nonnegative form `Γ₂ - ρΓ`.  This is why no `∂a` appears.

## 4. Are the hypotheses contradictory?  No (witnesses with `ρ > 0`)
* `gaussData d`, `cosData d` (`V = |x|²/2 + cos(x₀)/2`, `ρ = 1/2`): `BddHess3.coreCut` + `gibbsRd_curv`; `gaussData_ell_core2`, `cosData_ell_core2`.
* **`confRiem`** (non-flat, non-constant co-metric `e^{-|x|²}δ`, weight `2e^{|x|²}`, `Curv 2`, `Ric = -2δ`): `L f = e^{-|x|²}Δf - 4x·∇f` (`confRiem.L_formula`),
  `ψ = |x|²/2`, `α(s) = 2e^{-2s} - 8s`, `β(s) = 2se^{-2s}`, growth constants `C = 16` (`conf_radialJets`); hence `confRiem_core2` and
  `confRiem_mem_domain_of_Γ₂` with `ρ = 2`.  This exercises variable `a` and a variable weight.
* `ofGibbs G` (co-metric `δ`): `ofGibbs_core2`.
* The hypothesis on `f` of the converse is satisfiable (e.g. `f ∈ 𝒜₀`).
Note the class has `ρ`-independence: `Curv ρ` with `ρ` negative is allowed; only the existence of some `ρ` is used (by `BddHess3.hessGe` it is automatic in the Gibbs case).

## 5. Gibbs recovered / compared
`BddHess3 ⇒ CoreCut` (R18 `cut_bounds`; `Γχ = |∇χ|²`, `Γ₂χ = ‖Hess χ‖² + Hess V(∇χ,∇χ)` bounded by `Hess V`, `∇χ`, `Hess χ` bounds).  So
`ell_core2` implies R18's `gibbsRd_core2` (`gibbsRd_core2_via_ell`, same statement through `G.toEll.fullU`, defeq to `gibbsRdFull_unconditional`).
Converse comparison: `CoreCut` is **strictly weaker than `BddHess3`** for non-Gibbs data (confRiem has unbounded weight gradients `∇W = 4e^{|x|²}x`), but for
**radial Gibbs data it forces `V'` to grow at most like `r` up to logs**: for radial `L` with density `m(r)` and `|Lχ| ≤ K`, `(mχ')' = m Lχ`
gives `|χ'(r)| ≤ K·μ(r,∞)/m(r)` (Mills ratio), so cut-offs of total drop `1` need `∫^∞ μ(r,∞)/m(r) dr = ∞`.  For `V = r⁴/4` this integral is `∫ r^{-3} < ∞`:
**`CoreCut` fails for the quartic potential**, although R18-A2 proves `Core2` for the 1-D quartic by the different (BE/Hardy) weighted route.
So this R19 class does not subsume R18 A2; it is the class of the *cut-off in the `L²` graph norm with uniformly bounded commutator coefficients*.

## 6. `hypRiem` (hyperbolic plane, `W = V = 2cosh d`): decision
**`hypRiem` is NOT in class `H`: `hypRiem.toEll` admits no `CutFamily` (indeed no sequence of `C_c^∞` functions `χ_n → 1` locally uniformly with `|Lχ_n| ≤ K`).**
Math argument (NOT formalised in Lean; a by-hand proof): `L` commutes with the rotations about the origin (they are isometries fixing `u = cosh d`), so the
rotation average `χ̄_n` of `χ_n` is radial, `C_c`, `0 ≤ χ̄_n ≤ 1`, `|Lχ̄_n| ≤ K`, and `χ̄_n(r) = 1` for fixed `r` and `n ≥ N(r)` (eventual unit near each point of
the compact circle, uniformly by compactness).  In geodesic polar coordinates `L = ∂_r² + (coth r - V'(r))∂_r`, `m(r) = sinh r·e^{-2cosh r}`, `(mχ̄')' = m Lχ̄`, hence
`m(r)χ̄'(r) = -∫_r^∞ m Lχ̄`, so `|χ̄'(r)| ≤ K ∫_r^∞ m/m(r) = K/(2 sinh r)`.  Then `1 = χ̄_n(r₀) ≤ ∫_{r₀}^∞ |χ̄_n'| ≤ (K/2) log coth(r₀/2) → 0` as `r₀ → ∞`: contradiction.
Specifically the exhaustion `ψ = log(1+V)` of `HypExample` has `Lψ = (2V - V² + 4)/(1+V) - (V²-4)/(1+V)² ~ -V = -e^{ψ}`, violating `|Lψ| ≤ C(1+ψ)`
(`RadialJets` growth).  (`Curv 1` holds, `ρ = 1 > 0`, so only the cut-off hypothesis fails; the unbounded co-metric `diag(e^{2t},1)` is *not* the obstruction —
`confRiem`'s co-metric decays; the obstruction is the weight `W = 2cosh d` whose gradient grows exponentially in the distance while `μ`'s tail
`∼ e^{-e^r}` is super-exponentially small.)  Neither `Core2` nor its negation is claimed for `hypRiem`.  **Maximal true statement proved**: T1/T2 under `Curv ρ` + `CoreCut`.
A hyperbolic plane with a *quadratic-in-distance* weight (e.g. `W = A·(log cosh-type)²`) would plausibly satisfy `RadialJets` (`|Lψ| ≲ 1+ψ`), but a
formal verification (Hessian of `W`, `Curv ρ > 0`, integrability) was not done.

## 7. Hostile checks and limits
1. `ContDiff` is in the `(⊤ : ℕ∞)` sense everywhere (`Sm`, `S1`); no analytic functions.
2. `d = 0`: `Γ = L = G2 = 0` (`BddHess3.coreCut`, empty case handled explicitly).
3. Where each hypothesis is used: `Curv ρ` only in `integrable_G2'_resolvent` (cut-off Bochner) and `G2'_cs` (CS for `Γ₂'`); `CutFamily.bound`: `Γχ ≤ K` in Caccioppoli and `Γ(χ,v)`-terms;
   `|Lχ| ≤ K` in `|L(χ²)| ≤ 4K` and `vLχ`, `LF·Lv`; `|LLχ| ≤ K` for `v·LLχ`; `Γ(Lχ) ≤ K` for `Γ(Lχ,v)`; `Γ₂(χ) ≤ K` for `Γ₂(χ,v)`.
4. `CutFamily.eventually_one` is stated pointwise-eventually in `n` with a neighbourhood; this is exactly what the locality lemma `loc_one` needs
   (derivatives of order ≤ 4 of `χ_n` vanish at `x` once `χ_n ≡ 1` near `x`).
5. T6 (`RadialJets`) is a *sufficient* condition, scale-invariant: with `x₁ = α/R,…` all five cut-off quantities become polynomials in `σ^{(k)}`, `x_i` with no `R`
   (`radial_scalar`; the identity for `Γ₂(φ∘ψ) = φ'²(½αβ' + ½ββ'' - βα') + ββ'φ'φ'' + β²φ''²` is machine-checked by `ring` in `radial_scalar`).
   It does not use `Γψ ≤ 1`; `a_exh` of the data is unrelated and remains part of `EllData`.
6. Not proved: `CoreCut` for a general `EllData` from coordinate bounds on `a, w` (only the Gibbs flat case and radial functions of `ψ` are derived); no
   claim that `CoreCut` is necessary for `Core2` (it is not: the 1-D quartic has `Core2` without `CoreCut`).
7. `Core2` for arbitrary smooth data (≡ essential self-adjointness of `L²` on `C_c^∞`) remains neither proved nor refuted.
