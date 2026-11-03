# AUDIT R16 ELLIPTIC (self-attack, Armstrong step b)

Scope: `GibbsRd/EllipticDefs.lean`, `EllipticDiffQuot.lean`, `EllipticCaccioppoli.lean`, statements in
`GibbsRd/STATEMENTS_R16_Elliptic.md`.  Candid summary: the assigned target `interior_regularity_step` is NOT proved.  What is proved
is the d-independent calculus of weak derivatives, the difference-quotient machinery in the direction "bounded quotients ⇒ weak
derivative" (global `L²`), and the Caccioppoli identity/inequality for SMOOTH solutions.

## 1. Vacuity of the shared definition (found, fixed: erratum R16-E1)
`WeakDeriv` as specified uses `ContDiff ℝ ⊤ φ`.  In this Mathlib `⊤ : WithTop ℕ∞` is `ω` (analytic).  Compactly supported analytic
functions on `ℝ^d` (d ≥ 1) vanish, so the test clause would be vacuous: any two locally integrable `f, g` would satisfy it.  We use
`ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ` (= `Sm φ`, Mathlib `∞`).  The Sobolev-embedding agent and the glue agent must do the same;
otherwise the glue's identification of the two `WeakDeriv`s is of a vacuous predicate.  Non-vacuity of the corrected predicate:
`weakDeriv_of_smooth`, and `WeakDeriv.unique` (distinct `g` are not both weak derivatives).

## 2. Local vs global L²
`LocL2 f := ∀ K compact, MemLp f 2 (volume.restrict K)`; `LocL2 ⇒ LocallyIntegrable` (B1).  `Sobolev (k+1) f` demands `f ∈ LocL2` and
each `∂ᵢ f` weak, in `Sobolev k`: iterated weak partials up to order `k+1` (in all index orders; symmetry of mixed weak partials is not
needed and not proved).  Q2 (`weakDeriv_of_bounded_dq`) is a GLOBAL statement (`f ∈ L²(ℝ^d)`, quotients bounded in `L²(ℝ^d)`).
Its use for `H¹_loc` needs a cut-off argument (apply to `ζ f`, `ζ ∈ C_c^∞`, with `D_h(ζ f) = ζ(·+h) D_h f + f D_hζ`) plus gluing of the
local weak derivatives `g_R` (uniqueness on balls via `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`): NOT done.
Relation to the chain of `EllReg`: `MemLp (x k) 2 E.μ` implies `LocL2 (x k)` because `dens = w/Z` is continuous positive hence
bounded below on compacts — this implication is not proved here (glue's job).

## 3. The weak equation and `resolvent_weak`
`resolvent_weak`/`EllReg` state `∫ x_k · L a dμ = ∫ (x_k − x_{k+1}) a dμ`, `μ = Z⁻¹ w dx` (`integral_μ`: `∫ F dμ = ∫ dens·F dx`).  Dividing out
`Z⁻¹`, this is `∫ u (La) w dx = ∫ h a w dx` with `u = x_k`, `h = x_k − x_{k+1}`.  This is the VERY weak (distributional) equation for
`u ∈ L²_loc`.  Evans' Thm 1 assumes `u ∈ H¹`; passing from `L²_loc` to `H¹_loc` is an additional theorem (Friedrichs commutator, or
parametrix) not in Evans §6.3.  Two ways out for the glue: (a) prove it; (b) strengthen `EllReg`'s chain hypothesis with the
form-domain information `x_k ∈ D(𝓔)` that the resolvent chains in `weakHypo_of_reg` (for `WeakHypo` the `f ∈ D(L̄)`) and `f8_of_reg`
(`R^j Φ ∈ D(L̄)`) actually possess — but then one needs the weak gradient of a form-domain element (closure of `Γ` on `A₀`).
The statement `STATEMENTS_R16_Elliptic.md` E4 records that the assignment's `L²_loc`-only target contains this extra step.

## 4. Ellipticity only on compacts, weight `w`
`EllData` gives `a` smooth, symmetric, positive definite, bounded above; `w` smooth positive.  Local uniform ellipticity
`λ_K |ξ|² ≤ Σ aᵢⱼ ξᵢξⱼ` on a compact `K` follows from continuity+compactness of `K × S^{d-1}` (NOT proved here).  The proved Caccioppoli
inequality is stated with the intrinsic `Γ` (no Euclidean gradient, no lower ellipticity constant), using only positive semidefiniteness
(`quad_nonneg`).  Passing to `|∇u|²` needs `λ_K`.  The weight `w` stays inside every integral (it is the natural divergence-form
weight); `w` is smooth and positive, so locally bounded above and below (no use made of integrability of `w`).

## 5. d = 0 and d = 1
`d = 0`: `Fin 0` has no direction, `WeakDeriv` is never quantified, `Sobolev (k+1) f ⇔ LocL2 f`; every statement is trivially consistent.
`d = 1`: Q1/Q2 specialise to the classical 1-D facts; consistent with `Gibbs/Reg*.lean` (not cross-checked formally).

## 6. Statement-level checks of what IS proved
* `dq_ibp`: sign/convention verified by Lean (`dq i (−h)` on the test function); `h = 0` is allowed (`x/0 = 0` in Lean, both sides `0`).
* `weakDeriv_of_bounded_dq`: hypotheses `0 ≤ C`, `hₙ ≠ 0`, `hₙ → 0`, `‖dq hₙ f‖₂ ≤ C` along the sequence; conclusion `∃ g ∈ L²`,
  `WeakDeriv f g i`.  Non-vacuous (smooth `f ∈ L²` with `∂ᵢ f ∈ L²` satisfies the hypotheses; converse Q3 is NOT proved, so the
  equivalence "weak derivative in `L²` ⇔ bounded quotients" is only half formalised).  The bound `‖g‖₂ ≤ C` stated in the plan is not in
  the Lean statement (omitted; follows from weak lower semicontinuity, not proved).
* `Sobolev.smooth_mul`: Leibniz at every order (induction); `Sobolev.congr_ae`/`WeakDeriv.congr_ae` allow a.e. changes of representative.
* Caccioppoli: `u` smooth (not compactly supported), `ζ ∈ C_c^∞`; all integrands continuous compactly supported (so Bochner integrals are
  honest).  `caccioppoli_identity` is an identity (no ellipticity); the inequality is `Γ_young` + the identity.

## 7. What remains (exact statements; in this order of dependency)
Notation `W(E,u,h) := ∀ a ∈ A₀ d, ∫ u · E.L a · E.w = ∫ h · a · E.w`.
* R1 (Q3, Evans §5.8.2 Thm 3(i)): `WeakDeriv f g i → MemLp f 2 → MemLp g 2 → eLpNorm (dq i h f) 2 ≤ eLpNorm g 2`  (route: `|∫ dq f φ| ≤ ‖g‖‖φ‖` by
  `F(s) = ∫ f(z) φ(z − s h eᵢ) dz`, `F' = h ∫ g φ(· − s h e)`, mean value, then density `Lp.dense_hasCompactSupport_contDiff`).
* R2 (localisation): `Sobolev`-type local version of Q2: `LocL2 f`, ∀ compact `K` ∃ `C_K`, `eLpNorm (dq i hₙ f) 2 (vol.restrict K) ≤ C_K` ⇒ `∃ g, LocL2 g ∧ WeakDeriv f g i`.
* R3 (mollifier density): `v ∈ L²` compact support, `WeakDeriv v gⱼ j`, `gⱼ ∈ L²` ⇒ ∃ `vₙ ∈ C_c^∞`, supports in a fixed compact, `vₙ → v`, `∂ⱼ vₙ → gⱼ` in `L²`
  (needs `ρ_ε * v → v` in `L²`, absent from Mathlib: only the continuous case `ContDiffBump.convolution_tendsto_right_of_continuous`).
* R4 (extension of the weak form): `Sobolev 1 u`, `W(E,u,h)` ⇒ `∫ w Γ(u,v) = −∫ w h v` for compactly supported `v ∈ H¹` (from R3).
* R5 (E1, weak Caccioppoli): from R4 with `v = ζ² u`; as the smooth `EllData.caccioppoli`.
* R6 (E2, Evans Thm 1 Steps 2–3): test `v = −D_{−h}(ζ² D_h u)` (R4), `D_h` product rule, Young, R1 for `D_h u` ⇒ `‖D_h ∇u‖_{L²(K)}` bounded ⇒ R2 ⇒ `u ∈ H²_loc`, and the
  equation holds a.e.
* R7 (E3, Evans Thm 2): differentiate the equation weakly (`a, w` smooth: `u' = ∂_k u` solves `L u' = h' + (lower order)` with `H^{k-?}_loc` right-hand side) ⇒ induction `k → k+1`; needs R6 for the
  perturbed operator (first-order terms in the right-hand side).
* R8 (E4): `LocL2 u` only: Friedrichs step `L²_loc ⇒ H¹_loc` (commutator `[w a_{ij} ∂_j, ρ_ε*]` bounded on `L²`).
* R9 (glue): `MemLp 2 E.μ ⇒ LocL2`, local ellipticity constant, and Sobolev embedding (other agent) to feed `EllReg`.

## 8. Attack surface (for the independent hostile auditor)
1. A1: Is the correction of `ContDiff ℝ ⊤` really needed (check `#check` / `pp.all`: `@Top.top (WithTop ENat)`)?  Does the Sobolev agent's file use the vacuous one?
2. A2: `Sobolev` requires derivative in every direction `i` separately, in `Sobolev k`; does it agree with Evans' `W^{k,2}_loc` (all multi-indices up to `k`)?  (Yes via iteration, mixed-partial order not important; unproved formally.)
3. A3: `LocL2` via `volume.restrict K` for every compact `K`; vs `L²(B_R)`.
4. A4: `weakDeriv_of_bounded_dq`: `Fact` instances introduced locally; separability of `Lp ℝ 2 volume` found by instance resolution; the `h n = 0` junk value convention for `dq` (never used since `hₙ ≠ 0`).
5. A5: `caccioppoli`: only smooth `u`; no claim for weak solutions; constants `−2`, `4` correct (Lean-checked); relation to the Euclidean norm of `∇u` is not formalised.
6. A6: The title `interior_regularity_step` is NOT delivered (no Lean declaration of that name).
7. A7: `MarkovTriple.lean` got four import lines (new modules only); no frozen file changed.
8. A8: `ERRATA.md` section "Round 16 (elliptic half)" is appended; the other agent's appended section will need a trivial merge.
