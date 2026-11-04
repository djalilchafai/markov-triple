# AUDIT R20 D2 (self, hostile): the converse of BGL Prop. 3.3.17 for `EllData d` / `RiemData d` WITHOUT `Core2` / `CoreCut`

Files: `Instances/GibbsRd/DirectEll{Cut,Core,Main}.lean`, `Instances/Riemannian/DirectRiem{Hess,Transport,Main}.lean`,
`Instances/Riemannian/AxiomCheckR20DirectEll.lean`; statements `Instances/GibbsRd/STATEMENTS_R20_DirectEll.md` (registered `proposed`).

## DIFFERENCE FROM BGL
* BGL (Prop. 3.3.17, p. 161-162): converse via extension of a linear form to `L²` by density of `(L² + Id)𝒜₀`, i.e. `Core2` (silently used, ERRATA R15-1).
  R17-R19 proved `Core2` only under growth hypotheses (for `EllData`/`RiemData`: `Curv ρ` + `CoreCut`).
* Here: the converse is obtained as (i) `L f ∈ L²` by a cut-off (Caccioppoli, BGL Prop. 3.2.1 style) argument applied to `Γ₂`, (ii) the
  EXISTING abstract `FullTriple.mem_domain_of_ESA` (BGL Prop. 3.3.6 (i), uses F10 only).  `Core2` and `CoreCut` are not used.
* Why it works: the converse needs only `Lf ∈ L²`, not density of `(1−L)𝒜₀` for the graph norm of `L`; ESA of `L` identifies the maximal operator
  with the closure.  The cross term `Γ(χ,Γf) = 2Hess f(∇χ,∇f)` is bounded by `|∇χ|` through `Γ₂(f) − ρΓ(f) ≥ ‖Hess f‖²` (Bochner), so only
  completeness (`Γχ ≤ 1`) is needed; `Lχ`, `Γ₂(χ)` are never used.
* Hypotheses that differ: ONLY `Curv ρ` (+ completeness already in the data, `a_exh`/`g_exh`).  `CoreCut` removed.  The R17-R19 `Core2` theorems stand as
  independent, STRONGER facts (they give `Core2`, i.e. e.s.a. of `L²` on `C_c^∞`); this route does NOT give `Core2` and nothing is claimed about `Core2` for `hypRiem`.

## 1. What is proved (all `#print axioms`: `propext`, `Classical.choice`, `Quot.sound`)
* `EllData.exists_gradCut` (from `diff_isComplete`): `χ_n ∈ C_c^∞`, `0 ≤ χ_n ≤ 1`, `Γχ_n ≤ 1`, `χ_n → 1` a.e.
* `EllData.cutoff_identity`: `∫ c²(Lf)² = ∫ c²G2(f) + ∫ cΓ(c,Γf) − 2∫ c Lf Γ(c,f)` (two integrations by parts, Leibniz for `Γ`; checked by hand: with
  `φ = c²`, `∫φLΓf = −2∫cΓ(c,Γf)`, `∫φ(Lf)² = −∫φΓ(Lf,f) − 2∫cLfΓ(c,f)`, `G2 = ½LΓ − Γ(Lf,f)` pointwise).
* `EllData.cutoff_bound`: `∫ c²(Lf)² ≤ 2(∫|G2 f f| + ∫(Γf + G2') + 2∫Γf)` using `|cΓ(c,Γf)| ≤ Γf + G2'` (from `HessCS`, `Γc ≤ 1`, `0≤c≤1`),
  `−2ab ≤ a²/2 + 2b²` and `Γ(c,f)² ≤ Γc Γf ≤ Γf`; absorption of `½∫c²(Lf)²`.
* `EllData.memLp_L_of_hessCS` (Fatou, `integrable_of_cut_ae`), `EllData.ell_mem_domain_of_hessCS`.
* `RiemData.hess_cs`, `RiemData.hessNorm_le_G2'`, `RiemData.riem_hessCS`: `Γ(u,Γf)² ≤ 4Γ(u)Γ(f)(Γ₂(f) − ρΓ(f))` from `riem_bochner`, `riem_ricci_of_curv`, `pderiv_GamF_self`
  and Cauchy–Schwarz for the semidefinite form `Σ g^{ik}g^{jl}A_{ij}B_{kl}` (`hessNorm_nonneg`).
* `EllData.toRiem`, `toRiem_toEll : E.toRiem.toEll = E`, `hessCS_of_curv`: every `EllData` is the `toEll` of a `RiemData` (`g = a`, `W = log(det(a)^{-1/2}/w)`).
* **`EllData.ell_mem_domain_of_Γ₂_direct`** (hypothesis `hρ : E.Curv ρ` only), **`RiemData.riem_mem_domain_of_Γ₂_direct`**; same conclusion shape as
  `ell_mem_domain_of_Γ₂` / `riem_mem_domain_of_Γ₂` with `hC : CoreCut` deleted.

## 2. Faithfulness (hostile)
* Conclusion = book's: `∃ hF : [f] ∈ 𝒟(L), L[f] = [Lf]` a.e.  Hypotheses `f ∈ 𝒜`, `f ∈ L²`, `Γ(f), Γ₂(f) ∈ L¹` as in the book (Γ₂ the formula-defined, signed, one;
  `G2'` integrability follows from `Γ(f) ∈ L¹`).  `Curv ρ` is the book's `CD(ρ,∞)` on smooth functions for the formula `Γ₂` (not the abstract `CD(ρ,n)` of the Full triple; `n = ∞` is the Gibbs/Riemannian case).
* NOT used and NOT needed: `f ∈ L²` (only to form the class `[f]`), `ρ > 0`, any bound on `Lχ`, `Γ₂(χ)`, `∂a`, `∇log w`.
* The ESA input is the F10 field of `E.fullU`, proved from `weakHypo_unconditional`/`f8_unconditional` (`EllData.ellReg`, R16-R19; unchanged).
* A possible objection: `EllData.HessCS ρ` is an extra hypothesis of the abstract estimate.  It is NOT an extra hypothesis of the theorems: `hessCS_of_curv` derives it from `Curv ρ`.
  The only data-level input of `hessCS_of_curv` is the Riemannian reading of `(a, w)`; the identification `E.toRiem.toEll = E` is a theorem (structure extensionality `ext'`).
* The abstract Theory (`Theory/Extension/Converse.lean`) is unchanged: the abstract converse for a general Full triple is still conditional on `Core2`
  (`FullTriple.mem_domain_of_Γ₂`); what is new is that for `EllData`/`RiemData` the hypothesis is replaced by the Hessian bound, i.e. `Core2` was not necessary there.

## 3. Non-vacuity (hypotheses not contradictory)
* `hypRiem` (hyperbolic plane, `Curv 1`, `ρ = 1 > 0`, co-metric unbounded, NO `CoreCut` by the by-hand argument of `AUDIT_R19_CORE2ELL.md` §6, hence outside the whole R19 class):
  `hypRiem_mem_domain_of_Γ₂_direct`, `hypRiem_hessCS`, and `hypRiem_mem_domain_of_A₀_direct` (all hypotheses discharged for every `f ∈ C_c^∞(ℝ²)`).  This is the key new instance.
* `confRiem` (`Curv 2`): `confRiem_mem_domain_of_Γ₂_direct`, `confRiem_hessCS`.
* general `ell_mem_domain_of_A₀_direct`: every test function satisfies `hf, hf2, hG, hG2`, so the statement is satisfiable for every `E` with `Curv ρ`.
* No `sorry`, no new axiom, no `set_option`; `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` is used throughout via the library `Sm` (never analytic `⊤`).

## 4. Limits (exact)
* Only the single-chart `EllData d`, `RiemData d`.  The 1-D / `ℝ^d` Gibbs data have their own routes (not touched; `Instances/Gibbs*` owned by another stream); they are
  `EllData`'s via `GibbsRdData.toEll`, hence the theorem applies to `G.toEll` under `Curv ρ` (`gibbsRd_curv`).  Not stated separately here.
* `Core2` for `hypRiem` and for general smooth `V` remains open (R19-M1).  The R15-1 erratum ("unconditional converse OPEN") is now closed for `EllData`/`RiemData`
  under `Curv ρ`; it stays open for an arbitrary abstract Full triple.
* The claim that `hypRiem` has no `CoreCut` is the R19 by-hand argument, not formalised here (we do not need it for the theorem).
