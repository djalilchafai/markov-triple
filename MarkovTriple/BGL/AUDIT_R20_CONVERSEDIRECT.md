# AUDIT R20 D3: direct converse of BGL Prop. 3.3.17 without `Core2` (hostile self-audit)

Files: `Theory/Extension/ConverseDirect.lean`, `ConverseDirectInst.lean`, `ConverseDirectAxioms.lean`; statements in
`Theory/Extension/STATEMENTS_R20_ConverseDirect.md`.

## DIFFERENCE FROM BGL
* BGL (Prop. 3.3.17, p. 161-162): bounds `|∫ f L h| ≤ C‖h‖` on `(L²+Id)𝒜₀` and EXTENDS to `L²` by the core-for-`L²` step
  (tacit, ERRATA R15-1 = `Core2`) plus ergodicity.  
* Here: no `Core2`, no ergodicity.  The cut-off technique of BGL Prop. 3.2.1 (p. 142) is applied to `Γ₂`:
  `∫χ²(Lf)² = ∫χ²Γ₂(f) + ∫χΓ(Γf,χ) − 2∫χ Lf Γ(f,χ)` (F7 + F1 only, `cutoff_Γ₂_identity`); cross term by the Hessian
  Cauchy–Schwarz `Γ(χ,Γf)² ≤ 4(Γ₂f−ρΓf)Γ(χ)Γ(f)` (`hessCS`, derived from BGL (3.3.7) = `hessian_general_ineq`, because
  `Γ(χ,Γf) = 2H(f)(χ,f)`); last term by Young + `Γ(f,χ)² ≤ Γ(f)Γ(χ)`; Fatou ⇒ `Lf ∈ L²` (`memLp_L_of_Γ₂`); then ESA via
  the maximal-domain lemma (`mem_domain_of_maximal`).
* Hypotheses: BGL = ESA, CD(ρ,∞), ergodicity (+ tacit Core2).  Here = ESA (field F10), `IsComplete` (Def. 3.3.9), `CD(ρ,n)`
  on all of `𝒜`.  Core2 is NOT needed; `HessCS` is NOT an assumption.

## Claims checked
1. **Identity**: derived by hand (Γ₂ = ½LΓ − Γ(f,Lf); F7 for `p = Γf` against `χ²`, for `f` against `χ²Lf`; product rules
   `G_mul_right`); all integrands are in `𝒜₀` (ideal property F1 with `χ ∈ 𝒜₀`), hence integrable with NO assumption on `f`.
2. **Bound**: uses `0 ≤ ζ_k ≤ 1` (the ≤ 1 is derived from monotonicity + a.e. limit 1, not assumed) and `Γζ_k ≤ (k+1)⁻² ≤ 1`
   transferred from `Γ` to `ΓA` by `DiffusionTriple.ΓA_ae_eq`.  Constant independent of `k`; Fatou gives `Lf ∈ L²`.
   `Γ₂(f) ≥ ρΓ(f)` (CD) is used for `K ≥ 0`, which is what makes `Γ₂(f) ∈ L¹` suffice (no `Γ₂ ≥ 0`, any sign of `ρ`).
3. **Maximal-domain lemma** is the existing `mem_domain_of_ESA` (`ClosedIdent.lean`), whose proof is `𝒟(L̄*) = 𝒟(L̄)` via F10
   (`mem_domain_of_adjoint`).  `f ∈ L²` is needed for the class `[f]`; it is NOT derivable from the other hypotheses (kept).
4. **Satisfiability / non-vacuity** (`ConverseDirectInst.lean`, all `#print axioms` = propext, Classical.choice, Quot.sound):
   * OU (`ouFull`, `CD(1,∞)`, `ouDiff_isComplete`), generic `f`, and the CONCRETE nontrivial `f = id`
     (`id ∈ 𝒜 = C^∞(ℝ)`, `id ∉ 𝒜₀`, `Γ id = 1`, `Γ₂ id = 1`, `id ∈ L²(γ)`): `[x] ∈ 𝒟(L̄)`, `L̄[x] = [−x]`.  The existing
     `ou_mem_domain_of_Γ₂` obtains the same via `Core2` and Hermite density; the direct proof needs neither.
   * circle (`circle_CD_zero_top`, `CompactTriple.isComplete`), Lebesgue (`lebesgue_CD_zero_infty`,
     `lebesgueDiffusion_isComplete`): generic statements.
   * `EllData d` with `Curv ρ` and `RiemData d` with `Curv ρ`: `ConverseDirectInst.ell_mem_domain_of_Γ₂_direct` and
     `riem_mem_domain_of_Γ₂_direct`, using `EllData.diff_isComplete` (already in the repo).  This REMOVES the hypothesis
     `CoreCut` of R19-Ell (bounded `Lχ, L²χ, Γ(Lχ), Γ₂χ`), so the converse is now unconditional for every `EllData`/`RiemData` with a
     curvature lower bound, including (where `Curv` holds) the hyperbolic plane that has no `CoreCut` (R19-Ell-2) and, via
     `GibbsRdData.toEll`, ℝ^d Gibbs measures with `HessGe`-type curvature without the growth condition `GrowHess3`.
     (Only the theorems stated were compiled; the Gibbs-to-Ell reduction is not re-proved here.)
5. Contrast with Core2: no implication either way is claimed.  Completeness is a hypothesis of the direct route only, but it holds in
   every concrete class of the repo (`gibbsDiff_isComplete`, `gibbsRdDiff_isComplete`, `diff_isComplete`, `riemDiff_isComplete`,
   compact triples, OU, Lebesgue).

## What is NOT claimed
* `Core2` itself is neither proved nor needed; this does not settle essential self-adjointness of `L²`.
* `CD(ρ,n)` must hold for ALL `f ∈ 𝒜` (as in `mem_domain_of_Γ₂`); no weaker local version.
* The theorem does not drop `f ∈ L²`, `Γ(f), Γ₂(f) ∈ L¹`, F10 or completeness.
* 1-D Gibbs (`GibbsData`) application not added (the `Gibbs/*` files belong to another stream); completeness and CD theorems exist.

## Hostile checks run
No `sorry`, no new axioms, no `set_option`; build of the three modules with 0 warnings; `#print axioms` clean.
