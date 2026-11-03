# AUDIT R18 Stream A3 (Core2 on R^d Gibbs, `BddHess3`): independent hostile audit

Audited commit `e18a898` (branch `worktree-agent-add5b1ea2bc3491ff`). Build: `.lake/build` copied, `.lake/packages` symlinked; only the new modules were
(re)built (Mathlib not rebuilt). Probes were throwaway files outside the repo.

## Verdict: no CRITICAL/HIGH/MEDIUM finding. The result is real and non-vacuous.

## Checks
1. Statements. `pp.explicit` of `gibbsRd_core2` : `∀ {d} (G : GibbsRdData d), G.BddHess3 → FullTriple.Core2 (G.gibbsRdFull_unconditional)`;
   `gibbsRd_mem_domain_of_Γ₂ : G.BddHess3 → HessGe G.V ρ → f ∈ A → MemLp f 2 μ → Integrable (G f f) → Integrable (Γ₂ f f) → ∃ hF, ↑(generator ⟨[f],hF⟩) =ᵐ L f`.
   No hidden hypothesis. `BddHess3` = two `∃ C` bounds on `∂ᵢ∂ⱼV`, `∂ᵢ∂ⱼ∂ₖV`, exactly as frozen. `FullTriple.Core2` is the unchanged definition of
   `Theory/Extension/Converse.lean:237` (same one used by `OU/Core2.lean`, `ouFull_core2`). `GibbsRdData` has only the fields `V`, `smooth`, `integrable`
   (no `a_exh`-type smuggling); `gibbsRdFull_unconditional` was proved earlier (WeakHypo/F8), no new structure fields anywhere in the diff.
2. Non-vacuity (the R17 lesson). Verified by hand: `cosV = |x|²/2 + cos(x₀)/2`, `∂ᵢ∂ⱼV = δᵢⱼ - δᵢ₀δⱼ₀ cos(x₀)/2`, so `Hess V ≥ I - (1/2)e₀e₀ᵀ ≥ 1/2` and
   `|∂ᵢ∂ⱼV| ≤ 3/2 ≤ 2`; `∂³V = δ sin(x₀)/2`, `≤ 1/2 ≤ 1`; `e^{-V} ≤ e^{1/2} e^{-|x|²/2}` integrable (via `integrable_of_convex_rd`, so `μ` is a finite measure).
   `∇V` grows linearly and is unbounded. Lean: `cosData := GibbsRdData.ofConvex …` (a genuine `GibbsRdData`), `cosData_witness`, `cosData_core2`,
   `cosData_mem_domain_of_Γ₂`, `gaussData_*` are INSTANTIATED theorems, not just stated; I additionally typechecked `gaussData 0`, `gaussData 1`, `cosData 0` (R¹) `.Core2`.
   `BddHess3` and `ρ>0` are jointly satisfiable. Edge d=0: `Lr = 0` handled separately, compiles.
3. Axioms: all 14 `#print axioms` in `AxiomCheckR18Core2Rd.lean` and the probes give only `propext, Classical.choice, Quot.sound` (some lines omit Classical.choice, still within set).
   No `sorry/admit/axiom/set_option/native_decide` in `Core2Rd*.lean`. Each of the 11 `Core2Rd*.lean` files compiled with `lake env lean`: 0 warnings, 0 errors.
4. Proofs inspected. `exists_resolvent_smooth`: chain `v,a,(1-L)a,…` into the existing `ellReg`, then classical equation via IBP against test functions (real).
   `hess_bound`: pointwise Bochner `Hess v² ≤ ½ φ L Γ(v)+W` using `hρ` (only `Hess V ≥ ρ`, `ρ` any sign, Cauchy–Schwarz for `Γ(v,a)`), IBP of `φ L Γ(v)` onto `Γ(v) Lφ`, `|L(ψ²)| ≤ K'`
   from `|Lψ| ≤ K` and `|∇ψ|² ≤ 8C²`; this really derives `∇²v ∈ L²` from `Hess V ≥ ρ` + `|Lχ_n| ≤ K` (the latter from `BddHess3` via linear gradient growth). `core2_of_ZL`/`cutoff_ZL`: uniformly bounded
   coefficients (`CoeffGood`) times `L²` data, vanishing a.e. eventually ⇒ dominated convergence; commutator formula `Lr_remainder` proved from `Lr_mul`, `Lr_Gr`.
5. Docs. No overclaim: GAPS, STATEMENTS, AUDIT all state that unbounded `Hess V`/`∇³V`, `EllData`, `RiemData`, general `V` are NOT proved.
6. `scripts/check_frozen.py`: OK. Diff vs main touches only new files plus `ERRATA.md`, `GAPS.md`, `MarkovTriple.lean`, `frozen-manifest.json` (one new `proposed` entry). No frozen/fenced file edited.

## Findings (all LOW/INFO)
* L1 (LOW, doc). ERRATA R18-1 says "supersedes R17-2 for `ℝ^d`"; R17-2 is the Feller joint-measurability entry, unrelated. It should cite R17-M1 / R15-3 (Core2 for Gibbs conditional). Also the R18 ERRATA section has no table header row.
* L2 (LOW, doc). `GAPS.md` line "Partial: Core2 for 1-D Gibbs … open for general V, R^d, and for ρ>0 beyond OU" (Round 17 block) is now stale/inconsistent with the Round 18 block (R^d with `BddHess3` incl. d=1 via `GibbsRdData` is proved, but the 1-D `GibbsData` class is a different structure); no cross-reference.
* L3 (LOW, process). `AUDIT_R18_CORE2RD.md` claims "full `lake build` OK" and "book PDF not located; page numbers not checked"; I did not rebuild the whole project (only audited modules). STATEMENTS md was edited after being registered `proposed` (hash refreshed, allowed for `proposed`, disclosed as R18-3).
* L4 (INFO, scope). `BddHess3` (bounded Hessian) forces `|∇V| ≲ 1+|x|`; quartic-type potentials (`|x|⁴`) are excluded, correctly disclosed. `BddHess3.hessGe` shows the hypothesis already implies some `HessGe V ρ`, so the `ρ` in the converse is a genuine extra hypothesis only for the CD constant, as documented.
* L5 (INFO). `cosData` needs dimension `d+1 ≥ 1`; for `d=0` only the Gaussian witness exists (trivial space). Fine.
