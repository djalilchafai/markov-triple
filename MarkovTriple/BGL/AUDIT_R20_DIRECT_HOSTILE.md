# HOSTILE AUDIT R20 Stream D1 (commit bf4d522): direct converse of BGL Prop 3.3.17 for 1-D `GibbsData` and `GibbsRdData d`

Auditor: independent (Armstrong method). Everything below was re-derived or re-run; nothing taken from the author's audit.

## DIFFERENCE FROM BGL
This file only records checks. The audited route differs from BGL (p. 161-162): BGL uses the tacit core of `L^2` (`Core2`); D1 uses the cut-off identity on `Gamma_2`
(BGL Prop 3.2.1 technique) and ESA of `L` (BGL Prop 3.3.6 (i)). The audit confirms the route is sound; it does NOT claim `Core2` is solved (it is not, and is not needed).

## Verdict: NO finding above MEDIUM, and the MEDIUM is documentation/merge only. The claim (converse with only V'' >= rho / HessGe V rho, no Core2, no growth) stands.

## Findings (severity ranked)

* **F1 (MEDIUM, merge/doc, not Lean)**: the branch was cut before the D2/D3 merge, so D1 docs are stale relative to main:
  ERRATA R20-D1-4, GAPS D1 "Still open" and STATEMENTS "Not claimed" say `EllData`/`RiemData` and the general `FullTriple` converse are not done, whereas main has
  `ell_mem_domain_of_Gamma2_direct`, `riem_..._direct`, `FullTriple.mem_domain_of_Gamma2_direct` (ERRATA R20-D2-*, R20-D3-*, R20-M1). The branch's ERRATA R15-1 row lacks the R20-M1 UPDATE
  sentence and R20-M2 (on main) says D1 is not yet merged. `git merge-tree main bf4d522`: conflicts ONLY in ERRATA.md, GAPS.md, frozen-manifest.json (hand-merge keeping BOTH sides, otherwise the
  branch side deletes the D2/D3 entries). All Lean and MarkovTriple.lean hunks auto-merge. At merge: keep D2/D3 rows and manifest entries, add D1 rows, reword R20-D1-4/GAPS "not done" to
  "done by D2/D3 (abstract/Ell/Riem)", update R20-M2.
* **F2 (LOW, doc)**: STATEMENTS D1-2/D1-4 drafts still list `hf2 : MemLp f 2` and D1-5 describes the bump-sum potential / `spikyGibbs_hρ`; the deviations R20-D1-1/-2 are logged in the Status section as required.
  `AxiomCheckR20Direct.lean` has no `## DIFFERENCE FROM BGL` (a one-line comment only; no mathematics in it).
* **F3 (LOW, scope of witness)**: `spikyData_mem_domain_of_Gamma2` for R^d is only the general theorem specialised (no concrete `f`, unlike 1-D `spikyGibbs_id_mem_domain`). Mathematically the hypotheses are
  non-vacuous (f = x_1: Gamma = 1, Gamma_2 = v''(x_1) <= 3, x_1 in L^2) but this is not formalised for R^d. `spikyData_witness` is stated for `d+1` (d = 0 trivial).
* **F4 (INFO, collisions)**: `Direct*` names do not collide with D2 (`DirectEll*`, `DirectRiem*`, `ConverseDirect*`); no declaration-name collision (git grep on main for direct_pt, prim, spk*, rd_pt, sum_cross,
  spikyData, spikyGibbs: none). Scratch merge of main into bf4d522 (doc conflicts resolved `--ours`, discarded afterwards): a probe importing `AxiomCheckR20Direct`, `AxiomCheckR20DirectEll`,
  `ConverseDirectAxioms`, `DirectEllMain`, `DirectRiemMain` elaborates cleanly.
* **F5 (INFO, wording)**: "no growth conditions" is true for the converse. `Core2` is neither proved nor refuted for `spikyGibbs`; docs say so correctly. ERRATA D1-1 "supersedes R17-2, R18-1/..." is scoped "for the CONVERSE only": correct.

## Checks requested

1. **Statements.** `#check` of `gibbs_mem_domain_of_Γ₂_direct`, `gibbsRd_mem_domain_of_Γ₂_direct`, `memLp_Lg_of_Γ₂`, `memLp_Lr_of_Γ₂` (pp.explicit printed for the first): hypotheses exactly `hρ` (resp. `HessGe G.V ρ`),
   `f ∈ A`, `MemLp f 2`, `Integrable (G f f)`, `Integrable (Γ₂ f f)`; conclusion identical in shape to `gibbs_mem_domain_of_Γ₂` (which additionally has `G.BddJet`). No hidden Core2/growth argument (also by the walk in (4)).
   Lean statements equal frozen D1-1 and D1-3. D1-2/D1-4: Lean lemmas drop `hf2`; verified by hand that `f ∈ L²` is not used in the cut-off estimate (all integrals over compact supports; W ∈ L¹ from Γ(f), Γ₂(f) ∈ L¹ alone;
   the absorbed quantity ∫T is finite since T is compactly supported). `hf2` is used only in the final theorem to form `[f]`. The strengthening is genuine and logged (R20-D1-1).
2. **Non-vacuity.** `spkV` = double primitive of `spk = 2 + sin(e^{x²})`; `sm_prim` gives smoothness; `spkV_ge`: V >= x²/2 (V' >= x for x >= 0, V' <= x for x <= 0), so `e^{-V} <= e^{-x²/2}` is integrable: genuine `GibbsData`.
   `spk_peak`: for every X some x >= max(1,X) with e^{x²} = 2πk, cos = 1, so V''' = 2x e^{x²}. `spikyGibbs_not_polyHess` destructs `⟨-,-,C,N,hC⟩`: the THIRD clause (|V'''| <= C(1+|V'|^N)) fails
   (clauses 1-2 hold, 1 <= V'' <= 3); real proof via e^{x²} >= x^{2N}/N!, |V'| <= 3x, case N = 0 handled. `GrowHess ⇒ PolyHess`, `BddHess ⇒ GrowHess`, `BddJet` needs V' and V''' bounded (both false): spiky is outside the
   R17/R18/R19 1-D classes. Real theorems instantiated: `spikyGibbs_mem_domain_of_Γ₂` and `spikyGibbs_id_mem_domain` (f = id: Γ = 1, Γ₂ = V'' ∈ [1,3], id ∈ L² by `spikyGibbs_memLp_id`; L[x] = [-V']).
   R^d: `spikyData d` = Σ v(x_i) via `ofConvex`; `hessGe_spkVd`; `spikyData_not_growHess3` at (x₀,0,…,0): third-derivative clause fails; `BddHess3 ⇒ GrowHess3`. See F3.
3. **Math by hand.** (1-D) u = Lf, F7: ∫χ²u² = -∫(χ²u)'f' = -2∫χχ'uf' - ∫χ²u'f'; ∫χ²·½L(f'²) = -2∫χχ'f'f''; Bochner f'u' = ½L(f'²) - Γ₂, hence ∫χ²u² = -2∫χχ'uf' + 2∫χχ'f'f'' + ∫χ²Γ₂ (matches Lean
   `eT`, `e3`, `hpt`). Young: -2cc'us <= ½c²u² + 2c'²s²; 2cc'st <= K(s²+t²); f''² = Γ₂ - V''f'² <= |Γ₂| + |ρ|f'² (only use of V'' >= ρ); W ∈ L¹ independent of n; ∫T <= ½∫T + ∫W so ∫(χ_n u)² <= 2∫W; Fatou with χ_n → 1.
   Every product carries χ or χ², so f need not be compactly supported; f'' is locally bounded (smooth), no L²_loc issue; cross term bounded via Γ(f) ∈ L¹ and f''² <= |Γ₂| + |ρ|f'². (R^d) `sum_cross` is termwise Cauchy–Schwarz,
   |Hess f|² = Γ₂ - Hess V(∇f,∇f) <= |Γ₂| + |ρ||∇f|² from `HessGe`; `rd_pt` constants check. No error found. Consistent with the book (∫Γ₂ = ∫(Lf)² on D(L)); ESA of L (F10, proved for all Gibbs triples, not assumed)
   converts Lf ∈ L² into f ∈ D(L̄).
4. **Constant-graph probe** (throwaway `Lean.Environment` walk over all `MarkovTriple.*` constants in type+value): `gibbs_mem_domain_of_Γ₂_direct` (271 consts), `memLp_Lg_of_Γ₂` (8), `gibbsRd_mem_domain_of_Γ₂_direct` (286),
   `memLp_Lr_of_Γ₂` (23), `spikyGibbs_id_mem_domain` (277), `spikyData_mem_domain_of_Γ₂` (299): none contains Core2, CoreCut, GrowHess, PolyHess, BddHess, BddJet. Controls: `gibbs_mem_domain_of_Γ₂` flags `BddJet`;
   `gibbs_mem_domain_of_Γ₂_polyHess` flags `PolyHess`; `FullTriple.mem_domain_of_Γ₂` flags `FullTriple.Core2`; `mem_domain_of_ESA` clean.
5. **Axioms/hygiene.** `AxiomCheckR20Direct` builds; all 21 `#print axioms` = {propext, Classical.choice, Quot.sound}. No `sorry`, `set_option`, `axiom` in the D1 files; `lake env lean` on each of the 7 D1 Lean files: 0 warnings, 0 errors.
   Build hygiene as instructed (Mathlib not rebuilt); no lake/lean process left.
6. **Docs honesty.** `## DIFFERENCE FROM BGL` in all new Lean/md files except `AxiomCheckR20Direct.lean` (F2). No claim that Core2 is solved; R15-1 correctly kept as about the book's route; R20-M1 reconciliation missing only by branch age (F1).
7. **Frozen.** `python3 scripts/check_frozen.py`: OK at bf4d522. frozen-manifest.json diff vs main: a new `proposed` entry for `Instances/Gibbs/STATEMENTS_R20_Direct.md` (removed entries are the D2/D3 STATEMENTS entries absent on this older base; keep them at merge, F1). No frozen/fenced file edited.

## Merge recommendation
Merge D1 after hand-resolving ERRATA/GAPS/frozen-manifest (keep D2/D3 rows and manifest entries, add D1's, fix stale "not done" statements, F1). No Lean change needed.
