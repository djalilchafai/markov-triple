# Hostile audit, Round 25 Stream F (Core2 on R^d Lebesgue / Gaussian)

Auditor: independent; merged `worktree-agent-a05cea8655f969957` (8737558, 8cf4b63) on top of main 0e15ea7.

## Verdict: ACCEPT (with 1 MEDIUM and 3 LOW documentation findings; no mathematical or formal defect found)

## Checks
- (d) Build: full `lake build` OK (9478 jobs), 0 warnings; no `sorry`, `set_option`, `native_decide`, `axiom` in `Core2/*.lean`.
  `#print axioms` run on `cutoff4_graph_aux`, `heat_graph4`, `eq_zero_of_orth4`, `dense_Ψ_lebesgueRd`, `lebesgueRdFull_core2`, `gaussRdFull_core2`,
  `lebesgueRdFull_mem_domain_of_Γ₂`: only propext, Classical.choice, Quot.sound.
- (c) History: 8737558 touches only `STATEMENTS_R25_F.md` (32 lines) and `frozen-manifest.json` (one new entry); all Lean files, ERRATA, GAPS come in 8cf4b63.
  The freeze file contains the three theorem statements verbatim as proved (checked against Main.lean). 8cf4b63 only changes the manifest hash (because the Status
  section was appended to the frozen file, repo convention; the statements section is unchanged). No duplicate entries; `check_frozen.py` prints OK.
- (a) `Core2` (Theory/Extension/Converse.lean:237) is the real notion (approximating sequence with (1-L)b_n -> a, L(1-L)b_n -> La in L^2). All three theorems are about the genuine
  `lebesgueRdFull d hd` / `gaussRdFull d` (Full/Main.lean, Full/GaussFinite.lean). `lebesgueRdFull_core2` is `core2_of_dense (dense_Ψ_lebesgueRd hd)`, with density proved from
  `eq_zero_of_orth4` by orthogonal complement. Hypotheses of F3 are the generic ones (`CD ρ n`, `Γ₂`/`G` integrable); `lebesgueRdFull_CD_iff` shows `CD ρ n` iff `ρ ≤ 0 ∧ d ≤ n`, so
  the hypothesis is satisfiable (ρ = 0, any n >= d including n = ∞); not vacuous.
- (b) Math. Fourth-order cut-off: Δ²(χv) expands into terms (∂^kχ_n)(∂^j v), k >= 1, j <= 3-ish, k+j <= 4, with ∂^kχ_n = O(n^{-k}) (rescaled profiles `Sc`, `SmallFam`);
  `cutoff4_graph_aux` takes exactly the needed L^2 jets of v (v, ∂v, ∂²v, Δv, ∂Δv, ∂∂v-terms, ΔΔv) as hypotheses, which are discharged by `heat_graph4` for v = heat φ (all jets of heat φ are heat of
  C_c^∞ jets). Convergence of [b_n], [Lb_n], [LLb_n] is the product small-family times L^2 plus dominated convergence for χ_n v - v; sound. ODE: with G_k(s) = <w, heat_s L^kφ>,
  G0' = s G1, G1' = s G2 (heat parameter s plays the role of "a"; derivative carries factor s, as implemented), orthogonality gives G2 = 2G1 - G0, hence H = G1 - G0 has H' = sH,
  bounded by ‖w‖(‖heat Lφ‖+‖φ‖); `ode_all_zero` (multiply by e^{-s²/2}) gives H ≡ 0, then G0' = sG0, bounded, so G0(0) = <w,φ> = 0 (via `zero_of_ode_bdd`). Correct. Claim "no resolvent solution
  needed" is true: no 1-D resolvent is used.
- Statement "no abstract complete + CD ⇒ Core2": consistent with R24-D; nothing is claimed; honest.

## Findings
1. MEDIUM (docs, scope/novelty): `lebesgueRdFull_mem_domain_of_Γ₂` has the same conclusion and hypotheses as `FullTriple.mem_domain_of_Γ₂_direct` (R20, needs only `IsComplete`) and the
   finite-n converse of Stream B; `lebesgueRdFull` is complete (R24-A ESA), so F3 follows from R20 already, including n = ∞. It adds no new strength; its value is only that the BGL route
   (through Core2) is now available for this triple. ERRATA R25-F-1 / GAPS present it as a "Core2-based converse, any CD ρ n incl. n = ∞" without saying this. FIXED in docs below.
2. LOW (docs): `gaussRdFull_core2` is a pure rename/wrapper of R18 `gaussData_core2` (disclosed in STATEMENTS Status and ERRATA R25-F-1 "= R18 gaussData_core2"; GAPS says "R18 theorem under
   the R24 name"). Adequately disclosed; no inflation of the count of new results should be made.
3. LOW (docs): ERRATA R25-F-1 says "`ρ ≤ 0`" as if a restriction of the theorem; it is just the exact range where `CD` holds here (`lebesgueRdFull_CD_iff`). Clarified below.
4. LOW (docs): the statements file describes ODE as `G₀' = aG₁`, implemented with parameter s: harmless notation.
Stale placeholder text: none found (grep for TODO/placeholder/WIP empty). ERRATA R25-F-2 is accurate (cf. R24-D-3, `goFullTriple_not_core2`).
