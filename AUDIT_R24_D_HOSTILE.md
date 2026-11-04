# AUDIT R24 Stream D (hostile): Core2 duality criterion, `goFullTriple` is not Core2

Audited: merge of `worktree-agent-ad01d719fbd869a45` (impl HEAD c491e36, base 6bff800).  Verdict: **ACCEPT** (0 HIGH, 0 MEDIUM, 3 LOW doc/process).

## Checks performed
* Full-repo `lake build`: success, 9443 jobs.  Each R24 file re-run with `lake env lean`: no output (0 warnings, 0 errors).
  `grep` over `R24/*.lean`: no `sorry`, `set_option`, `axiom`, `native_decide`.
* `#print axioms` run by me (`AxiomCheckR24D.lean`) on `core2_orth`, `core2_iff_dense`, `go_not_core2_of_pair`, `R24.holder`,
  `R24.ode_series`, `go_deficiency_pair`, `goFullTriple_not_core2`, `exists_fullTriple_cd_not_core2`, `hyp_core2_route_status`,
  `hyp_core2_of_coreCut`: all only `propext, Classical.choice, Quot.sound`.
* `scripts/check_frozen.py`: OK.  Manifest has exactly one entry for `STATEMENTS_R24_D.md`, status `proposed`, hash matches the file.
* (a) `Core2` (Extension/Converse.lean:237) is: for each `a in A0` there are `b_n in A0` with `(1-L)b_n -> a` and `L(1-L)b_n -> La` in L2
  (the graph-density form of "(1-L)A0 is a core for L", i.e. A0 core for L2).  This is the real BGL-tacit notion, with `L` on `A0`
  (not closure-dependent) and `A0 = C_c^infty((-1,1))` for `goFullTriple`.  The negation is not a domain artefact.
  Hand re-derivation: recurrence `(n+1)(n+2)a_{n+2} = (n^2+3n+1)a_n` is exactly `Lw = w` for `L=(1-x^2)d^2-4x d` (matches `aa`);
  indicial exponents at x=1 are 0 and -1, so singular solution `(1-x)^{-1}` is log-divergent in L2(mu): L is ESA (F10) but borderline.
  `L[(Lam/4)log(1-x^2)] = (Lam/4)(6x^2-2)/(1-x^2)` (checked by hand), which cancels the `Lam/(1-x^2)` blow-up of `w`, leaving
  `(1-x^2) g^2` bounded, so `g=w-Lh in L2(mu)`, `h in L2(mu)` (`s log^2 s` bounded) are plausible and are proved.  Sign: the pairing is
  with `w`, `(1-L)w=0`; Lean's `hb` computes `<(1-L)b, w1> = int b w1 - int Lb w1 = int b (w1 - Lw1) = 0` through local copies `w1 in A0`
  (lemma `key`, `sym_A0`), and `a`-test: `int a w1 != 0` with a bump on a sign-definite neighbourhood of `w(0)=1`: sound.  Mechanism
  agrees with the classical "Delta^2 on R^n minus a point is ESA iff n >= 8" (here the reduced dimension is 4 < 8).
  Functional is continuous in `(c, Lc)` in L2 x L2, which is exactly what `Core2` controls: `core2_orth` correctly uses both convergences.
* (b) Statements as proved are faithful and non-vacuous (`w(0)=1`).  `exists_fullTriple_cd_not_core2` is `<goFullTriple, goFullTriple_CD, ...>`
  with `goFullTriple := goFull go_esaProp` : a genuine `FullTriple ℝ` (F1-F10 are structure fields, F10 discharged by R23-F-1) with `CD 3 4`.
  Consistent with R15-1 (Core2 tacit, never derived), R20 (converse of Prop 3.3.17 without Core2 for complete triples) and Stream B.
  No theorem elsewhere in the repo claims Core2 for a general F1-F10+CD triple (all Core2 instances are for OU/Gibbs/Riem with
  completeness/cut-off hypotheses); a clash would in any case have produced `False` in Lean.
* (e) Honest scope: R24-D-1 states non-complete only; R24-D-4 and GAPS list Core2 for hypRiem / complete triples as OPEN; the Poincare-style
  heuristic in R24-D-4 is labelled "by hand (unverified here, no Lean)".  `hyp_core2_route_status` is pure packaging of earlier results
  (the "not RadialJets" conjuncts are R22 results; the theorem says nothing about Core2 of hypRiem itself); `hyp_core2_of_coreCut` is a conditional.

## Findings
1. LOW (process): commit 66d4827 adds `STATEMENTS_R24_D.md` and the manifest entry in the SAME commit as `Core2Criterion.lean` and `GoCore2.lean`
   (parts A, B1), so statements were not committed strictly before those proofs.  GoPair/GoSeries/HypStatus (B2-B4, C) came after.  Also the manifest
   hash was re-sealed in c491e36 after the Status/analysis section was appended; the diff shows the Targets section is byte-identical, only Status added.
2. LOW (doc, stale): the docstring of `Core2` in `Theory/Extension/Converse.lean` still says "we know of no counter-model satisfying F1-F10"; now false
   (`goFullTriple_not_core2`).  The R23-F-1 / older GAPS line ("not formalised") is superseded by the new GAPS Round 24 entry but not edited.  Not changed here
   (core file; edit would not alter statements but I did not touch it).  Suggested one-line addendum: "(see R24-D-1: `goFullTriple` is one)".
3. LOW (doc): STATEMENTS "Mathematical analysis" asserts `Core2` for F1-F10+CD "is FALSE (new, part B)" in a section frozen before the proof; harmless since proved.
   `hyp_core2_of_coreCut` is an extra theorem outside the frozen list (logged as deviation in Status; fine).

No fixes applied to sources; report only.
