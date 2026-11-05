# Hostile audit, R29 Stream P (de069e4 freeze, 4d9c7cc proofs, base f0edf3a)

Verdict: ACCEPT. No doc change was necessary.

## Findings (severity ranked)

1. LOW (process). `STATEMENTS_R29_P.md` was edited after the freeze commit de069e4 (a "Status" section of 11 lines was appended; the frozen
   statement block itself is untouched), and the manifest sha256 was updated in 4d9c7cc to the final file (entry status "proposed").
   check_frozen.py prints OK. The manifest diff vs main f0edf3a is exactly one appended entry; no duplicate or altered foreign entries.
   de069e4 contains only the statements file and the manifest entry; no Lean files precede it. The only drift from the frozen text is
   parenthesisation of P5/P6 integrals, declared in the Status section.
2. LOW (docs). The tightness equivalence is a characterisation, not progress on existence of a deficit point; the docs say so explicitly
   (GAPS, ERRATA R29-P-1, STATEMENTS). Correctly labelled "question still open".
3. INFO. P3 is correct and non-circular (checked by reading Tight.lean).
   * P1 (`tight_real_of_univ_eq_one`): uses only mass one at x0, inner regularity of kappa_t(x0,.) to get a compact K0 with mass > 1-delta/2,
     a Urysohn function f in C_c with 1_{K0} <= f <= 1, Feller continuity of Q_t f (so Q_t f > 1-delta near x0), and
     Q_t f(y) <= kappa_t(y, tsupport f). It does NOT assume mass one near x0 (only sub-Markov everywhere, which is a proved lemma).
     K = tsupport f is compact; U is a genuine neighbourhood. Hypotheses actually used: IsFellerC0, local compactness, T2, second countability,
     Borel. Full support is not needed.
   * P2 (`le_univ_of_tight_real`): needs only IsOpenPosMeasure (the good set {Q_t f >= 1-delta} is closed and has x0 in its closure
     because the a.e. bound on an open neighbourhood of positive measure produces good points arbitrarily near x0). S11 is not used;
     the docs state this honestly. The a.e. hypothesis is weaker than "for every y", so P3 is a true equivalence.
   * Quantifiers: for every eps>0 there exist a compact K and a neighbourhood U of x0 with the bound; this is non-trivial on non-compact X
     (K must be compact, bound uniform on U) and trivial on compact X, as expected for tightness.
   * Compact corollary (P4a) uses `fellerKernelInf_univ_ae` (S11 a.e. mass one) plus P2; consistent with R27 Mass.lean (a.e./ac-initial results)
     and with the compact survey. It strengthens a.e. to pointwise on compact spaces; no contradiction.
4. INFO. 1-D identities verified by hand. With c = V'u/2: (u'-c)^2 - (u'+c)^2 = -2V'uu'; (V'u^2)' = V''u^2 + 2V'uu', hence
   -2 int V'uu' = -[V'u^2]_a^b + int V''u^2. Lean statement oneD_boundary_identity matches, including signs. Hypotheses: HasDerivAt on [a,b]
   and continuity of u', V2 on [a,b] (so all integrals exist); no compact support needed because the boundary term is explicit.
   oneD_boundary_bound: -V1 b u b^2 + V1 a u a^2 <= -V1 b u b^2 when V1 a <= 0: correct. Docs call them pure real analysis,
   not tied to a FullTriple, and the converse of Prop 3.3.17 for n=infinity is stated as still open. No overclaim.
5. INFO. The by-hand 1-D no-counterexample arguments and the "no mass loss at a single point" heuristic are labelled "not formalised / heuristic /
   by hand" in STATEMENTS, GAPS and ERRATA R29-P-2.
6. Mechanical. Full `lake build` succeeded (9537 jobs), 0 warnings/errors in the whole log; no sorry/set_option/native_decide in R29P files;
   `#print axioms` run by me on all seven theorems: only propext, Classical.choice, Quot.sound. MarkovTriple.lean imports the three new files.
   The scratchpad script overwrite mentioned by the implementer did not affect the repo or manifest.
