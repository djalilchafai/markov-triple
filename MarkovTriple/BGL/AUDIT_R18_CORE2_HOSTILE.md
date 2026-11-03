# Hostile audit R18 Stream A2 (Core2 for GrowHess Gibbs), commit 12b88e0

Verdict: NO CRITICAL / HIGH / MEDIUM finding.  The claimed theorems are proved and non-vacuous.  Three LOW doc items.

## Verified
1. Build hygiene: `.lake/build` copied, `.lake/packages` symlinked; Mathlib replayed, not rebuilt.  `lake build ...AxiomCheckR18Core2` OK.
2. Axioms: all 19 `#print axioms` (hardy_ibp, memLp_of_BE, memLp_of_hardy, resolvent_weighted_L2, cutoff_ZL_w, *_core2_of_growHess/bddHess,
   *_mem_domain_of_Γ₂_growHess/bddHess, cos*/quar* witnesses) give only propext, Classical.choice, Quot.sound.  No sorry/axiom/admit/set_option
   in Core2W*.lean; 0 warnings (re-elaborated each file with `lake env lean`).
3. Statements (pp.explicit probe): `gibbsFull_core2_of_growHess : ∀ G, G.GrowHess → FullTriple.Core2 G.gibbsFull_unconditional`; the converse takes only
   GrowHess, `∀x, ρ ≤ V''`, `f ∈ A`, `MemLp f 2`, `Γ(f), Γ₂(f)` integrable; no hidden Core2 or extra hypothesis.  `FullTriple.Core2` is the
   unchanged R15 def in Theory/Extension/Converse.lean:237 (untouched by the diff).  GrowHess = ∃C ∀x, |V''|≤C(1+|V'|) ∧ |V'''|≤C(1+|V'|).
4. Non-vacuity by hand and in Lean: cos: V'=x-sin x/2, V''=1-cos x/2∈[1/2,3/2], V'''=sin x/2, bounded hence in GrowHess; V'' ≥ 1/2 > 0 and
   V' unbounded.  quartic: V''=3x²+1, V'''=6x, V'=x³+x, |V'|=|x|(x²+1); 3x²+1 ≤ 6(1+|x|³+|x|) and 6|x| ≤ 6(1+|V'|): C=6 valid.  Both are genuine
   GibbsData (smooth, `exp(-V)` integrable, proved via Gaussian domination), and `cosGibbs_core2`, `quarGibbs_core2`, `*_mem_domain_of_Γ₂` are
   instantiated with `ρ=1/2`, `ρ=1` (convexity lemmas proved).  `cosGibbs_not_bddJet`, `quarGibbs_not_bddHess` proved.  GrowHess jointly satisfiable
   with ρ>0 (contrast R17 BddJet).
5. Proofs: `hardy_ibp` applies `ibp_master` with test function x, P=η²V'f² smooth compactly supported, so no boundary terms; identity
   H=P'-V'P expanded correctly (checked by hand).  (BE): with q=f'-V'f, t=ηV'f, H = η²V''f²+2ηη'V'f²+η²V'²f²+2η²V'fq = η²V''f²+2η'ft+t²+2tηq,
   so t² = H - η²V''f² - ..., and the lower bound V'' ≥ -Cw(1+|V'|) is used with the right sign (a1).  (Hardy): H = η²V''f²+2η'ft+2tηf'-t², so
   t² ≤ η²V''f²+... - H, upper bound V'' ≤ V'²/4+B used correctly, s=-4.  In the application GrowHess gives V'' ≥ -C(1+|V'|) directly and
   V'' ≤ C+C|V'| ≤ V'²/4+C+C² (AM-GM): signs correct.  Only |η'| ≤ K (chiR_iter_bound) is used; Fatou via R17 memLp_two_of_cutoff with n-uniform
   bound.  No structure field hides assumptions (GibbsData: smooth, integrable).  `cutoff_ZL_w` coefficients: only `memLp_mul_growth`
   (|c| ≤ C(1+|V'|)) is used, never bounds on V'.  The Core2 assembly is a clean Lp-equality computation.
6. BGL numbering (PDF found at /tmp/claude-1000/bgl/bgl.pdf, extracted text): Prop 3.2.1 (ESA, p.142), Def 3.3.9 (Completeness, p.157), Prop 3.3.17
   (p.161-162, converse requires "additional ergodicity", noted in the repo as ERRATA R15-1; the Lean converse replaces ESA/ergodicity by Core2) all
   match the citations.  The proof is a direct cut-off/graph-norm argument in the spirit of 3.2.1, not BGL's.
7. Frozen: `scripts/check_frozen.py` OK; diff vs main touches only the manifest (one new `proposed` entry for STATEMENTS_R18_Core2.md), no frozen/fenced file.

## Findings
- LOW-1 (doc inconsistency): STATEMENTS_R18_Core2.md body still says "Not claimed: Core2 for V'' unbounded (e.g. x⁴)" and B1/B2 signatures differ from the Lean
  ones; Status section (R18-D1..D3) logs both and supersedes, and `quarGibbs` (x⁴/4+x²/2) is proved, but the body text now reads as contradicted.  Note
  the sha256 registered is that of the post-proof text (statements were edited after proofs via logged deviations; acceptable but not "pre-proof frozen").
- LOW-2 (doc): AUDIT_R18_CORE2.md attack 2 says the hypotheses `Γ(f),Γ₂(f)∈L¹` are "satisfied by f∈C_c^∞ (not re-formalised)": correct but the final
  converse instances `cosGibbs_mem_domain_of_Γ₂` are therefore not shown non-vacuous by an explicit f in Lean (the converse content is mostly for non-compactly
  supported f; a witness f is not provided).
- LOW-3 (stale docs): STATEMENTS_R17_Core2.md, AUDIT_R17 and AxiomCheckR17 still state ρ>0 open; only superseded by ERRATA R18-1 and GAPS (acceptable, R17-M1 pointed to R18-1 in AUDIT_R18_CORE2.md; ERRATA R17-M1 row itself not annotated).
- No overclaim: Core2 for arbitrary V is explicitly not claimed (R18-4, GAPS); sharpness of GrowHess is explicitly not claimed.
