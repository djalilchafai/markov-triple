# HOSTILE AUDIT: R17 Stream A (Gibbs `Core2`, converse of BGL Prop 3.3.17 under bounded V', V'', V''')
Audited commit b77249f (branch worktree-agent-af9f8a40602298b81) on a detached checkout; Mathlib not rebuilt (build copied, packages symlinked).

## Verdict: no soundness defect, no hidden hypothesis, proofs real. One MEDIUM scope finding (the theorem is empty for rho > 0), three LOW/INFO doc points.

## Checks
1. Statements. `FullTriple.Core2` is the unchanged R15 definition in `Theory/Extension/Converse.lean` (same one used by `ouFull_core2`, which is proved by
   `core2_of_dense`); not weakened. `#check` (pp, probe) of `GibbsData.gibbs_mem_domain_of_Γ₂`: hypotheses are exactly `G.BddJet`, `∀ x, ρ ≤ V''`, `f ∈ A`,
   `MemLp f 2 G.μ`, `Integrable (G f f)`, `Integrable (Γ₂ f f)`; conclusion `∃ hF : [f] ∈ generator.domain, generator [f] =ᵐ L f`. No `Core2` hypothesis, no other
   implicit/instance hypothesis. `gibbsFull_core2 : G.BddJet → G.gibbsFull_unconditional.Core2`. `GibbsData` has only fields `V`, `smooth`, `integrable`
   (no smuggled assumption). `BddJet` = three `∃ C, ∀ x, |.| ≤ C` clauses, matches the frozen A0.
2. `#print axioms` on all ten audited theorems: propext, Classical.choice, Quot.sound only. grep: no sorry/set_option/axiom/admit/native_decide in Core2*.lean.
   `lake env lean` on each of the five Core2 files: 0 warnings, 0 errors. `scripts/check_frozen.py`: OK. `git diff --name-status main b77249f`: only added files plus
   ERRATA.md, MarkovTriple.lean, Theory/GAPS.md, frozen-manifest.json (new `proposed` entry); no frozen/fenced path modified.
3. Proofs real. `exists_resolvent_smooth` (Core2Resolvent.lean l.148-205) builds the Friedrichs resolvent `Rres`, gets a `ContDiff n` representative for every n via
   `resolvent_gain` (existing R15/R16 theorem), `smooth_rep_of_forall`, then the weak equation and du Bois-Reymond (`ae_eq_zero_of_integral_contDiff_smul_eq_zero`) +
   continuity. Smoothness is `Sm` (ContDiff ∞, not ω). `gibbsFull_core2` cuts off `chiR (Rn n) * v` with dominated convergence in `cutoff_ZL`; the identification of
   `(1-L)b_n - a` with `m0 - m1` is a genuine a.e. computation. Nothing is assumed in a structure.
4. Non-vacuity of the hypotheses (probe, throwaway file): `sqrtGibbs : GibbsData` (V = sqrt(1+x^2), integrability proved by comparison with 2/(1+x^2)) is genuine, finite
   measure, `sqrtGibbs_bddJet` proved with constants 1,1,3. Probe compiled `∀ x, 0 ≤ V''` for it. 

## Findings
* **MEDIUM (scope/vacuity of the stated curvature clause).** `BddJet` forces `V'` bounded, hence `inf V'' ≤ 0` (if `V'' ≥ ρ > 0` then `V'(x) ≥ V'(0)+ρx` unbounded).
  So `gibbs_mem_domain_of_Γ₂` can only be applied with `ρ ≤ 0`; for `ρ > 0` (the case that matters for LSI/PI, where the book uses the converse) the hypotheses are
  contradictory and the theorem is vacuous. Conversely, `BddJet` alone provides `ρ = -sup|V''|`, so the `ρ` hypothesis is always satisfiable, i.e. the converse is
  really "for every BddJet Gibbs triple with CD(-C,∞)". For `sqrtGibbs` the sharp constant is `ρ = 0` (V'' = (1+x^2)^(-3/2) > 0, V'' -> 0), never positive. Neither the
  STATEMENTS nor AUDIT file says this; the AUDIT's "with `V'' ≥ ρ`" and the ERRATA R17-2 phrase "UNCONDITIONAL" invite the reading that uniformly convex (ρ>0) non-Gaussian
  potentials are covered. They are not (those have unbounded V'); only OU (separate proof) covers ρ>0 in 1-D. Not a mathematical error; a documentation omission.
* **LOW (doc).** AUDIT item "A5 ... non-Gaussian, non-compact" does not state the curvature value; add "ρ ≤ 0 necessarily". Also statement A4 non-vacuity argument ("f = 1")
  holds, but the docs never exhibit a non-test f with Γ₂ integrable; fine, not required.
* **LOW (doc).** AUDIT: "Hypotheses of A4 on f are satisfied by every f in C_c^∞": true (compact support), OK, but then the content beyond R15 is only that `Core2` is discharged;
  the unconditional status for compact-support f was already a corollary of `mem_domain_of_A`-type results? Not checked; claim is harmless.
* **INFO (honesty).** "Partially closed/discharged" is accurate: GAPS, ERRATA R17-2 and AUDIT item 1 explicitly say Core2 is NOT proved for arbitrary Gibbs, nor for R^d,
  and speculate Core2 may fail for wild V (labelled belief, not claim). The STATEMENTS "Not claimed" cross-refers to `STATEMENTS_R17_Core2Rd.md` "if present"; it is absent
  in this commit (harmless dangling pointer). No overclaim found.
