# HOSTILE AUDIT R19 Stream A5 (Core2 + converse of BGL Prop 3.3.17 on R^d under `HessGe V rho` + `GrowHess3`)

Audited commit `de620d7` (branch `worktree-agent-a902c4f8da732d2ac`), independent re-check; nothing on that branch fixed.
Build hygiene: `.lake/build` copied, `.lake/packages` symlinked; only the 4 new `Core2RdW*` modules plus the axiom-check file were (re)built (9168 jobs, Mathlib not rebuilt).
Each `Core2RdW*.lean` also compiled singly with `lake env lean`: 0 errors, 0 warnings. No lake/lean process of mine left running.

## Verdict: no CRITICAL, HIGH or MEDIUM finding. The claims hold. Three LOW/INFO remarks.

## 1. Statements and hidden hypotheses
* `#check` with `pp.explicit` of `gibbsRd_core2_w`: `forall {d} (G : GibbsRdData d) {rho}, HessGe G.V rho -> G.GrowHess3 -> FullTriple.Core2 (G.gibbsRdFull_unconditional)`. Nothing else.
* `gibbsRd_mem_domain_of_Gamma2_w`: `forall G {rho}, HessGe -> GrowHess3 -> forall {f}, f in A -> forall (hf2 : MemLp f 2 mu), Integrable (G f f) -> Integrable (Gamma2 f f) -> exists hF, generator = L f a.e.`. No hidden Core2 or extra hypothesis.
* `FullTriple.Core2` printed: unchanged definition (Theory/Extension/Converse.lean:237; no file under `Theory/` other than GAPS.md differs from main).
* Extra hypotheses of C3 (`v, grad v, Hess v in L2`) and C4 (`d_k V * Lv in L2`): both are discharged INSIDE `gibbsRd_core2_w`: `v in L2` from `exists_resolvent_smooth`, `grad v` from `memLp_grad_resolvent`, `Hess v` from `memLp_hess_resolvent_free` (hypothesis `HessGe` only), `W1..W3` from `resolvent_weighted_L2`, `hWL` from `W1` and `a in C_c` (compact support). Not hidden assumptions of the final theorems. The C3 deviation actually weakens hypotheses (drops `hrho`, `Lv = v-a`), so it strengthens the lemma. `cutoff_ZL_w` is not part of the final statements.
* `GrowHess3` printed: exactly the two `exists C` fields (Hess and third derivatives <= C(1+sum|d_l V|)).

## 2. Non-vacuity (hand verified and Lean)
* `quarData d`: V = sum(x^4/4 + x^2/2), d_i V = x^3+x, d_i d_i V = 3x^2+1 >= 1, d_i^3 V = 6x_i, off-diagonal 0. Constant check: 3x^2+1 <= 3(1 + |x|^3 + |x|) since 2x^2 <= |x|^3+|x| (AM-GM); so C=3 works (Lean proves it via `x^2 <= 1+|x|^3`). Third: 6|x| <= 6(1+|x|^3+|x|). OK.
* `quarData := GibbsRdData.ofConvex` with `0 < 1` and `HessGe V 1`: genuine `GibbsRdData` (smooth, `exp(-V)` integrable); finite measure via the structure's `integrable` field (confirmed by `#print GibbsRdData`).
* `quarData_not_bddHess3 d : not (quarData (d+1)).BddHess3`: real proof, evaluating `d0 d0 V` at the constant point `|C|+1` giving `3(|C|+1)^2+1 <= C`, contradiction. d=0 edge: `quarData 0` exists, `example : (quarData 0).GrowHess3` and `example : not (quarData 1).BddHess3` compile in my probe.
* `quarData_core2`, `quarData_mem_domain_of_Gamma2`, `quarData_witness`, `gaussData_growHess3` are instantiated and compile.

## 3. Axioms / hygiene
`#print axioms` on all 12 listed theorems (core2_w, mem_domain_w, hess_resolvent_free, V_mul_of_hardy, resolvent_weighted_L2, growHess3, laplace_le, cutoff_ZL_w, quarData_witness/core2/mem_domain, gaussData_growHess3): only `propext, Classical.choice, Quot.sound`. grep: no `sorry`, `set_option`, `native_decide`, `axiom` in the R19 files. `python3 scripts/check_frozen.py`: OK. Diff vs main touches only: ERRATA.md, GAPS.md (appends), MarkovTriple.lean (imports), frozen-manifest.json (one new `proposed` entry), new files. R18 files untouched.

## 4. Proofs are real
* `hess_bound_free` / `memLp_hess_resolvent_free`: uses `ibp_Lr` with `phi = cut^2` (compactly supported) for `int phi L Gamma(v) = -int Gamma(phi, Gamma v)`; pointwise Bochner (`bochner_pt`, `hess_pt`, R18) with `HessGe` giving `Q >= rho Gamma(v)`; Young step `hessIBP_pt` (verified algebra: `-(2 q psi)(2 h a)/2 <= 1/4 psi^2 h^2 + 4 q^2 a^2`) absorbed with factor 1/4 giving the constant 4/3; only `sum |d_k cut|^2 <= 8C^2` (R=n+1>=1) is used. The Laplacian of the cut-off never appears (L(cut) is not needed, because the identity moves the derivative onto Gamma(phi, .) rather than onto L(phi); the |grad V| in L(chi) is thereby avoided). Absorption done at finite R (all integrals compactly supported), before Fatou (`memLp_two_of_cut`). Sound.
* `hardy_bound`/`memLp_V_mul_of_hardy`: `ibp_Lr` with test function V, `LV = Delta V - |grad V|^2`, so `int g|grad V|^2 = int g Delta V + int Gamma(g,V)`; `hardy_pt` is the exact real inequality with Young 1/2 + the 1/4 from `Delta V <= |grad V|^2/4 + B`; plausible and compiled. Hypothesis `Delta V <= Gr V V/4 + B` IS implied in the application: `GrowHess3.laplace_le` (sum of d diagonal terms <= dC(1+s), `s^2 <= d N` Cauchy-Schwarz, `d C s <= N/4 + d^3 C^2` from `(s-2d^2 C)^2>=0`; correct signs and constants, d=0 handled separately). Used as `hB` in `resolvent_weighted_L2` (via `simpa [Gr, sq]`).
* `resolvent_weighted_L2`: order W1 -> (Hess v from C1) -> W2 (Hardy applied to `d_i v`, needs `Hess v in L2`) -> W3 (Hardy applied to `d_k V v`, whose gradient is `d_i d_k V v + d_k V d_i v`, in L2 by `memLp_mul_growth` and W2). No circularity.
* `cutoff_ZL_w` / `ZL_Lchi`, `ZL_dLchi`, `ZL_LLchi`: every term is `Good` (derivatives of order 1..4 of chi_n, uniformly bounded, eventually zero) times an `L2` weighted jet; `GrowHess3` converts `d^2V g`, `d^3V g` into Hardy jets. Final identity via `Lr_Lr_mul` (R18) and `ring`. Real.

## 5. Findings (severity ranked)
1. LOW (process): `STATEMENTS_R19_Core2Rd.md` was edited after being fixed (Status section appended; hash refreshed in manifest, entry is only `proposed`, so allowed, and the Status section documents R19-Rd-4). The C3 statement text still lists `hrho` and `Lv = v - a` hypotheses while the Lean lemma has different (weaker) ones; logged in ERRATA R19-Rd-4. No action needed.
2. LOW (docs): the audit's claim "full `lake build` OK (9347 jobs)" is not independently re-run here (I built only the audited modules, 9168 jobs including this branch's new modules, success, no warnings). ERRATA R19-Rd-1 says "supersedes the open part of R18-Rd-1", accurate.
3. INFO (scope, honestly stated): `Core2` for `HessGe V rho` alone is NOT proved; `GrowHess3` is a genuine extra hypothesis, sharpness is not claimed (GAPS, ERRATA R19-Rd-2 HIGH "honest scope", AUDIT section 4). The GAPS example "e^{|x|^2}-type V" (Hess/|grad| unbounded) is correct. No overclaim found. The radial quartic is correctly declared not formalised; separable witness only.

No fix required before merge.
