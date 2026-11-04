# Hostile audit, Round 19 Stream A4 (Core2 under `PolyHess`, witness `exp(x^2)`), commit 8f142de

Auditor: independent (Armstrong method). Nothing on the audited branch was modified.

## Verdict
No CRITICAL/HIGH/MEDIUM finding. The Lean content is sound, the statements are faithful, and the witness is genuinely non-vacuous and outside `GrowHess`.

## Checks (evidence)
1. Statements. `#check` (default and `pp.explicit`) of `gibbsFull_core2_of_polyHess`, `gibbs_mem_domain_of_Gamma2_polyHess`, `gibbs_mem_domain_of_Gamma2_convex`:
   hypotheses are exactly `PolyHess` (resp. `rho <= V''`, the `o(V'^2)` clause `forall eps>0, exists B>=0, V'' <= eps V'^2 + B`, `|V'''| <= C(1+|V'|^N)`), plus `f in A`, `MemLp f 2`, `Gamma, Gamma_2 in L^1`.
   No Core2 or other hypothesis hidden (no extra instance/arguments). `FullTriple.Core2` printed: unchanged definition (Converse.lean untouched in `git diff main`); `gibbsFull_unconditional` untouched.
   `PolyHess` printed as described. The `_convex` variant derives conjunct 1 with `Cw=|rho|` correctly (`V'' >= rho >= -|rho|(1+|V'|)`).
2. Non-vacuity, by hand and in Lean. `V=e^{x^2}`: `V'=2xE`, `V''=(2+4x^2)E>=2` (E>=1+x^2), `V'''=(12x+8x^3)E` (derivatives verified).
   `V''=o(V'^2)`: for `x^2>=M=max(1,3/(2 eps))`, `eps E>=3/2` so `eps*4x^2E^2 >= 6x^2E >= (2+4x^2)E`; else bounded by `(2+4M)e^M`. Correct.
   `|V'''|<=60(1+V'^2)`: `|x|>=1`: `<=20|x|^3E <= 20x^2E^2 <= 5V'^2`; `|x|<1`: `<=20*3=60`. Correct (constant 60 suffices, even smaller).
   Integrable `e^{-V}`: `e^{-e^{x^2}} <= e^{-x^2/2}`; genuine `GibbsData` with finite mass (`Z>0` generic lemma).
   `expGibbs_not_growHess`: real proof, at `x=|C|+2`: `V''>=4x^2E` vs `C(1+V')<=3|C|xE`, contradiction since `4x>3|C|`. `expGibbs_core2`, `expGibbs_mem_domain_of_Gamma2` instantiate the main theorems (rho=2), checked by `#check`.
   `PolyHess` and `V''>=2` are jointly satisfied, so the converse theorem is not vacuous. `GibbsData.smooth` is `Sm` (C-infinity), no analyticity smuggled.
3. Axioms: `lake build AxiomCheckR19Core2`: all 16 listed theorems depend only on `propext, Classical.choice, Quot.sound`. grep: no `sorry`, `set_option`, `axiom`, `native_decide`, `admit` in the new files. `lake env lean` on each of the four Core2Poly files: no output (0 warnings, 0 errors).
4. Proofs.
   `hardy_ibp_w`: `P=eta^2 V' psi^2 f^2`, `(P w)'=(P'-V'P)w`, compact support, `ibp_master`; `H` expansion matches by `ring` (signs: `-eta^2V'^2psi^2f^2` from `-V'P`). OK.
   `memLp_of_BE_w`: with `d=V'a+q`, `0=H` gives `t^2 = -eta^2 S -2eta' a t -2t eta q`; uses LOWER bound on S: correct sign. `memLp_of_hardy_w`: `0=H=eta^2S+2eta'at+2t eta d - t^2`, uses UPPER bound `S<=(V'^2/4+B)a^2`: correct (1-1/4-1/4-1/4>0).
   Role of psi: `psi=V'^n`, `V''psi^2+2V'psi psi' = (2n+1)V'' V'^{2n}` (`key_pow`); Hardy step uses `eps=1/(4(2n+1))`, BE step uses `(2n+1)Cw`. Cascade: v-step needs level-n of both v and v' (IH), v'-step needs `V'^n v`, `V'^n a` (compact) and `V'^n v'`: no circularity.
   `memLp_mul_poly`: `|c g|<=C(|g|+|V'^N g|)` dominated in L^2: valid. `cutoff_ZL_p`: coefficient `V'''` handled via `(hpow N).1`, `V''` via `|V''|<=D(1+V'^2)` (`abs_V2_le`, uses conjuncts 1,2 with eps=1) and `(hpow 2/3)`, `V'V''` via `hpow 3`. Third conjunct used only there. Correct.
   No assumption smuggled in a structure field (`GibbsData` has V, smooth, integrable only).
5. Frozen/process: `scripts/check_frozen.py` OK. `git diff main HEAD --name-only`: only new R19 files, `MarkovTriple.lean` (imports), `ERRATA.md`, `GAPS.md`, `frozen-manifest.json` (one new `proposed` entry). No fenced/frozen file, lakefile, toolchain or manifest touched.

## Findings (all LOW/INFO)
- LOW-1 (doc wording). `STATEMENTS_R19_Core2.md`, `AUDIT_R19_CORE2.md`: "`Core2` <=> essential self-adjointness of `L^2` on `C_c^infty`" is stated as an equivalence but only the direction used earlier (`core2_of_dense`, graph-norm density) exists in Lean; the equivalence (and "m_+-=2 limit-point count") is informal. Not used by any theorem; suggest "essentially equivalent (informally)".
- LOW-2 (doc). "e.s.a. of `L` on `C_c^infty` holds for every V (Gaffney/BGL 3.2.1)" is correct (complete weighted line, intrinsic distance Euclidean, smooth positive density), cited in GAPS/AUDIT, but not formalised in this repo; the STATEMENTS file states it without a citation. Fine, but label it "known, not formalised".
- LOW-3 (doc). The "spiky `V'''`" paragraph IS labelled heuristic in AUDIT ("heuristic, not formalised") and as "obstruction of the cut-off proof, NOT a proof Core2 fails" in STATEMENTS. Honest. Minor: that a spiky example keeps `V''>=rho` yet violates conjunct 3 is correct; whether `V'''v` truly fails to be in L^2 is unverified, as admitted.
- INFO-1 (process). Statements file hash in the manifest was refreshed after appending the Status section (ERRATA R19-3 says so); entry remains `proposed`; the targets text is unchanged by that append per diff of Status only (not independently verifiable from history since file was added in one commit).
- INFO-2. No overclaim of Core2 for general V found: all docs (ERRATA R19-1/2, GAPS, AUDIT, STATEMENTS "Not claimed") limit to `PolyHess` and list `R^d`, EllData, RiemData, non-polynomial `V'''`, `V''` not `o(V'^2)` as open. Note `PolyHess` excludes e.g. `V=e^{e^{x^2}}`-type? (V''/V'^2 -> 0 fails only if V'' ~ V'^2; for exp(exp x^2)-like, V'' ~ V'^2/... still o(V'^2)? requires check; not claimed.) The classification of what lies outside is thus only partially explored, but nothing is overclaimed.
- INFO-3. `PolyHess` conj. 3 with exponent `N` arbitrary and conj 2 together are not implied by `V''>=rho`; the `_convex` theorem correctly states them as separate hypotheses.

## Hygiene
`.lake/build` copied, `.lake/packages` symlinked; `lake build --no-build` showed only new modules out of date (Mathlib not rebuilt). Probes were throwaway (removed). No lake/lean processes left.
