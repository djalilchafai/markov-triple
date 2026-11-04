# AUDIT R22 E1 (hostile): bounded open sets of R, non-complete / non-ESA; R20 leftovers

Base main b44dbee + implementation bacc858 merged. Verdict: **ACCEPT**. No HIGH, no MEDIUM, 2 LOW (docs).

## Verified
* Build: the 8 new modules were each recompiled with `lake env lean` (Basic, Dense, Diffusion, NotComplete, NotESA, Ioo,
  DirectEllConst, DirectSpiky): zero output (0 errors, 0 warnings). `AxiomCheckR22E1` builds; `#print axioms` rerun on all 19
  targets: only propext, Classical.choice, Quot.sound. grep for sorry/set_option/axiom/admit/native_decide: only the `#print axioms` lines.
* Frozen: `scripts/check_frozen.py` prints OK. Diff vs main touches only IntervalGen/* and frozen-manifest.json (one added `proposed`
  entry, the implementer's STATEMENTS file). No fenced file, lakefile, manifest, toolchain, ERRATA or GAPS edited.
* Non-connected Omega. `A₀_dense`: no connectedness used. K n = {dist(.,Omega^c) >= 1/(n+1)} is closed and inside Omega; smooth
  Urysohn cut-offs theta_n are 1 on K n with tsupport in K(n+1) inside Omega; mu(Omega \ K n) -> 0 by continuity from above (the
  intersection is empty because Omega is open, `pos_dist`). Valid for infinitely many components and fat-Cantor complements.
  `exp_orth`: IBP is done on all of R against compactly supported f (`Lebesgue.ibp_cs`); f, f'' vanish off Omega, so the mu-integral
  equals the R-integral up to the normalising constant (`integral_μ`); there are no boundary terms for any bounded open Omega.
  `not_complete`: `abs_deriv_le` gives |zeta'| <= c on ALL of R (on Omega by continuity of zeta' plus the open set {c^2 < zeta'^2}
  having positive Lebesgue measure; off Omega because deriv zeta is in A₀ so vanishes there). Hence zeta is c-Lipschitz on R
  (MVT on convex univ) and zeta(y) = 0 for y not in Omega, so |zeta(x)| <= c|x-y| for every x. No reachability of y from x inside
  Omega is needed, the segment lives in R. The a.e. point x with zeta_k(x) -> 1 exists because mu is a probability measure. Correct;
  only Omega^c nonempty and mu != 0 are used.
* No inconsistency: `Ω.diff` is a fully constructed `DiffusionTriple` (every field proved). The argument cannot specialise to R
  (Omega^c empty there; boundedness is used for `compl_nonempty` and finite mu), so the library's `diff_isComplete` for R is not
  contradicted. `IsComplete` is the verbatim Frozen/Complete.lean definition.
* `not_esaProp`: unfolds the actual `DiffusionTriple.ESAProp`; uses `generator_R` (G(Ru) = Ru - u) and the limit
  <u, L a - a> -> <u, G(Ru) - Ru> = -||u||^2 against exp_orth = 0 for all a. Sound. `no_fullTriple` follows via `T.esaProp`.
* `ΓA_eq`, `Γ₂_eq` by explicit derivative computation; `diff_CD` via nlinarith with explicit hints for rho <= 0, 1 <= n (n = infinity
  gives inverse 0). `GenCD` is honestly named, not `FullTriple.CD`.
* `BddOpen.Ioo_zero_one_μ : (Ioo 0 1).μ = Interval.ivμ` is proved, consistent with R21.
* Part (c): `ell_const_mem_domain_direct` genuinely applies `E.ell_mem_domain_of_Γ₂_direct hρ hfS hf2 hG hG2` after discharging
  integrability of Γ and Γ₂ (both 0 via `pderiv_const`); `L 1 = 0` is a separate lemma (`fullU_L_const_fn`), not used to bypass the
  theorem. `spikyData_const_mem_domain` and `spikyData_sin_mem_domain` go through `spikyData_mem_domain_of_Γ₂`; the sin
  computations (Gr = cos^2 x0, second-order form = sin^2 x0 + spk(x0) cos^2 x0) are proved and bounded by 1 and 4. The Status
  honestly calls these weak non-vacuity checks (bounded f, trivial conclusion for f = 1). DIFFERENCE FROM BGL sections present.

## Findings
* LOW-1 (doc): proposed ERRATA R22-E1-1 says "GAPS R21 'I5 open' can be removed". The "I5 ... OPEN, not done" text is in
  `Instances/Interval/STATEMENTS_R21_Interval.md` lines 102-106, not in GAPS.md; `Theory/GAPS.md` line 285 lists only the R21 proved
  items and has no I5-open entry. Better wording: "R21 STATEMENTS I5 (stretch) is now done; cite IntervalGen in GAPS". The
  mathematical claim (I5 closed, for arbitrary bounded open Omega, not just finite unions of intervals) is accurate. Not edited
  (file owned by others).
* LOW-2 (doc): STATEMENTS G3 says the argument is a "weaker form" of |zeta(x)| <= dist(x, boundary) sup|zeta'|. It is in fact the
  global c-Lipschitz bound plus zeta(y)=0; no action needed, wording only.
* Observation (not a defect): R21 `ivDiff` and `(Ioo 0 1).diff` agree in mu, A₀, L, Γ but differ in the exhaustion field; Status states
  this. ERRATA R22-E1-2 and R22-E1-3 are accurate; R22-E1-1 accurate modulo LOW-1.
