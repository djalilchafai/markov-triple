# Hostile audit R29 Stream N (round sphere S^{n-1}: Fischer, density, F10/S10/S11, conditional FullTriple)

Verdict: **ACCEPT** (no content defects; only low/info doc observations).
Merged `worktree-agent-a1cb62c7519a91d8c` (6676ca8 freeze, bc69dfb proofs; base f0edf3a). Full `lake build`: 9540 jobs, success,
0 warnings in the whole log; the six new modules (Fischer, Harm, Density, Spectral, Full, AxiomCheckR29N) were compiled in this run
(not cached). No `sorry`, `set_option`, `native_decide`, or `axiom` in `Instances/SphereN/Full/`.

`#print axioms` (own run, from the build log): `fischer`, `dense_span_harm`, `sphere_esa`, `sphere_ergodic`, `sphere_semigroup_one`,
`sphereStandard`, `sphere_semigroup_poly_mem`, `sphereFull`, `sphereFull_CD`, `sphereFull_core2`: all `[propext, Classical.choice, Quot.sound]`
(`sphereFull*` take `h8` as an explicit argument, so no hidden axiom).

## (a) F10 / `core_of_dense_range` / `sphere_esa`: CORRECT
The library's F10 (`FullTriple.esa`) is the "core" form: every `u in D(L-bar)` (L-bar = Friedrichs generator `T.generator`) is an
L2-limit of `cls a_m`, `a_m in A0`, with `Lcls a_m -> generator u`. The generic lemma proves exactly this. Checked line by line:
`g := u - Gu`; pick `m_n = (1-L)a_n -> g` (density of the range); `a_n = R m_n` by `R_cls_sub` (`R(1-L)a = a` on A0, which encodes the
symmetry/IBP of L on A0 inside the library's form data, a theorem for every DiffusionTriple); `R` continuous and `R g = u`
(`generator_apply_eq_iff`); hence `cls a_n -> u` and `Lcls a_n = cls a_n - m_n -> u - g = Gu`. This is the standard "symmetric + ran(1-L) dense
=> essentially self-adjoint / core" argument run directly with the Friedrichs resolvent. No invariance of A0 under `P_t` is needed (that is the
other route, `core_of_invariant`). Range density is shown in `sphere_esa` from eigenvectors: `(1-L)(1+lam_k)^{-1} h = h` and `dense_span_harm`.

## (b) S10 / S11: CORRECT, in the library's form
* `StandardTriple.ergodic` is stated for all `u in D(generator)` (Friedrichs domain, not A0) with `generator u = 0`; `sphere_ergodic` has exactly
  this signature. Passage to the closure domain: `Gu = 0 => R u = u`; `R` self-adjoint; for an eigenvector `e` of `R` with eigenvalue
  `(1+c)^{-1} < 1` (`c = lam_k > 0`), `<e,u> = <Re,u> = (1+c)^{-1}<e,u>` forces `<e,u> = 0` (likewise `<e,1> = 0`); degree 0 handled by
  `w = u - ubar*1`. Then `w` is orthogonal to a dense span, so `w = 0`. No eigen-expansion of `u` is needed, only density.
* `StandardTriple.conservative` is the exhaustion form. `sphere_semigroup_one` proves `P_t[1] = [1]` and `sphereStandard` feeds it to the generic
  `conservative_of_semigroup_one` (Mass.lean), the same bridge used for finite-measure instances; sigma is a probability measure for n >= 1.

## (c) `sphereFull` and `SphereF8`: honest conditional
* `SphereF8 n hn` is a `def ... : Prop` (not an axiom): `forall t f, exists g in A0S n, (P_t [f]) =ae g`. It is plugged in verbatim
  (`semigroup_A := h8`), so it is literally the library's F8 with `A = A0 = C^inf(S^{n-1})`: not weaker, not trivial.
* Satisfiable (by hand): L is the Laplace-Beltrami operator, `P_t` its heat semigroup on a compact smooth manifold; for `f in C^inf`,
  `||proj_k f||_{C^m} = O(k^{-N})` for all N (Sobolev + iterated L), so `P_t f = sum e^{-lam_k t} proj_k f in C^inf` (and `P_0 f = f`). So `h8` is true,
  not contradictory.
* Every other field is proved, none conditional on h8: F1, F2 (`pos_detect_S`, smoothTransition trick), F3 (`A0S_comp`), F4, F5, F6
  (`GammaS_comp_gen`, `LS_comp_gen` for all smooth psi), F7 (`ibp_sphere`, both forms), F9 (via `energy_zero_const`), F10, S10, S11.
  `sphereFull_CD`, `sphereFull_core2` depend on h8 only through the argument. STATEMENTS Status, GAPS R29-N and ERRATA R29-N-2 all say
  "NO unconditional FullTriple" / conditional on `SphereF8`. No doc calls `sphereFull` unconditional.

## (d) Algebra: CORRECT
`lap_rsq_mul`: Delta(r^2 q) = 2n q + 4 x.grad q + r^2 Delta q; with Euler: (2n+4d) q + r^2 Delta q. `lap_rsq_pow_mul_harm`: a_0 = 2n+4k > 0,
a_{j+1} = 2n + 4(2(j+1)+k) + a_j > 0 (needs n > 0, hypothesis present). Fischer: strong induction (d<2 automatically harmonic; else solve
Delta q = Delta p in W_{e+2} using preimages a^{-1}|x|^{2j+2}h of generators; p - q harmonic). Eigenvalue: `LS_extrinsic` gives
L f = Delta F - sum y_i y_j d_ij F - (n-1) sum y_i d_i F; harmonic homogeneous of degree k: 0 - (k^2-k) - (n-1)k = -k(k+n-2).
n=3: k=1 -> -2, k=2 -> -6 (n=2: -k^2). Density: Stone-Weierstrass for the polynomial subalgebra (points separated by coordinates) then
`restr(r^2 q) = restr q` plus Fischer.

## (e) Deviations R29-N-1: no content change (confirmed)
`fischer (hn : 0 < n) : forall d {p}, p.IsHomogeneous d -> p in Wsp n d` with `Wsp` a `def` unfolding to exactly the frozen span; explicit `u hu`
on `sphere_esa`; `sphere_semigroup_one` about `cls <1, one_mem>`; `hn` explicit. Elaboration-level only.

## (f) Git / manifest
6676ca8 touches only `STATEMENTS_R29_N.md` and `frozen-manifest.json`; the manifest diff vs f0edf3a is exactly the one new entry. `scripts/check_frozen.py`: OK.
**LOW/INFO**: the current STATEMENTS file differs from the manifest sha (047ba205...) because the pre-announced "Status (after the proofs)" placeholder was
filled in (diff touches only that section; the statement block is unchanged since 6676ca8). Checker passes (status "proposed"); re-hash when promoting.

## (g) Other findings
* (INFO) `sphere_semigroup_poly_mem` is correctly labelled partial F8 (polynomial restrictions only).
* (LOW, doc, fixed) ERRATA R28-L-4 still read "OPEN" for the whole list although semigroup/ergodicity/Core2(conditional)/F10 now exist; relabelled
  "PARTLY SUPERSEDED by R29-N-1/2" (append only). GAPS (L4) was already annotated "SUPERSEDED in part".
* No SEVERE/HIGH/MEDIUM findings.

## (h) Not-done list: honest
F8 for all f, Poincare/Obata/Lichnerowicz on all of L2, Feller/bridge, comparison with the zonal sphere: all listed as not done. No overclaim found.

## Feasibility of closing F8 (follow-up plan)
Effort: large, est. 1500-3000 lines, 2-3 streams.
1. Spectral route. (i) orthogonality of distinct eigenspaces and `f = sum_k proj_k f` in L2 (symmetry of L + density; ~300 lines); (ii) derivatives of
   harmonic homogeneous polynomials are harmonic homogeneous (algebraic, small); (iii) sup-norm bound for harmonic polynomials, `||h||_inf <= C 2^k ||h||_{L2(S)}`
   by the harmonic mean value property / Cauchy-type estimate on B(0,2) (not in Mathlib; ~500-800 lines) or `C k^{(n-2)/2}` via the zonal kernel (needs rotation
   invariance of sigma); (iv) `||grad_S h||^2 = k(k+n-2)||h||^2` from `ibp_sphere` and `proj_k(L^j f) = (-lam_k)^j proj_k f`, giving `||proj_k f||_{L2} = O(k^{-N})`;
   (v) uniform convergence of the differentiated series, smoothness of the sum, and identification with the a.e. class in `A0S` (A0S is defined through the cutoff
   extension `ext`, which makes the bookkeeping the hardest part).
2. Alternative formulation: replace `A` by a Sobolev-type algebra `{f : sum k^{2m}||proj_k f||^2 < inf for all m}`; then F3/F4/F6 (smooth-composition stability) need
   Moser-type estimates: harder, not recommended.
3. Status quo: keep `SphereF8` as the sole hypothesis (cheap, honest; F10, S10, S11, Core2-given-h8 already proved).
Suggested split: stream N2 = (i),(ii),(iv); stream N3 = (iii),(v).
