# AUDIT R23-G1 (hostile): F10 for zonal Gegenbauer goDiff (lambda = 3/2)

Branch ad7e99d merged on main dc4119a, then G2 (2307284) merged for the probe (only conflict: frozen-manifest.json, resolved keeping both `proposed` entries, valid JSON).

## Verdict: ACCEPT. No HIGH, no MEDIUM findings. 1 LOW (doc).

## Verified
1. `ESAProp` (Theory/ESAOne.lean:25-28) is verbatim the `esa` field of FullTriple (Frozen/FullTriple.lean:71-74), modulo unfolding `toStandardTriple.toDiffusionTriple`.
   `esaProp_of_orth` (ESA/Main.lean:27-58) is sound: it uses `R_cls_sub` (R(cls a - Lcls a) = cls a, i.e. symmetry/positivity of L on A0 through the
   Friedrichs resolvent), the generator characterisation `generator_apply_eq_iff`, and continuity of R. Argument: g = u - Lu; density of (1-L)A0 gives
   m_n = (1-L)a_n -> g; cls a_n = R m_n -> R g = u; Lcls a_n = cls a_n - m_n -> u - g = Lu. Nothing assumed beyond the hypothesis; not circular.
   Not trivially strong: its hypothesis ("(1-L)A0)^perp = 0") is exactly the classical criterion. Sign convention irrelevant: <(1-L)a,w>=0 iff <(L-1)a,w>=0.
   Against the non-ESA triples (IntervalGen/NotESA.lean:78 `not_esaProp`, `Ioo_not_esaProp`; Interval `iv_not_esaProp`): there exp is a nonzero element
   orthogonal to (L-1)A0, so the orth hypothesis is FALSE there and the lemma does not apply; no conflict.
2. Math by hand (all confirmed). W Lf = (W^2 f')' for Lf = W f'' - 4x f' (goL, Diffusion.lean:21-22; lemma at line ~58). Weak equation
   int u W (f - Lf) = 0 gives (W^2 v')' = W v, so F = W^2 v', F' = W v (Weyl.lean hypotheses hv, hF). Y = Fv, Y' = W v^2 + F^2/p >= 0 (`Y_mono`).
   If Y(t0) > 0 then F keeps sign, |F| >= f0, p <= 4(1-x)^2 on (0,1) (Weyl.lean hp, uses (1+x)^2<=4), v' >= f0/(4(1-x)^2), v >= c/(1-x) near 1 (phi monotone trick),
   W v^2 >= (1-x) v^2 >= c^2/(1-x) not integrable (`not_integrableOn_div_one_sub`). Negative F handled by (v,F) -> (-v,-F). Y<=0 on (0,1); reflection
   (v(-x), -F(-x)) gives Y>=0 on (-1,0); monotonicity of Y propagates to all (-1,1); Y=0 => Y'=0 => W v^2 + F^2/p = 0 => v=0. Both endpoints are handled.
   lambda = 3/2 is genuinely used: general lambda has p = W^(lambda+1/2), weight W^(lambda-1/2); singular solution v ~ (1-x)^(1/2-lambda), and
   W^(lambda-1/2) v^2 ~ (1-x)^(-(lambda-1/2)) is non-integrable iff lambda >= 3/2. Here p=W^2, weight W^1 (exponents 2 and 1) give exactly (1-x)^(-1). For lambda<3/2
   the integrand is integrable and the argument breaks at the non-integrability step (and ESA is false there). The two places where lambda enters are the bound
   p <= 4(1-x)^2 (needs exponent >= 2) and the divergence of int dx/(1-x) (needs weight exponent 1 + v^2 exponent -2).
3. `#print axioms` (run myself): weyl_end, weyl, weak_regular, esaProp_of_orth, go_orth_zero, go_esaProp all [propext, Classical.choice, Quot.sound].
   grep: no sorry / set_option / axiom / native_decide in ESA/*.lean. Build of ESA modules: 0 warnings. `scripts/check_frozen.py`: OK on merged tree.
   Diff vs main: only the 5 new .lean files + STATEMENTS_R23_G1.md + one `proposed` manifest entry; no fenced file, lakefile/manifest/toolchain untouched.
4. Composition probe (scratch, not committed), with G1+G2 merged:
   `noncomputable example : FullTriple R := goFull go_esaProp` OK;
   `example : (goFull go_esaProp).CD 3 4 := goFull_CD go_esaProp` OK;
   `example : not (goFull go_esaProp).toDiffusionTriple.IsComplete := goFull_not_complete go_esaProp` OK.
   (Plain `example : FullTriple R := ...` errors only with "depends on noncomputable goFull": needs the `noncomputable` keyword, a probe artefact, not a defect.)
   `#print axioms` on the FullTriple def, CD and not-complete theorems: [propext, Classical.choice, Quot.sound] each. G2's own AxiomCheck (goFull, goFull_CD, goFull_not_complete) is also clean.

## Findings
- LOW (doc): STATEMENTS_R23_G1.md lists `esaProp_of_orth` in namespace ...GegenbauerOpen.ESA, but it lives in `MarkovTriple.BGL.DiffusionTriple` (Main.lean:23-27). Cosmetic.
- INFO: I did not re-derive Prim.lean/Regularity.lean (du Bois-Reymond, ~520 lines) line by line; their statements (`weak_regular` hypothesis/conclusion, checked against goL and the weak identity) are consistent and Lean-checked with clean axioms, so soundness rests on the kernel.
