# AUDIT R17 "Noncompact": hostile self-audit (finite-`n` curvature-dimension on a non-compact state space)

Files: `MarkovTriple/BGL/Instances/SphereOpen/{Basic,LpTransport,Triple,Semi,Full,Support,Main,AxiomCheck}.lean`;
statements fixed beforehand in `Instances/SphereOpen/STATEMENTS_R17_Noncompact.md` (registered `proposed` in `frozen-manifest.json`).
No frozen/fenced file, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` was modified.

## 1. What was asked and what exists
Goal: a non-compact instance of `CD(ρ,n)`, `ρ>0`, `n<∞`, finite measure, feeding `FullTriple.logSobolev_dim_unconditional` (BGL Thm 5.7.4).

Analysis of the candidates (mathematics, not formalized; the book was not available in the sandbox, so no book numbering was checked):
* `ρ>0`, `n<∞` forces (Bonnet-Myers) a bounded intrinsic distance `d_Γ`.  Hence every weighted chart of the library that is complete
  for `d_Γ` (`EllData`/`RiemData`/`GibbsRdData`: co-metric bounded above) is excluded: complete + bounded diameter = compact.
* Laguerre `L = x f'' + (a-x) f'` (`d_Γ = 2√x`, unbounded): `n = ∞` only; Hermite/OU: `n = ∞`; Cauchy/Student-type `V = c log(1+x²)`:
  the Riccati condition `V'' ≥ ρ + V'²/(n-1)` fails for `ρ>0` at infinity, so only `ρ ≤ 0`.
* The only examples with `ρ>0`, `n<∞` are Jacobi/Gegenbauer on `(-1,1)` (spheres `Sⁿ`, `CD(n-1,n)`).
Therefore the maximal target is the Gegenbauer (zonal `S³`) triple on the OPEN interval `(-1,1)`.

## 2. What was built
`ZonO = {x ∈ [-1,1] | -1<x<1}` (non-compact, `not_compactSpace_ZonO`), `μO = μZ.comap val` (probability; the two poles are null),
`oT : DiffusionTriple ZonO`, `oFull : FullTriple ZonO` with `𝒜 = {f∘val | f ∈ 𝒜_Z}` (functions smooth up to the endpoints), `L(f∘val) = (L_Z f)∘val`,
`Γ(f∘val, g∘val) = (Γ_Z f g)∘val`.  F8/F10/S10/S11 come from the intertwining `R_O ∘ restr = restr ∘ R_Z`, `P^O_t ∘ restr = restr ∘ P^Z_t`
(`Semi.lean`), proved by continuity and density of `span{e_k}` (the images of the Chebyshev eigenfunctions are eigenfunctions of `oT`,
`DiffusionTriple.R_cls_eigen`, `semigroup_cls_eigen`).  `oFull_CD : CD 2 3` is the existing BGL `Γ₂(f) = F''²+2(F'/sinθ)²` computation
(`Sphere/Curvature.lean`) pulled back pointwise a.e. (`Γ₂_O`).  `oFull_LS : LS (1/3) 0` and `oFull_finiteDimInterpolation` follow from
`FullTriple.logSobolev_dim_unconditional` / `finiteDimInterpolation_of_CD` (`ρ=2`, `n=3`, `(n-1)/(ρn) = 1/3 < 1/2`).

## 3. Hostile checks
* **Faithful statement.** `oFull.CD 2 3` is the frozen `FullTriple.CD`, quantifying over ALL `f ∈ oFull.A` (not only a sub-family).
  `oFull_LS` is the frozen `DiffusionTriple.LS` (`IsProbabilityMeasure`, `0<C`, `0 ≤ D`, test class `𝒜₀`).  Hypotheses of the general theorem
  (`IsProbabilityMeasure oFull.μ`, `0<ρ`, `1<n`, `n ≠ ⊤`, `CD`) are all discharged, none assumed.
* **No vacuous hypotheses.** Every field of `FullTriple` is a theorem here (no `sorry`, no axiom).  `ContDiff ℝ ⊤`: all smoothness
  hypotheses in the code use `(⊤ : ℕ∞)` coerced (the frozen convention; `Sm`), never analytic `ω`.  The extension `liftO` is unique
  (`eq_of_comp_eq`), so `L`, `Γ` are not junk values on `𝒜₀`.
* **Not degenerate.** `μO` is a probability measure (`inferInstance`), `oFull_μ_pos_of_open` (every non-empty open set has positive measure),
  `oFull_Γ_ne_zero` (`Γ(x) = 1-x² > 0` on all of `(-1,1)`, not a.e. zero), `CD 2 3` is the equality case (the sphere), `n=3` finite so the
  `(Lf)²/n` term is active.
* **Axioms.** `#print axioms` of `oFull`, `oFull_CD`, `oFull_finiteDimInterpolation`, `oFull_LS`, `oFull_Γ_ne_zero`, `oFull_μ_pos_of_open`,
  `RO_restrC`, `PO_restrC`, `restrL_surjective`, `not_compactSpace_ZonO`: only `propext`, `Classical.choice`, `Quot.sound`.
* **Warnings.** 0 warnings, 0 errors in the files added; no `set_option`.

## 4. Limits (no overclaiming)
1. **The instance is the compact zonal `S³` triple restricted to a dense conull open subset.**  `L²(μO) ≅ L²(μZ)` unitarily, the Friedrichs semigroup
   is the transported one, and `𝒜` contains the functions smooth up to the poles.  Consequently `oFull.A = oFull.A₀` also holds (so `oFull` is
   a "Compact Markov Triple" in the frozen, algebraic sense of BGL Def. 3.3.26); only the TOPOLOGICAL state space is non-compact.  The new
   theorems therefore exercise the finite-`n` log-Sobolev theorem on a non-compact space, but no analytic difficulty specific to non-compactness
   (ESA of `C_c^∞(-1,1)`, which holds only for dimension parameter `n ≥ 4`, boundary behaviour, regularity) is treated.
2. **A state space complete for `d_Γ` cannot occur** (Bonnet-Myers; mathematical remark, not formalized).  A formal proof of that obstruction is NOT given.
3. Only `n = 3`, `ρ = 2`.  Other Gegenbauer parameters (`n ≥ 4`, non-integer), unequal Jacobi parameters, and the genuinely different algebra
   `C_c^∞(-1,1)` are not built.  A second instance was not built for that reason.
4. The book (BGL) PDF was not available; examples were identified from the repository's own citations (Sect. 5.7 p. 272: Thm 5.7.4 for `Sⁿ`)
   and direct computation, not checked against the book text.

## 5. Verdict
No soundness defect or vacuity found.  The open item "no non-compact CD(ρ,n), n finite, instance" is closed only in the topological sense of limit 1.
