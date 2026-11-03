# STATEMENTS R17 "Noncompact" (Armstrong method): finite-dimensional CD(rho,n) on a topologically non-compact space (COSMETIC instance: zonal S^3 minus its poles; see ERRATA R17-M2)

Written BEFORE any proof.  Namespace `MarkovTriple.BGL.Instances.SphereOpen`, files `MarkovTriple/BGL/Instances/SphereOpen/*.lean`.
Do not weaken while proving; deviations go to the "Status" section and to `ERRATA.md` (prefix `R17-`).

## 0. Which BGL examples can feed Thm 5.7.4 (analysis, no Lean)

Thm 5.7.4 needs `rho > 0`, `1 < n < infty`, finite measure.  By the Bonnet-Myers diameter bound (classical; `CD(rho,n)`, `rho>0`, `n<infty` forces intrinsic diameter
`<= pi sqrt((n-1)/rho)`; stated here as mathematical context only, NOT formalized, and the numbering in the book was not checked: no copy of
BGL was available in the sandbox) the intrinsic metric `d_Gamma` is BOUNDED.  Therefore:
* a state space that is COMPLETE for `d_Gamma` is compact (Hopf-Rinow type); every complete weighted chart of the library
  (`EllData`, `RiemData`, `GibbsRdData`: co-metric bounded above, i.e. metric bounded below by Euclid, hence complete and of
  infinite diameter) is therefore EXCLUDED: for it `CD(rho,n)` with `rho > 0`, `n < infty` is impossible;
* Laguerre `L = x f'' + (a-x) f'` on `(0,infty)`: `d_Gamma = 2 sqrt x` unbounded, only `n = infty`; Hermite/OU: `n = infty`;
  Cauchy/Student-type `V = c log(1+x^2)`: curvature `rho <= 0` (the Riccati condition `V'' >= rho + V'^2/(n-1)` fails at infinity for `rho > 0`);
* [CORRECTED, ERRATA R17-M3: the original text said these were the ONLY BGL examples; that is false -- compact weighted manifolds (`S^n`, `SO(n)`, `CP^n`), other Jacobi parameters and simplex diffusions also qualify; and Bonnet-Myers bounds `d_Gamma` but does not by itself force a compact state space.]  The BGL examples with `rho > 0`, `n < infty` considered here are the Jacobi/Gegenbauer family on the interval `(-1,1)` (sphere `S^n`,
  `CD(n-1,n)`; Sect. 2.7 / Sect. 5.7 p. 272 "Theorem 5.7.4 applies to `S^n`").  Their state space is the open interval, not complete
  for `d_Gamma` (bounded), with finite measure.

Consequently the maximal honest target is: the Gegenbauer (zonal `S^3`) triple on the OPEN interval `(-1,1)` (a non-compact
topological space; the sphere with its two poles removed), with the algebra `A` of functions smooth up to the endpoints.

## 1. Statements

Notation: `Zon = [-1,1]`, `sCompact`/`sFull`/`sT`: existing zonal `S^3` triple (`Instances/Sphere`), `mu_Z` its probability measure
`(2/pi) sqrt(1-x^2) dx`, `A_Z` its algebra `{f | theta -> f(cos theta) is C^infty}`; `CD(2,3)` = `sphere_CD_two_three`.

N1 `ZonOSet : Set Zon := {x | -1 < x.1 ∧ x.1 < 1}`, `abbrev ZonO := ↥ZonOSet`; `theorem not_compactSpace_ZonO : ¬ CompactSpace ZonO`
   (the state space is genuinely non-compact).  `mu_O : Measure ZonO := mu_Z.comap Subtype.val`;
   `instance : IsProbabilityMeasure mu_O` (the two poles are `mu_Z`-null).
N2 (Lp transport) for `1 <= p < infty`: `restrLp` : `Lp R p mu_Z ≃ₗᵢ[R] Lp R p mu_O` (restriction `u ↦ u ∘ Subtype.val`), with
   `restrLp (cls f) = cls (f ∘ val)` for `f ∈ A_Z`.
N3 (the Diffusion triple) `oT : DiffusionTriple ZonO` with `mu = mu_O`, `A₀ = {f ∘ val | f ∈ A_Z}` (non-unital), `L (f ∘ val) = (L_Z f) ∘ val`,
   `Gamma (f ∘ val)(g ∘ val) = (Gamma_Z f g) ∘ val`  (`L_Z f = (1-x^2) f'' - 3 x f'`, `Gamma_Z f g = (1-x^2) f' g'`; the lift is unique because
   `ZonOSet` is dense in `Zon` and elements of `A_Z` are continuous).
N4 (semigroup transport) `restrLp (P_t u) = P'_t (restrLp u)` for the Friedrichs semigroups of `sT` and `oT`; same for the resolvent `R`.
N5 (the Full triple) `oFull : FullTriple ZonO` (`A = {f ∘ val | f ∈ A_Z}`, F1-F10 all PROVED, not assumed; F8, F9, F10, S10, S11 via N4),
   and `oCompact`-like statement `∀ f, f ∈ oFull.A ↔ f ∈ oFull.A₀` is NOT claimed (topological non-compactness is the point; `A = A₀` still holds
   but is not needed).
N6 `theorem oFull_CD : oFull.CD 2 3`  (finite `n = 3`, `rho = 2`; BGL's `CD(n-1,n)` Gamma_2 computation: `Gamma_2(f) = F''^2 + 2 (F'/sin theta)^2`).
N7 `theorem oFull_finiteDimInterpolation : oFull.FiniteDimInterpolation (2 * (3/(3-1)))` (via `FullTriple.finiteDimInterpolation_of_CD`).
N8 `theorem oFull_LS : oFull.toDiffusionTriple.LS (1/3) 0` (BGL Thm 5.7.4, `C = (n-1)/(rho n) = 1/3`, via `FullTriple.logSobolev_dim_unconditional`),
   strictly better than `1/rho = 1/2`.
N9 (non-degeneracy) `∃ f ∈ oFull.A₀, ¬ (oFull.Γ f f =ᵐ[oFull.μ] 0)`, and `oFull.μ` is a probability measure with full support-type
   property `∀ U open nonempty in ZonO, 0 < mu_O U` (so the measure does not live on a smaller set).

Not claimed: any instance with a state space complete for `d_Gamma`; the Jacobi family with unequal parameters; any `n ≠ 3`.

## Status (written after the proofs; no statement N1-N9 was weakened)
PROVED, 0 sorry, axioms `propext, Classical.choice, Quot.sound` (`SphereOpen/AxiomCheck.lean`):
N1 `ZonO`, `not_compactSpace_ZonO`, `μO`, `IsProbabilityMeasure μO` (`Basic.lean`; `μZ_compl`: the poles are null).
N2 `restrL p` (linear, norm preserving, surjective, every `p`; `restrC` for `p = 2`) (`LpTransport.lean`, `Semi.lean`).
N3 `oT : DiffusionTriple ZonO` (`Triple.lean`).
N4 `RO_restrC`, `PO_restrC` (`Semi.lean`): by density of `span {e_k}` and `DiffusionTriple.R_cls_eigen` / `semigroup_cls_eigen`.
N5 `oFull : FullTriple ZonO` (`Full.lean`; F8 `semigroup_cls_mem_O`, F10 `core_of_invariant`, S10 `open_ergodic`, S11 `semigroup_one_O`).
N6 `oFull_CD : oFull.CD 2 3`; N7 `oFull_finiteDimInterpolation`; N8 `oFull_LS : LS (1/3) 0` (`Main.lean`).
N9 `oFull_Γ_ne_zero` (witness `f(x)=x`, `Γ f = 1-x²>0`), `oFull_μ_pos_of_open` (full support, `Support.lean`).
Remark (honesty): `oFull.A = oFull.A₀` holds, so `oFull` is also a "Compact Markov Triple" in the frozen sense `𝒜 = 𝒜₀` (BGL Def. 3.3.26);
what is non-compact is the TOPOLOGICAL state space `(-1,1)`.  The triple is the restriction of the compact zonal `S³` triple to a dense conull
open subset; it contains no new analysis (no ESA of `C_c^∞(-1,1)`, no new regularity theory).  See `BGL/AUDIT_R17_NONCOMPACT.md`.
