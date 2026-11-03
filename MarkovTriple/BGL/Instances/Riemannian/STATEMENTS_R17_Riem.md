# Round 17 (stream F): Riemannian items: converse of (1.16.8), relaxed completeness, hyperbolic plane (target statements)

Written BEFORE any proof (Armstrong step (a)); changed only by a logged erratum (`ERRATA.md`, prefix `R17-`).
Source: BGL Sect. 1.16 ((1.16.4), (1.16.5), (1.16.8) and the discussion around it: `Gamma_2 >= rho Gamma` for all `f`
iff `Ric_g + Hess W >= rho g`), App. C.3, Def. 3.3.9 (completeness), Sect. 1.11.3.  Setting: `R : RiemData d` of
`Riemannian/Data.lean`; `R.beRicci = ricci + hess W`, `R.gl = (g^{ij})^{-1}`, `R.Curv rho` = Def. 3.3.14 (`n = infty`) on all `C^infty f`.

## (i) The converse of (1.16.8)  (file `Riemannian/BochnerConverse.lean`)

BGL proof: given `x` and a covector, choose `f` with prescribed gradient at `x` and vanishing Hessian at `x`
(in the book: normal coordinates; here `f(y) = c.(y - x) + 1/2 gamma_{ij}^k(x) c_k (y-x)^i (y-x)^j`), apply Bochner (1.16.4) at `x`.
Hypothesis needed: NONE beyond `Curv rho` on `C^infty` test functions (quadratic polynomials are `C^infty`, so no
"richness" hypothesis is required: `Curv rho` is stated for all `C^infty f`, not for `C_c^infty` only).

* `RiemData.hessZeroPoly (R) (x) (c : Rd d) : Rd d -> R`: a quadratic polynomial `f` with `Sm f`,
  `pderiv f k x = c k` and `R.hess f i j x = 0` for all `i j`.
* `RiemData.riem_ricci_of_curv {rho} (h : R.Curv rho) : forall x xi : Rd d,
     rho * sum_ij gl_ij(x) xi_i xi_j <= sum_ij beRicci_ij(x) xi_i xi_j`   (the converse; `Curv rho => Ric_g + Hess W >= rho g`)
* `RiemData.riem_curv_iff_ricci {rho} : R.Curv rho <-> (forall x xi, rho * sum gl xi xi <= sum beRicci xi xi)`   ((1.16.8), both directions)

## (ii) Removing the bounded co-metric (files `GibbsRd/Ell.lean`, `GibbsRd/EllDiff.lean`, `GibbsRd/EllipticE2E.lean`, `Riemannian/Data.lean`)

`EllData.a_bdd` / `RiemData.g_bdd` (global upper bound of the co-metric) is used only (1) to build the completeness
cut-offs `Gamma(zeta_k) -> 0` (Def. 3.3.9) and (2) as a local bound on compact sets (automatic by continuity).
Minimal replacement (the standard completeness criterion: a proper function with bounded gradient, i.e. a smoothed Riemannian distance):

* field `EllData.a_exh` / `RiemData.g_exh : exists psi : Rd d -> R, Sm psi /\ (forall x, 0 <= psi x) /\
     (forall c, Bornology.IsBounded {x | psi x <= c}) /\ (forall x, sum_ij a_ij(x) d_i psi(x) d_j psi(x) <= 1)`
* `EllData.diff_isComplete` re-proved from `a_exh` (cut-offs `s(2 - psi/R)`), statement unchanged;
* `EllData.exh_of_bdd`: the old hypothesis implies the new one, so Gibbs, `diagRiem`, `confRiem`, `ofGibbs` are re-instantiated
  with unchanged meaning.

## (iii) Hyperbolic plane (file `Riemannian/HypExample.lean`)

Global chart `R^2 -> H^2`, `(x,t) |-> (x, e^t)` of the half-plane model: metric `e^{-2t} dx^2 + dt^2`, co-metric
`g^{11} = e^{2t}`, `g^{22} = 1` (UNBOUNDED, non-conformal, curvature `K = -1`).  `u = cosh t + x^2 e^{-t}/2 = cosh d((x,t),(0,0))`.
Weight `W = 2u`.  Then `w_g = e^{-t}`, integrable `e^{-2u - t}`.

* `hypRiem : RiemData 2` (all fields proved; `g_exh` with `psi = log(1+u)`);
* `hypRiem.ricci_eq : ricci i j x = - gl i j x` (Ric = -g, from the coordinate Riemann tensor);
* `hypRiem.hess_W : hess W i j x = 2 u(x) gl i j x`;
* `hypRiem.curv : hypRiem.Curv 1` (via `riem_curv_of_ricci`) and `hypRiem_not_curv_gt : 1 < rho -> not (hypRiem.Curv rho)` (via the converse (i));
* unconditional Poincare `PI 1`, spectral gap 1, `CD(1,infty)` of the Full triple, log-Sobolev `LS(1,0)` (machinery of `Riemannian/Unconditional.lean`).

## Out of scope / not attempted
Multi-chart (atlas) manifolds and compact manifolds (spheres): BGL's coordinate approach used here needs a single global chart `R^d`;
the round sphere in stereographic coordinates is a chart of `S^d` minus a point, a bounded-above metric is false there and the
exhaustion field `g_exh` fails for it (finite distance to the missing pole), so it is not a `RiemData`.
