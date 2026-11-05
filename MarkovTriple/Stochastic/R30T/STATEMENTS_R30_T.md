# Round 30, Stream T: frozen target statements (regularity for the `R^d` Gibbs / elliptic / Riemannian `FullTriple`s)

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R30T`, file `Stochastic/R30T/Regularity.lean` (+ `AxiomCheckR30T.lean`).
Goal: shrink the three hypotheses (a) `IsFellerC0`, (c) `kappa_s(x,.) << mu` at every `x`, (d) pointwise initial condition of
`gibbsRdFull_bridge_of_feller`, `fullU_bridge_of_feller`, `riemFull_bridge_of_feller` (R29 O).

## Decisions made before proving (honest; no claim beyond what is proved)

* (a) is split into CONTINUITY (provable from the smoothness field `semigroup_A` / F8 of the three `FullTriple`s, with a sup-norm approximation of
  `C_c` by `C_c^infty`; no curvature needed) and DECAY AT INFINITY.  Decay at infinity is NOT claimed: only the exact reduction
  "`IsFellerC0` iff every continuous representative of `P_t f` (f in C_c) tends to 0 at infinity" is stated (G2).
* (d) is attacked through the Bakry-Emery bound `Gamma(P_t f) <= P_t Gamma(f)` (`CD(0,inf)`, i.e. convex `V` for Gibbs) which makes `{P_t f : t <= 1}` locally
  equi-Lipschitz for `f in C_c^infty`; with `P_t f -> f` in `L^2` (strong continuity) this gives pointwise convergence.  It needs `CD(0,inf)`, so it is stated with `Hess V >= 0` (Gibbs)
  and, generically, with the hypotheses `CD 0 inf` and a local ellipticity hypothesis `hell`.  Non-convex `V` (negative curvature) is NOT covered.
* (c) (`kappa_s(x,.) << mu` at EVERY `x`) is NOT a target: it needs Lipschitz smoothing from `L^infty` data (BGL reverse Poincare / local Poincare inequality
  `Gamma(P_t f) <= (1/2t) P_t(f^2)`), which is not in the library and whose interpolation proof needs a new regularity analysis (cf. `Theory/GradientBound.lean`).
  The outcome for (c) is recorded in the Status section (written in the proof commit).

## Statements (`Stochastic/R30T/Regularity.lean`)

Setting: `d : N`, `S : FullTriple (Rd d)` with `[IsFiniteMeasureOnCompacts S.toDiffusionTriple.mu] [S.toDiffusionTriple.mu.IsOpenPosMeasure]`; `ccL2`, `Qop`, `fellerKernelInf`, `IsFellerC0` from `Stochastic/R24`.
```
-- G1: continuous bounded representatives of P_t f, f in C_c (for the three instances `S.A = Afull d`, `S.A_0 = A_0 d` hold by `rfl`)
theorem rd_semigroup_cc_exists_cont (hA : S.A = Afull d) (hA0 : S.A₀ = A₀ d) (t : R>=0)
    (f : C_c(Rd d, R)) {C : R} (hC : forall y, |f y| <= C) :
    exists g : C(Rd d, R), (forall x, |g x| <= C) /\
      (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d -> R) =ᵐ[S.toDiffusionTriple.mu] g

-- G2: exact reduction of the C_0-Feller property to decay at infinity
theorem rd_isFellerC0_iff_decay (hA : S.A = Afull d) (hA0 : S.A₀ = A₀ d) :
    IsFellerC0 S.toDiffusionTriple <-> forall (t : R>=0) (f : C_c(Rd d, R)) (g : C(Rd d, R)),
      (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d -> R) =ᵐ[S.toDiffusionTriple.mu] g ->
        Tendsto g (cocompact (Rd d)) (nhds 0)

-- G3: pointwise initial condition (generic form)
theorem rd_initial_condition (hA : S.A = Afull d) (hA0 : S.A₀ = A₀ d) (hCD : S.CD 0 ∞)
    (hell : forall R : R, exists c : R, 0 < c /\ forall g : Rd d -> R, Sm g -> forall x : Rd d, ‖x‖ <= R ->
      c * ∑ i, pderiv g i x ^ 2 <= S.toDiffusionTriple.ΓA g g x)
    (f : C_c(Rd d, R)) (x : Rd d) {eps : R} (heps : 0 < eps) :
    exists delta : R>=0, 0 < delta /\ forall t : R>=0, t < delta -> forall g : C(Rd d, R),
      (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d -> R) =ᵐ[S.toDiffusionTriple.mu] g -> |g x - f x| < eps
```
Gibbs instance (`G : GibbsRdData d`, `S = G.gibbsRdFull_unconditional`; `Hess V >= 0` is `HessGe G.V 0`):
```
theorem gibbsRdFull_isFellerC0_iff_decay : (G2 for S = G.gibbsRdFull_unconditional)
theorem gibbsRdFull_hinit (hV : HessGe G.V 0) (hF : IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple)
    (x : Rd d) (f : C_c(Rd d, R)) : Tendsto (fun t : R>=0 => Qop hF t f x) (nhds[>] 0) (nhds (f x))
noncomputable def gibbsRdFull_bridge_of_feller_ac (hV : HessGe G.V 0) (hF : IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple)
    (hac : forall s : R>=0, 0 < s -> forall x, fellerKernelInf hF s x ≪ G.gibbsRdFull_unconditional.toDiffusionTriple.mu) :
    MarkovProcessBridge G.gibbsRdFull_unconditional.toDiffusionTriple      -- R29 `gibbsRdFull_bridge_of_feller` with (d) discharged
```
G1, G2 apply (by `rfl` equalities) to `gibbsRdFull_unconditional`, `fullU`, `riemFull_unconditional`.

## DIFFERENCE FROM BGL
None for G3 (BGL Cor. 3.3.19 gradient bound + strong continuity).  G1's continuity argument (smooth representative + uniform approximation) is standard real analysis, not in BGL.
