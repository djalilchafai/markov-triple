# Round 31, Stream U: frozen target statements (reverse Poincare inequality and `kappa_s(x,.) << mu` at every `x`)

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R31U`, directory `Stochastic/R31U/` (+ `AxiomCheckR31U.lean`).
Goal: close open item (c) of Round 29/30 (ERRATA R30-T-1): `kappa_s(x,.) << mu` at EVERY `x` for the Feller kernels of the reduced
bridges `*_bridge_of_feller_ac` (`Stochastic/R30T`).  `IsFellerC0` (item (a)) stays an explicit hypothesis.

## Route (BGL)
BGL Ch. 3/4: under `CD(0,inf)`, interpolate `s |-> P_s((P_{t-s} f)^2)`: its derivative is `2 P_s Gamma(P_{t-s} f)`, and the gradient bound
(Thm 3.3.18 / Cor. 3.3.19, already unconditional in the library via `strongInterpolation`) gives `Gamma(P_t f) <= P_s Gamma(P_{t-s} f)`; hence
the reverse Poincare inequality `2 t Gamma(P_t f) <= P_t f^2 - (P_t f)^2`.  We prove it in the weak (test-function `h`) form dictated by the
`FullTriple` axioms (positivity detection F2 only applies to `A`-valued functions) and extract the sup-form used below.  Then:
Lipschitz bounds `|grad P_t f| <= C/sqrt(2 c t)` locally uniformly in `f` with `|f| <= C` (local ellipticity), uniform approximation of `C_c`
by `C_c^infty`, and the argument "`mu(K) = 0`, `f_n down 1_K`, `P_s f_n -> 0` in `L^2` and locally equi-Lipschitz, hence `Q_s f_n (x) -> 0` at every `x`",
inner regularity of the Riesz measure `kappa_s(x,.)`.

## Decisions made before proving (honest)
* The full POINTWISE reverse Poincare inequality `2 t Gamma(P_t f) <= P_t(f^2) - (P_t f)^2` a.e. is NOT a frozen target: its proof needs positivity
  detection for `L^2`-classes (`P_s(Gamma(P_{t-s} f))` has no `A`-representative); what is frozen (U1) is the sup-form, which is all that item (c) needs.
  If the pointwise form is obtained it is recorded in the Status section only.
* Finiteness of `mu` is assumed (`[IsFiniteMeasure]`): the integrations by parts (`ibp_bdd`, `Bdd.domain`) of the library are for finite `mu`.
  The three instances `gibbsRdFull_unconditional`, `fullU`, `riemFull_unconditional` have probability reference measures.
* `CD(0,inf)` (convex `V`, `Curv 0`) as in R30T; negative curvature is NOT covered.
* The 1-d `gibbsFull` (`FullTriple R` with its own `Afull`) is not covered (generic theorems are for `FullTriple (Rd d)`).

## Statements

U1 (sup-form of the reverse Poincare inequality; `Stochastic/R31U/Reverse.lean`, generic `FullTriple`):
```
theorem reverse_poincare_sup {E : Type*} [MeasurableSpace E] (T : FullTriple E) [IsFiniteMeasure T.μ] (hCD : T.CD 0 ∞)
    (f : T.A₀) {C : ℝ} (hC : ∀ᵐ x ∂T.μ, |f.1 x| ≤ C) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ x ∂T.μ, 2 * (t : ℝ) * T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) x ≤ C ^ 2
```
U2 (Lipschitz smoothing of `C_c` data, `Stochastic/R31U/Lip.lean`): `S : FullTriple (Rd d)`, `[IsFiniteMeasure S.toDiffusionTriple.μ]`,
`[S.toDiffusionTriple.μ.IsOpenPosMeasure]`, `hA : S.A = Afull d`, `hA₀ : S.A₀ = A₀ d`, `hCD : S.CD 0 ∞`, `hell` as in R30T `rd_initial_condition`:
```
theorem rd_smoothing_lip (R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ≥0, 0 < t → ∀ (C : ℝ) (f : C_c(Rd d, ℝ)), (∀ y, |f y| ≤ C) →
      ∀ g : C(Rd d, ℝ), (S.toDiffusionTriple.semigroup t (ccL2 S.toDiffusionTriple f) : Rd d → ℝ) =ᵐ[S.toDiffusionTriple.μ] g →
        ∀ x y : Rd d, ‖x‖ < R → ‖y‖ < R → |g x - g y| ≤ K * C / Real.sqrt t * ‖x - y‖
```
U3 (absolute continuity of the Feller kernel at EVERY point, `Stochastic/R31U/Kernel.lean`): same hypotheses as U2 and `hF : IsFellerC0 S.toDiffusionTriple`:
```
theorem rd_kernel_ac (hF : IsFellerC0 S.toDiffusionTriple) (s : ℝ≥0) (hs : 0 < s) (x : Rd d) :
    fellerKernelInf hF s x ≪ S.toDiffusionTriple.μ
```
U4 (reduced bridges with (c) and (d) discharged, `Stochastic/R31U/Instances.lean`; `IsFellerC0` the only analytic hypothesis):
```
noncomputable def gibbsRdFull_bridge_of_feller_U (G : GibbsRdData d) (hV : HessGe G.V 0)
    (hF : IsFellerC0 G.gibbsRdFull_unconditional.toDiffusionTriple) : MarkovProcessBridge G.gibbsRdFull_unconditional.toDiffusionTriple
noncomputable def fullU_bridge_of_feller_U (E : EllData d) (hC : E.Curv 0) (hF : IsFellerC0 E.fullU.toDiffusionTriple) :
    MarkovProcessBridge E.fullU.toDiffusionTriple
noncomputable def riemFull_bridge_of_feller_U (R : Riemannian.RiemData d) (hC : R.Curv 0)
    (hF : IsFellerC0 R.riemFull_unconditional.toDiffusionTriple) : MarkovProcessBridge R.riemFull_unconditional.toDiffusionTriple
```
(and `gibbsRdFull_kernel_ac`, `fullU_kernel_ac`, `riemFull_kernel_ac`: U3 for the three instances).

## DIFFERENCE FROM BGL
The book states the reverse Poincare inequality pointwise (BGL Thm 4.7.2-type); here only its sup-form is a frozen target, see Decisions.
The step "`kappa_s(x,.) << mu` at every `x` from local equi-Lipschitz bounds" (Riesz measure, Chebyshev on a ball, inner regularity) is standard measure theory, not in BGL.

## Status
Files (`Stochastic/R31U/`): `Tri.lean`, `Theta.lean`, `Reverse.lean` (U1), `Lip.lean` (U2), `Kernel.lean` (U3), `Instances.lean` (U4), `AxiomCheckR31U.lean`.  No `sorry`, no `set_option`, 0 warnings, axioms only `propext, Classical.choice, Quot.sound`; full `lake build` green.
ALL frozen statements PROVED with the frozen names, not weakened: `reverse_poincare_sup` (U1), `rd_smoothing_lip` (U2), `rd_kernel_ac` (U3), `gibbsRdFull_bridge_of_feller_U`, `fullU_bridge_of_feller_U`, `riemFull_bridge_of_feller_U`, `gibbsRdFull_kernel_ac`, `fullU_kernel_ac`, `riemFull_kernel_ac` (U4).  Hypotheses: U2/U3 carry `hA hA₀ hCD hell` explicitly; the instance `*_kernel_ac` carry the convexity hypothesis `hV`/`hC` and `hF` (ERRATA R31-U-3).
Delivered beyond the frozen text: `int3_le`, `tri_continuous`, `hasDerivAt_int3`, `theta_continuous`, `theta_hasDerivAt`, `Pt_bdd`, `ibp_sq`, `strong_mono`, `reverse_aux`, `lip_smooth`, `kernel_null_compact`.
NOT proved: `IsFellerC0` (item (a)), the pointwise reverse Poincare inequality (only the sup-form), non-finite `mu`, `CD(rho,inf)` with `rho < 0` (ERRATA R31-U-1, R31-U-2, R31-U-4).
