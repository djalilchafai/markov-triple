# Round 32, Stream B2: frozen target statements (pointwise reverse Poincare inequality)

Written BEFORE any proof.  Namespace `MarkovTriple.Stochastic.R32B2`, directory `MarkovTriple/Stochastic/R32B2/` (+ `AxiomCheckR32B2.lean`).
Extends Round 31 Stream U (`Stochastic/R31U`, `reverse_poincare_sup`).

## Scope (what is attempted)
ATTEMPTED: the pointwise reverse Poincare inequality `2t Gamma(P_t f) <= P_t(f^2) - (P_t f)^2` a.e. for `f` in the test algebra, under `CD(0,inf)`,
finite `mu`, on a generic `FullTriple`.
NOT attempted in this round (stated honestly up front): `CD(rho,inf)` with `rho < 0`, the 1-D `gibbsFull`, non-finite `mu`.

## Route (BGL, proof of the reverse Poincare inequality; interpolate `s |-> P_s((P_{t-s} f)^2)`)
* `f^2 in A_0` (non-unital subalgebra), so `P_t(f^2)` has an `A`-representative `T.Pt t (f^2)` (F8): the final positivity detection is the ordinary F2.
* The obstacle of Round 31 (`P_s(Gamma(P_{t-s} f))` has no `A`-representative) arises only in the weak monotonicity
  `int h Gamma(P_t f) <= int P_s h Gamma(P_{t-s} f)`.  It is removed by (B1) a positivity detection for `L^2` functions, proved from the density D2 of `A_0` in `L^2`
  and `comp_mem` (`h -> sqrt(h^2+e^2)-e`), combined with the library `strongInterpolation` (square-root form, `e -> 0`), Jensen `jensen_sq` for the sub-Markov `P_s`
  and the symmetry of `P_s`.

## Statements

B1 (positivity detection in `L^2`, `Stochastic/R32B2/Detect.lean`; any `DiffusionTriple`):
```
theorem pos_detect_L2 {E : Type*} [MeasurableSpace E] (D : DiffusionTriple E) {u : E → ℝ}
    (hu : MemLp u 2 D.μ) (h : ∀ g ∈ D.A₀, 0 ≤ᵐ[D.μ] g → 0 ≤ ∫ x, g x * u x ∂D.μ) :
    0 ≤ᵐ[D.μ] u
```
B2 (pointwise reverse Poincare inequality, `Stochastic/R32B2/Main.lean`; generic `FullTriple`):
```
theorem reverse_poincare_pointwise {E : Type*} [MeasurableSpace E] (T : FullTriple E)
    [IsFiniteMeasure T.μ] (hCD : T.CD 0 ∞) (f : T.A₀) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ x ∂T.μ, 2 * (t : ℝ) * T.toDiffusionTriple.ΓA (T.Pt t f) (T.Pt t f) x ≤
      T.Pt t ⟨f.1 * f.1, T.A₀.mul_mem f.2 f.2⟩ x - (T.Pt t f x) ^ 2
```

## DIFFERENCE FROM BGL
None in the statement (BGL states it pointwise).  The proof deviates only in how monotonicity is passed from the square-root form to the `Gamma` form
(Jensen for `P_s` plus `L^2` positivity detection), recorded here because the book simply says "by Jensen".

## Status
Files (`Stochastic/R32B2/`): `Detect.lean` (B1), `Weak.lean` (`sqrt_form`, `weak_mono`), `Main.lean` (`reverse_integrated`, B2), `AxiomCheckR32B2.lean`.  No `sorry`, no `set_option`, 0 warnings, axioms only `propext, Classical.choice, Quot.sound`; full `lake build` green.
ALL frozen statements PROVED with the frozen names and hypotheses, not weakened: `pos_detect_L2` (B1), `reverse_poincare_pointwise` (B2).
Delivered beyond the frozen text: `phiE`, `selfadj_int`, `selfadj_test` (symmetry of `P_s` on `L^2` classes), `sqrt_form` (`int h sqrt(Gamma(P_t f)) <= int P_s h sqrt(Gamma(P_{t-s} f))`), `weak_mono` (`int h Gamma(P_t f) <= int P_s h Gamma(P_{t-s} f)`, `0<s<t`), `reverse_integrated`.
NOT attempted (as announced in the freeze): `CD(rho,inf)` with `rho < 0`, the 1-D `gibbsFull`, non-finite `mu`; consequently `rd_kernel_ac` (R31U) is not extended.
Remark: the hypothesis `0 < t` is not needed by the proof of `reverse_integrated`; it is kept in B2 as frozen.
