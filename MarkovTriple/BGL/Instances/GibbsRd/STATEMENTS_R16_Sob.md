# STATEMENTS R16 Sob (Armstrong method): Sobolev embedding for weak derivatives — written BEFORE the proofs

Textbook: Evans PDE §5.6.3 Thm 6 (Morrey/Sobolev, general), §5.8.2 Thm 4/5; Gilbarg–Trudinger Thm 7.25–7.26, Cor. 7.11;
interior (local) version.  Namespace `MarkovTriple.BGL.Instances.GibbsRd.Sob`, files `SobDefs.lean`, `SobOrthant.lean`,
`SobMollify.lean`, `SobMain.lean`.  Functions on `Rd d = Fin d → ℝ`, Lebesgue measure.

## Definitions
* `WeakDeriv f g i` : shared definition, verbatim, with ONE forced change: `ContDiff ℝ ⊤ φ` is written `ContDiff ℝ ∞ φ`
  (`∞ = ((⊤:ℕ∞):WithTop ℕ∞)`).  Reason: in this Mathlib the literal `⊤ : WithTop ℕ∞` is `ω` = analytic; analytic + compact
  support forces `φ = 0` and the definition would be vacuous.  (The repo's `Sm`/`Afull` use `(⊤ : ℕ∞)`, same meaning.)
* `LocL2 f` := `∀ K compact, MemLp f 2 (volume.restrict K)`.
* `HasSobL2 k f` (recursive): `HasSobL2 0 f := LocL2 f`; `HasSobL2 (k+1) f := LocL2 f ∧ ∀ i, ∃ g, WeakDeriv f g i ∧ HasSobL2 k g`.
  Unfolded: for every word `(i₁,…,i_j)`, `j ≤ k`, the iterated weak derivative exists (as a chain of `WeakDeriv`) and is `L²_loc`.
  (Iterated, not multi-index; each step is a weak derivative of the previous one, as in the task text.)
* `HasSobL1` : same with `LocallyIntegrable` (weaker; the embedding is proved for it; `HasSobL2.toL1`).

## Theorems
S1 (core classical inequality, Gagliardo/FTC telescoping) `abs_le_integral_mixD`: `d`, `φ ∈ C_c^∞(ℝ^d)`:
   `|φ(x)| ≤ ∫ |∂_0 ∂_1 ⋯ ∂_{d-1} φ|` (all `x`).  [Evans §5.6 proof of Thm 6 step, the `W^{d,1} ⊂ L^∞` case.]
S2 (mollification) `WeakDeriv h g i → ∂_i (h ⋆ ρ) = g ⋆ ρ` for `ρ ∈ C_c^∞`; iterated along `WeakIter`.
S3 (continuous representative, order `d`) `sob_continuous_rep`: `HasSobL1 d f → ∃ g, Continuous g ∧ f =ᵐ g`.
S4 (`C^m`) `sob_contDiff_rep`: `HasSobL1 (m + d) f → ∃ g, ContDiff ℝ m g ∧ f =ᵐ g`; same for `HasSobL2`.
S5 (CORE INTERFACE) `smooth_of_weak_all_orders`: `(∀ k, HasSobL2 k f) → ∃ g, ContDiff ℝ ∞ g ∧ f =ᵐ g`
   (and `L1` form).  Also `sob_contDiff_rep` gives every `C^m` and `smooth_rep_unique`.

## HONEST SCOPE (deviation from the task's sharp indices)
The task asks for `k > d/2` (resp. `k ≥ m + ⌊d/2⌋ + 1`).  The route chosen (mixed-derivative/FTC telescoping, no Fourier
analysis) proves the embedding with `k = d` (resp. `k = m + d`): `W^{d,1}_loc ⊂ C` (mixed derivative).  Sharp indices need
Plancherel/Fourier or the Gagliardo–Nirenberg `L²` interpolation; NOT done here (open, stated in the report).  Since the
core interface `smooth_of_weak_all_orders` quantifies over all orders, and `EllReg` has `∃ n` depending on `m`, the weaker
index suffices for the glue (`2n ≥ m + d`).

## Status (end of round)
All of S1-S5 proved, no `sorry`, standard axioms only.  Lean names: `abs_le_integral_mixD` (S1), `pd_mol_weak`, `iterD_mol`
(S2), `sob_core` / `sob_core_contDiff` (core, compact support), `sob_continuous_rep`, `sob_contDiff_rep`, `sob_contDiff_rep_L2`
(S3/S4), `smooth_of_weak_all_orders` (+ `_L1`) (S5; conclusion `ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)`).  Open: sharp index.
Erratum R16-Sob-E1 (ω vs ∞) logged in ERRATA.md.
