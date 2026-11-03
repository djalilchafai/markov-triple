# Round 15 self-attack (Armstrong step (b)); written against `STATEMENTS_R15.md`

Each item: attack, result, consequence.  "Checked" = verified by a Lean statement or by reading the final code.

## A. Vacuity of the interface structures
1. `KernelRepresentation.rep` / `KernelBridge.rep` are `μ`-a.e. identities, so on their own they would allow
   arbitrary `κ_t(x,·)` for `x` in a null set, and say nothing about the *shape* of `κ_t(x,·)`.  Could a junk family
   satisfy them?  Checked: no, in the sense that the kernels are pinned down a.e.:
   `KernelRepresentation.ae_unique` (finite `μ`, countably generated σ-algebra): two representations of the same
   triple have `μ`-a.e. equal kernels for each `t`; `KernelRepresentation.kernel_null_ae`: `κ_t(x,N) = 0` a.e. for every
   measurable `μ`-null `N` (so `∫ g dκ_t(x,·)` is independent of the representative of `g`, a.e. in `x`).
   Not pinned: the values on a null set of `x` (inherent to the book's convention, BGL Sect. 1.2.2).
2. `μ = 0`: excluded by `DiffusionTriple.finite_prob` (a zero measure is finite, hence a probability measure: absurd).
   `T.A₀ = 0` would make `IsTestClassRep` vacuous, but `T.dense` forces density in `L²`.
3. `KernelBridge` additionally fixes `κ_0 = id` and exact Chapman-Kolmogorov everywhere; the two proved instances
   (OU, circle) have these exactly (`ouKernel_comp`, `circleKernel_comp`; `*_zero`), so the structure is inhabited
   non-trivially (not only by `κ_t = id`, which would force `P_t = id`).
4. `IsMarkov`: both instances are Markov everywhere (`ouSemigroup_isMarkov`, `circleSemigroup_isMarkov`).

## B. Representatives, null sets, junk values
5. `rep` is stated through `hL.toLp g`, so it only sees the `L²` class of `g`; the integral `∫ g dκ_t(x,·)` uses the
   chosen representative.  Consistent by item 1 (`kernel_null_ae`).
6. Junk: `∫ g dκ` is `0` for non-integrable `g`.  All `g` in `rep` are bounded and `κ_t(x,·)` is finite, so the
   integral is a true integral; `IsTestClassRep` uses `T.A₀`, bounded by axiom D2 (`T.bounded`).
7. Riesz kernels: `κ_t(x,·) := 0` on the null set `N_t` of "bad" `x` (where the countably many a.e. conditions fail).
   This is invisible to `rep`.  It makes `rieszKernelRep` sub-Markov only, even for conservative `T`; the Markov
   (everywhere) variant is `rieszKernelRep_markov` (redefine `κ_t(x,·) := δ_x` where the mass is `≠ 1`, a measurable
   set, null by `rieszKernel_univ_ae`).  Checked.
8. a.e. vs everywhere for Chapman-Kolmogorov: the Riesz kernels satisfy only the a.e. forms already derived in
   `KernelRepresentation.ck_integral` / `ck_ae` (no exact CK, no `κ_0 = id`); this is the reason `rieszKernelRep` is a
   `KernelRepresentation` and not a `KernelBridge`.  Exact-CK versions (Kolmogorov/Dynkin regularisation) are NOT
   attempted.  `ck_ae` additionally needs a countably generated σ-algebra (true on compact metrizable spaces).

## C. Hypotheses actually used / finiteness
9. `kernelRep_of_dense`: uses `hsub`, `hinv : μ.bind κ_t ≤ μ` (only this: no equality, no finiteness of `μ`),
   boundedness of `D` (so that `κ_t f` is defined and `h = g - f` stays bounded) and density of `D` in `L²`.
   `hinv ≤` cannot be dropped in general (without it `h ↦ κ_t h` need not be an `L²`-contraction), but is implied by
   invariance (OU, circle: `=`), and in the Riesz case is proved (item 12).
10. Riesz construction: `X` compact, Hausdorff, second countable (so `C(X)` separable and `C(X) ≃ C_c(X)`), Borel
    σ-algebra; `IsFiniteMeasure T.μ` is a *hypothesis* (automatic for `CompactTriple`, `compactTriple_isFiniteMeasure`).
    Not reduced to Polish/locally compact/`σ`-finite (would need `C_c` density in `L²`, cut-offs for the bound
    `|P v| ≤ ‖v‖`; the proof is expected to carry over but is not done).  No relation between `Γ, L` and the topology
    is used (only positivity and sub-Markov of `P_t`): the result holds for every compact metrizable topology
    compatible with the σ-algebra.
11. The two statements about `P_t` used (`semigroup_nonneg`, `semigroup_le_one`) are repo theorems for a bare
    `DiffusionTriple`; they are used for the representatives `P_t [f]`, `f ∈ C(X)` only.
12. Sub-invariance of the Riesz kernels: `∫ P_t u ≤ ∫ u` for `u ≥ 0` by symmetry + `P_t 1 ≤ 1`
    (`integral_semigroup_le`), then continuous `f ≥ 0` → closed sets (`HasOuterApproxClosed`) → Borel sets
    (inner regularity by closed sets of finite measures on metrizable spaces).  The kernel `κ_t` is *not* proved
    invariant (`=`); invariance needs `P_t 1 = 1`, which we do not wire in (only `≤` is needed for `rep`).
13. Choice: `rieszKernel` uses `Classical.choose` three times (functional, measure, kernel).  Only axioms
    `propext/Classical.choice/Quot.sound` appear (all 41 `#print axioms` in `AxiomCheckR15.lean`).

## D. Instance-specific
14. Circle normalisation: `κ_t(x,·) = law(x + Z mod 1)`, `Z ∼ N(0,2t)` is consistent with `L = d²/dx²`,
    `L e_n = -(2πn)² e_n`: this is *proved* (`integral_fourier_heat`: `∫ e_n(x+z) dN(0,2t) = e^{-(2πn)² t} e_n(x)` with
    `lam n = (2πn)²`), not assumed.  The representation is proved on `trigSpan` (real trigonometric span) and
    extended; it is not proved directly on all of `𝒜₀ = C^∞(𝕋)` (not needed: `IsTestClassRep` is not asserted for the
    circle; the `KernelBridge` is).
15. The circle files contain two parallel developments of `mc, ms, lam` (`MarkovTriple.Sanity.Circle` in
    `Analysis/Circle`, `MarkovTriple.BGL.Circle` in `Instances/Circle`); density (`dense_Atrig`) is in the first,
    the semigroup eigen-relations in the second; they are definitionally equal (`fun x => (fourier n x).re`), and
    Lean accepts the mixture by `rfl`-conversion.  Not a soundness issue, a maintenance hazard.
16. OU: `ouKernelBridge` extends `ou_isTestClassRep` (on `C_c^∞`).  Unbounded `g ∈ L²(γ)` (e.g. polynomials, the
    Hermite basis) are NOT covered by `rep` (the statement requires bounded `g`); for them `∫ g dκ_t(x,·)` exists
    for every `x` but the identification with `P_t g` is not stated (it would follow by monotone convergence from
    truncations; not done).

## E. MarkovProcess interface
17. `MarkovProcessSemigroupData` mirrors Armstrong's `SubMarkovKernelSemigroup` as read in a copy of the source
    found at `/tmp/lsi-armstrong-audit/sources/MarkovProcess` (untrusted, a copy of unknown provenance (no .git directory; consistent with the upstream pin 666cda02 used by the sibling project SuperdiffusionCLT)).  Fidelity of the mirror
    to the *current* upstream structure is NOT checkable here.  `IsSubMarkovKernel κ := ∀ x, κ x univ ≤ 1` is unfolded;
    `kernel_add` uses `Kernel.comp` (= `∘ₖ`).  Joint measurability, the only extra field, is proved for OU
    (`ouKernel_measurable_joint`) and circle (`circleKernel_measurable_joint`).
18. No dependency added: `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` untouched (`git status`).

## F. What a hostile reader should still check
* that `kernelRep_of_dense` is not accidentally stronger than needed for the circle (it is applied with
  `D = trigSpan`, whose elements are bounded measurable `L²`; checked by the compiler);
* `rieszKernelRep` for a triple whose σ-algebra is Borel for *two different* compact topologies gives
  a.e.-equal kernels (`ae_unique`), so nothing depends on the topology chosen.
