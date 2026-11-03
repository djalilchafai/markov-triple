# Round 17, Stream A (Gibbs `Core2`): statements fixed BEFORE the proofs.

Change only by a logged erratum in `ERRATA.md` (prefix `R17-`).  Setting: `G : GibbsData` (1-D, `μ = Z⁻¹ e^{-V}dx`,
`𝒜₀ = C_c^∞`, `L f = f'' - V' f'`), `G.gibbsFull_unconditional : FullTriple ℝ` (F1-F10, `WeakHypo`/`F8` theorems since R15).

## Analysis of the book's argument (BGL p. 161-162, Prop. 3.3.17, last claim; see `Theory/Extension/STATEMENTS_R15_Core2.md`)
The book's proof needs `(1-L)𝒜₀` to be a core for `L` (= `Core2`, ERRATA R15-1).  By the reduction `core2_of_dense`
(`Theory/Extension/Core2Reduce.lean`) it suffices that `(1-L)² 𝒜₀` is dense in `L²(μ)`, i.e. that `L²` is essentially
self-adjoint on `C_c^∞`.  The route taken for OU and Lebesgue (`Instances/OU/Core2*`, `Instances/Lebesgue/Core2*`) is the
direct one, which we follow: for `a ∈ 𝒜₀` solve `v - L v = a` (resolvent of the Friedrichs generator; smoothness by the
elliptic regularity already proved for Gibbs), show `v, v', v'', v''' ∈ L²(μ)`, and cut off: `b_n = χ_n v ∈ 𝒜₀` satisfies
`(1-L) b_n → a`, `L(1-L) b_n → L a` in `L²(μ)`.  The cut-off commutators `[L, χ_n]` involve `V' χ_n'`, `V'' χ_n'`,
`V''' χ_n'`; they are controlled (dominated convergence, uniformly in `n`) exactly when `V', V'', V'''` are bounded.
**We do NOT claim `Core2` for arbitrary `GibbsData`**: for `V` with unbounded derivatives the commutator terms are not
controlled by the information `v ∈ 𝒟(L²)`, and we found no argument in the book (or elsewhere) giving `Core2`
(equivalently ESA of `L²` on `C_c^∞`) in general; `OU` (`V = x²/2`, unbounded `V'`) is covered by its own proof.

## Targets (names in `MarkovTriple.BGL.Instances.Gibbs`)
* **A0** `GibbsData.BddJet (G) : Prop`: `V'`, `V''`, `V'''` (`deriv`, `deriv ∘ deriv`, `deriv ∘ deriv ∘ deriv`) are bounded on `ℝ`.
* **A1** `GibbsData.exists_resolvent_smooth`: `a ∈ 𝒜₀` ⇒ `∃ v`, `v` smooth (`ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)`), `MemLp v 2 μ`,
  `∀ x, L v x = v x - a x`.   (No `BddJet`.)
* **A2** `GibbsData.resolvent_jet_L2` (under `BddJet`): for `v` as in A1, `v', v'', v''' ∈ L²(μ)`.
* **A3** `GibbsData.gibbsFull_core2 (hb : G.BddJet) : G.gibbsFull_unconditional.Core2`.
* **A4** `GibbsData.gibbs_mem_domain_of_Γ₂` (**unconditional converse of Prop. 3.3.17 for bounded-jet Gibbs**): `BddJet`,
  `∀ x, ρ ≤ V''`, `f ∈ 𝒜`, `f ∈ L²(μ)`, `Γ(f), Γ₂(f) ∈ L¹(μ)` ⇒ `[f] ∈ 𝒟(L)` and `L[f] = [L f]` a.e.  (From A3 and
  `FullTriple.mem_domain_of_Γ₂` with `gibbsFull_CD_unconditional`.)
* **A5** non-vacuity: `BddJet` holds for `V(x) = √(1+x²)` (a genuine `GibbsData`), so A3-A4 are not empty.

## Not claimed
* `Core2` / the converse for `GibbsData` without `BddJet`; for `EllData`/`GibbsRdData` on `ℝ^d` see `STATEMENTS_R17_Core2Rd.md`
  (if present) and the audit `AUDIT_R17_GIBBSCORE2.md`.
