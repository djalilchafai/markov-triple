# Round 15 self-audit: converse of BGL Prop. 3.3.17 (p. 162)

Files: `Theory/Extension/Converse.lean` (+ `AxiomCheckR15.lean`), statements `Theory/Extension/STATEMENTS_R15_Converse.md`
(written before the proofs), erratum `ERRATA.md` R15-1, R15-2.

## 1. What is proved
* `int_Γ₂_mul`: `∫Γ₂(f,h) = ∫ Lf·Lh`, `f ∈ 𝒜`, `h ∈ 𝒜₀` (F1, F7).  `int_L_A₀`: `∫ L g = 0`.
* `ell_sq_le` (book: "`K` positive bilinear ⇒ `K(f,h)² ≤ K(f,f)K(h,h)`", integrated): `(∫K(f,h))² ≤ ∫K(f) ∫K(h)`, from CD via
  `K(f + s h) ≥ 0` a.e., the quadratic expansion (`Γ₂_quad`, `G_quad`) and the discriminant.
* `exists_rep`: Hahn–Banach + Riesz: `|Λ b| ≤ M‖Φ b‖` ⇒ `Λ b = ⟪w, Φ b⟫`.
* `bound_fLv`: `|∫ f L(b − Lb)| ≤ M ‖[b] − [Lb]‖`, `M = |1+ρ|‖f‖₂ + √(∫K(f)(1+|ρ|))`.
* `mem_domain_of_Γ₂` (CONDITIONAL on `Core2`): `f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹` ⇒ `[f] ∈ 𝒟(L)`, `L[f] = [Lf]` a.e.
* `core2_of_surjective`: `Core2` holds when `(1−L)𝒜₀ = 𝒜₀` (a.e.).

## 2. What is NOT proved (exact)
The unconditional converse.  The missing input is `FullTriple.Core2`:
`∀ a ∈ 𝒜₀ ∃ b_n ∈ 𝒜₀, [b_n − L b_n] → [a], [L(b_n − L b_n)] → [L a]` in `L²` (i.e. `𝒜₀` is a core for `L²`).  The book (p. 162) uses it
without proof ("easily seen from the spectral decomposition", "extended to `L²`").  We did not find a derivation of it from F1–F10
(ESA is the core property for `L` only); it is not a "non-book idea" but a gap in the book's text, hence the conditional theorem.
Whether `Core2` is derivable from F8 (`P_t 𝒜₀ ⊂ 𝒜`) + CD is open to us; we did not produce a counterexample either.

## 3. Attacks on the statement
* **Vacuity of the hypotheses.** `Γ₂(f) ∈ L¹` and `Γ(f) ∈ L¹` hold for all `f ∈ 𝒜 ∩ 𝒟(L)` (R14: `integrable_Γ₂_of_domain`), so the
  hypothesis class contains the conclusion class; the theorem is the converse, non-trivial exactly when `𝒜 ∩ 𝒟(L) ⊊ 𝒜 ∩ L²`.
  `Core2` is satisfiable (`core2_of_surjective`) but only checked abstractly: no concrete `FullTriple` instance of the library was shown
  to satisfy `Core2` (the circle full-instance is not in the library).  So the theorem is not yet exercised on an instance.
* **Total-function junk.** `Γ₂`, `G`, `L` are total; all arguments are in `𝒜` / `𝒜₀` by hypothesis; `Lb b := ⟨L b, _⟩ ∈ 𝒜₀`.
  The class `[f]` is `hf2.toLp f`.  The conclusion `L[f] = [Lf]` is a.e.
* **`μ(E) = 1` vs `∞`.** The route never uses density of `L𝒜₀` in `L²₀`, so the finite/infinite distinction of the book disappears;
  `1 ∈ L²` for finite `μ` is allowed (`f = const` gives `Γ₂ = 0`, trivially in `𝒟(L)`).
* **Use of S10.** Not used (book: only for step (1)).  Not a contradiction: the book's use is to identify `{Lh}` as dense in `L²₀`; in the
  route here the dense set is `(1−L)𝒜₀` (dense in `L²` once `Core2` and D2 hold), where no ergodicity is needed.
* **CD.** `CD ρ n` with any `n ≥ 1`; only `K = Γ₂ − ρΓ ≥ 0` is used (book: CD(ρ,∞)).  `ρ` may be negative (the bound uses `1+|ρ|`).
* **ESA.** F10 enters only through `mem_domain_of_adjoint` (with `esa` of the resolvent) and, implicitly, in the statement of `Core2`.
* **Hypothesis `hG: Γ(f) ∈ L¹`** is used only to make `K(f) = Γ₂(f) − ρΓ(f)` integrable in `ell_sq_le`.  The book's closing remark (for `ρ ≥ 0`
  `Γ(f) ∈ L¹` is not needed) is NOT formalized; we assume both hypotheses as in the book's statement.

## 4. Attack surface (for the independent hostile audit)
1. `Core2` is a genuine extra hypothesis: check the claim that it is implicit in the book's step and not derivable from F1–F10 (a derivation
   would remove the conditionality; a counterexample would make the book's statement suspect in this generality).
2. `LLₗ` (`b ↦ [L L b]`) linear structure: a.e. linearity of `L` on `𝒜₀` and `L_congr_A`; `Φₗ`, `Λₗ` definitions match `v = b − Lb`.
3. `bound_fLv`: the inequalities `‖[Lb]‖ ≤ N`, `‖[b]‖ ≤ N` use `⟪[b],[Lb]⟫ = −∫Γ(b) ≤ 0` (F5, F7); check `hCle`, `hℓbd`.
4. `ell_sq_le`: integrability of `K(f,h)` (`Γ₂_pairA₀`: `∈ 𝒜₀`) and a.e. expansions.
5. `exists_rep`: well-definedness on `range Φ` through `quotKerEquivRange` (does not need injectivity of `Φ` on test functions).
6. `Core2` statement: the second limit is `[Lb_n] − [L L b_n] → [L a]`, the `L`-image of `(1−L)b_n → a`.
7. Final step: `mem_domain_of_adjoint` takes adjointness against ALL of `𝒜₀` (`hadj`), proved by the limit in `Core2`.
