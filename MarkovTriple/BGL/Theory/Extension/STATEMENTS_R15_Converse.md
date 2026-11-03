# Round 15: converse of BGL Prop. 3.3.17 (book p. 162).  Statements fixed BEFORE the proofs.

Change only by a logged erratum in `ERRATA.md`.  Setting: `T : FullTriple E` (F1-F10; F10 = ESA in core form, S10 = ergodicity
are fields).  `G = ΓA`, `Γ₂ = DiffusionTriple.Γ₂`, `K(g) = Γ₂(g) - ρΓ(g)`.

## Book statement (p. 162, last claim of Prop. 3.3.17)
Under ESA, CD(ρ,∞) and ergodicity: `f ∈ L²(μ) ∩ 𝒜` with `Γ₂(f), Γ(f) ∈ L¹` ⇒ `f ∈ 𝒟(L)`.

## Target T-conv (the formal converse)
`FullTriple.mem_domain_of_Γ₂ (hCD : T.CD ρ n) (hf : f ∈ T.A) (hf2 : MemLp f 2 μ) (hG : Integrable (G T f f) μ)
(hG2 : Integrable (Γ₂ f f) μ) : ∃ hF : [f] ∈ 𝒟(L), L[f] = [L f]`   -- under the additional hypothesis `T.Core2` below.

## Book proof, steps, and what each is in Lean
* (0) reduce to `L f ∈ L²` by 3.3.6 (i)  [`mem_domain_of_adjoint`, existing].
* (1) `{L h : h ∈ 𝒜₀}` dense in `L²₀`  [book; NOT used in the route below].
* (2) `ℓ_f(h) = ∫(Lf + ρ f)Lh = ∫K(f,h)`, `|ℓ_f(h)|² ≤ ∫K(f) ∫K(h) ≤ C(f) ‖h‖²_{𝒟(L)}`  [lemmas `int_Γ₂_mul`, `ell_sq_le`:
  integrated Cauchy-Schwarz for `K` on `𝒜 × 𝒜₀`, obtained from `K(f + s h) ≥ 0` (CD) and the discriminant].
* (3)-(4) the book obtains `|ℓ_f(h)| ≤ C ‖L h‖₂` by Riesz in `𝒟(L)` and the spectral calculus, then extends `ℓ_f` to `L²`.
  Route formalized here (same ingredients, no spectral calculus): put `v = h - L h ∈ 𝒜₀`; then `‖h‖_{𝒟(L)} ≤ ‖v‖₂` and
  `∫ f L v = (1+ρ)∫ f L h - ℓ_f(h)`, hence `|∫ f L v| ≤ M ‖v‖₂` for all `v ∈ (1-L)𝒜₀`  [`bound_fLv`].
  Hahn-Banach + Riesz in `L²` give `w ∈ L²` with `∫ f L v = ⟪w, v⟫` on `(1-L)𝒜₀`.
* (5) **Implicit hypothesis of the book (`Core2`)**: passing from `v ∈ (1-L)𝒜₀` to arbitrary `u ∈ 𝒜₀` (equivalently:
  "`ℓ_f` extends to `L²`", "`g = Lk` from the spectral decomposition") needs that `(1-L)𝒜₀` is a core for `L`, i.e. that
  `𝒜₀` is a core for `L²` (L² essentially self-adjoint on `𝒜₀`).  The book states only ESA of `L` (core for `L`) and ergodicity; the
  step is not derived there and does NOT follow from "𝒜₀ core for L" by abstract operator theory (powers of ES operators need
  not be ES on the same invariant domain).  Formal statement:
  `FullTriple.Core2 T := ∀ a : 𝒜₀, ∃ b : ℕ → 𝒜₀, [b_n] - [L b_n] → [a] and [L b_n] - [L L b_n] → [L a]` (in `L²`).
* (6) with `Core2`: `∫ f L u = ⟪w,u⟫` for all `u ∈ 𝒜₀` ⇒ `[f] ∈ 𝒟(L*) = 𝒟(L)` (`mem_domain_of_adjoint`).

## Consequences recorded
* Ergodicity S10 is not needed in this route (it is needed in the book only for (1)); noted in the self-audit.
* Unconditional converse (without `Core2`) is NOT claimed.
