# Round 15 (Core2): deciding `FullTriple.Core2`.  Statements fixed BEFORE the proofs.

Change only by a logged erratum in `ERRATA.md`.  Setting: `T : FullTriple E` (F1-F10), `Φ = 1 - L`, `Ψ = (1-L)^2` on `𝒜₀`,
all as `L²`-valued maps `b ↦ [b] - [L b]` and `b ↦ [b] - 2[L b] + [L L b]`.

## Book analysis (p. 161-162, Prop 3.3.17 last claim; Prop 3.2.1/Cor 3.2.2; Prop 3.3.6; Prop 3.3.11)
The book's p. 162 argument works with `ℓ_f(h) = ∫ K(f,h)`, `h ∈ 𝒟(L)`; `|ℓ_f(h)| ≤ C‖h‖_{𝒟(L)}`; Riesz in `𝒟(L)` gives `g`;
"easily seen from the spectral decomposition g = Lk"; then `ℓ_f(h) = ∫(Lg + k)Lh` for `h ∈ 𝒜₀`, bounded by `C‖Lh‖₂`; "ESA and
ergodicity: ℓ_f extends to L²", hence `Lf + ρ f ∈ L²`.  The identification `ℓ_f(h) = ∫(Lf+ρf)Lh` is for `h ∈ 𝒜₀` only; passing to
the conclusion `f ∈ 𝒟(L*)` needs the bound on `⟨f, L u⟩` for `u` in a core of `L`, while the book's bound lives on `u = L h`,
`h ∈ 𝒜₀` (or on `(1-L)𝒜₀`): that `L𝒜₀` / `(1-L)𝒜₀` is again a core is exactly `Core2` (the previous round's R15-1).  Prop 3.3.6, Prop 3.3.11
and Cor 3.2.2 only give a core for `L` (ESA), never for `L²`.  We found no book argument that avoids it.

## Targets
* **T-red** (abstract reduction).  `FullTriple.core2_of_dense : Dense (range of Ψₗ) → T.Core2`, where
  `Ψₗ b = [b] - 2[L b] + [L L b]` (`= (1-L)² b`).  (Converse direction also true; not needed.)
  Proof uses only: `‖[c]‖,‖[Lc]‖ ≤ ‖[c]-[Lc]‖` for `c ∈ 𝒜₀` (F5, F7), and (a.e.) linearity of `L` on `𝒜₀`.
* **T-compact.** For every `CompactTriple` (`𝒜 = 𝒜₀`): the converse `CompactTriple.mem_domain_of_A` holds with NO `Core2`, NO `CD`,
  NO integrability hypothesis: `f ∈ 𝒜 ∩ L² ⇒ [f] ∈ 𝒟(L)` and `L[f] = [L f]` a.e. (trivial: every `f ∈ 𝒜` is a test function).
  (`Core2` itself is NOT claimed for compact triples.)
* **T-OU.** `ouFull.Core2` (via `Dense ((1-L)² C_c^∞)` in `L²(γ)`: Hermite basis + a cut-off approximation `cutoff_approx2`
  in the graph norm of `L²`, using the closure properties of rescaled cut-off derivatives, `Core2Tail.lean`), hence
  `ou_mem_domain_of_Γ₂` : the converse for `ouFull` with `CD(1,∞)` (`ouFull_CD`) and no further hypothesis.
* **T-Leb.** `lebesgueFull.Core2` (resolvent solution `v` of `v - v'' = a`, `v, ..., v⁗ ∈ L²`, `χ_n v → v` in the graph norm
  of `L²`), hence `lebesgue_mem_domain_of_Γ₂` (for `CD(ρ,n)`, `ρ ≤ 0`, `1 ≤ n`).
* **Gibbs** (`gibbsFull_unconditional`): NOT claimed.  `Core2` for a general `GibbsData` is open (see audit).

## Not claimed
* Core2 for an arbitrary `FullTriple` (no derivation from F1-F10 found; see `AUDIT_R15_CORE2_SELF.md`).
* The `ρ ≥ 0` remark (`Γ(f) ∈ L¹` not needed) of the book.
