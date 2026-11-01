# Errata

Source: hostile audit of the frozen statements (see AUDIT_FROZEN.md, MarkovTriple/Audit/TwoPoint.lean).

| id | severity | finding | resolution |
|---|---|---|---|
| F1 | HIGH | Non-ergodic triples (e.g. `Sanity.trivialFull` on `Bool`, L=Γ=0) satisfy `CD ρ ∞` for all ρ but have neither PI nor LSI. `CD(ρ,∞) ⇒ LSI(1/ρ)` is false over the bare structures. | Add a frozen `Ergodic` predicate (Γ f f = 0 ⇒ f const a.e., plus L²-closure form); assume it in the theorems, not in the structure. Status: fixed (pending re-audit): see Frozen/Ergodic.lean, Sanity/Ergodic.lean |
| F2 | MEDIUM | `CD` is imposed on A₀ only, but `FullMarkovTriple.semigroup_stable` lands in A; nothing transfers Γ₂ ≥ ρΓ to A. | Add `CD` on A for full triples (or transfer lemma). Status: fixed (pending re-audit): Frozen/CDFull.lean |
| F3 | MEDIUM | Constants in A₀ force μ finite; infinite σ-finite triples excluded. | Scope note; decide with author. Status: open |
| F4 | LOW | `fisherInfo` has no hypothesis on h (junk value 0 for non-integrable). | Theorems must assume h > 0 and integrability. Status: fixed (pending re-audit): `IsFisherAdmissible` in Frozen/Fisher.lean |
| F5 | MEDIUM | (from Phase 3) Positivity-preservation of P_t cannot be derived from the `MarkovTriple`/`FullMarkovTriple` fields: `diffusion` is guarded by ψ(f) ∈ A₀, so |f| / smooth truncations are not known to lie in the form domain. The bridge `isSemigroupOf_tripleSemigroup` needs the extra hypothesis `IsMarkovianForm T` (|u| ∈ Q, E(|u|) ≤ E(u)). | Author decision: strengthen the structure (BGL: A₀ stable under all smooth ψ) or keep `IsMarkovianForm` as an explicit hypothesis of Bakry–Émery theorems. Status: open |
| B1 | MEDIUM | (re-audit) Ergodicity does not give `IsProbabilityMeasure`: the zero-measure trivial triple is ErgodicL2 with `CD ρ ∞` for all ρ and no PI/LSI. | Every CD ⇒ PI/LSI theorem must carry `[IsProbabilityMeasure μ]` and `Ergodic` on a `FullMarkovTriple`. Status: open (theorem-level obligation) |
| F6 | MEDIUM | (re-audit) `FullMarkovTriple.ibp_A` is one-sided (A₀ function in the test slot only); the docstring claim "f ∈ A with f, Lf ∈ L² lies in D(L̄) by esa" is unsupported. Bakry–Émery proof also needs Γ(P_t f) ∈ L¹ and ∫ LΓ(P_t f) = 0. | Add the symmetric identity as a field; add 'A stable under smooth ψ' to FullMarkovTriple (do NOT strengthen `MarkovTriple.diffusion`; circle/OU would break). Status: open, needs author decision |
| H1 | MEDIUM | Bridge `isSemigroupOf_tripleSemigroup` is machine-checked non-vacuous only for the Γ=0 triple; `IsMarkovianForm` for the circle needs Fejér convergence in H¹ (~300–500 lines). | Open |
| H2 | MEDIUM | Markov property not in the structure; some triples may have no IsSemigroupOf witness (semigroup_stable vacuous). Same root as F5. | Resolved together with F6. Status: open |
| L1 | LOW | Semigroup.lean docstring claims uniqueness of P under esa; not proved. | Prove or soften. Open |
| E1-E3 | LOW | check_frozen.py: `Frozen/Basic.lean` not hashed (root imports it); subdirectories not scanned; no automatic run (hook/CI). | Open |
