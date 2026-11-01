# BGL correspondence

| BGL | Lean | status |
|---|---|---|
| ergodic Markov triple (ker L̄ = constants; BGL ch. 3/4, numbering unverified) | `MarkovTriple.ErgodicL2` (Frozen/Ergodic.lean) | stated (proposed); non-example `Audit.T2_not_ErgodicL2` proved |
| elementary ergodicity (Γ f f = 0 ⇒ f const) | `MarkovTriple.ErgodicΓ`; `ErgodicL2.toErgodicΓ` proved (Sanity/Ergodic.lean) | stated (proposed); circle ergodicity: `Sanity.Circle.circle_ergodic_statement` (statement only) |
| CD(ρ,n) on extended algebra 𝒜 (BGL §3.3–3.4, unverified) | `FullMarkovTriple.CDFull`, `CDFull.toCD` (Frozen/CDFull.lean) | stated (proposed) |
| Fisher information hypotheses (BGL §5.7) | `MarkovTriple.IsFisherAdmissible` (Frozen/Fisher.lean) | stated (proposed) |
| Markov triple, BGL §3.1 (Def. 3.1.x; numbering unverified): σ-finite μ, non-unital algebra A₀ ⊂ ⋂Lᵖ stable under smooth ψ with ψ(0)=0, pointwise carré du champ, chain rule | `MarkovTriple` (Frozen/MarkovTriple.lean) | stated (proposed), redesigned round 2; instances: `Sanity.trivialTriple`, `Sanity.Circle.circleTriple` (C^∞(𝕋)), `Sanity.Lebesgue.lebesgueTriple` (infinite μ, C_c^∞(ℝ)) |
| Full Markov triple, BGL §3.3–3.4 (unverified): extended unital algebra A stable under all smooth ψ, Γ-calculus on A, ESA of L|A₀ (range criterion), integration by parts in both slots | `FullMarkovTriple` (Frozen/FullMarkovTriple.lean) | stated (proposed); instance only `Sanity.trivialFull` |
| f ∈ A, f, Lf ∈ L² ⇒ f ∈ D(L̄), L̄f = Lf (BGL §3.3–3.4 closure-domain statement, numbering unverified) | `FullMarkovTriple.resolvent_eq` (Hilbert/FullBridge.lean) | proved |
| Markov (first Beurling–Deny) property of the closed form of (E,Γ) | `Hilbert.isMarkovianForm` (Hilbert/MarkovCriterion.lean); `Hilbert.circle_isMarkovianForm` | proved (theorem for every `MarkovTriple`) |
| Friedrichs semigroup P_t = e^{tL} is the symmetric Markov semigroup of a full triple | `Hilbert.isSemigroupOf_full`, `FullMarkovTriple.tripleSemigroup_one` | proved; conservativeness clause vacuous for infinite μ (ERRATA G1) |
