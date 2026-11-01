# BGL correspondence

| BGL | Lean | status |
|---|---|---|
| ergodic Markov triple (ker L̄ = constants; BGL ch. 3/4, numbering unverified) | `MarkovTriple.ErgodicL2` (Frozen/Ergodic.lean) | stated (proposed); non-example `Audit.T2_not_ErgodicL2` proved |
| elementary ergodicity (Γ f f = 0 ⇒ f const) | `MarkovTriple.ErgodicΓ`; `ErgodicL2.toErgodicΓ` proved (Sanity/Ergodic.lean) | stated (proposed); circle ergodicity: `Sanity.Circle.circle_ergodic_statement` (statement only) |
| CD(ρ,n) on extended algebra 𝒜 (BGL §3.3–3.4, unverified) | `FullMarkovTriple.CDFull`, `CDFull.toCD` (Frozen/CDFull.lean) | stated (proposed) |
| Fisher information hypotheses (BGL §5.7) | `MarkovTriple.IsFisherAdmissible` (Frozen/Fisher.lean) | stated (proposed) |
