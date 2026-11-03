# Hostile audit: round 15, strong interpolation for every FullTriple (branch HEAD 77b3e89)

Independent auditor. **Result: no soundness defect, no vacuity, no misformalization.** `FullTriple.strongInterpolation : T.CD ρ n → T.StrongInterpolation` is exactly the frozen structure (unmodified; real derivative statement with
explicit integrability); `strong_gradient_bound_unconditional` follows through the frozen `strong_eps`. The unused hypothesis `h ≥ 0` makes the result a strengthening. Lemma 3.3.20 constants (ψ' = 1/(2S), ψ'' = −1/(4S³), K₁ = 1/(2ε), K₂ = 1/(8ε³)),
`ibp_bdd` (truncation genuinely needed: `h ↦ ∫hLG` is not form-continuous since LG ∈ L¹), `lemma3320` (Γ(G_ε) ≤ Γ₂−ρΓ via `reinforced_cd`), the sign and reparametrisation in `strongInterpolation`, and the requirement `Lg ∈ 𝒟(ℰ)` for g = P_τ f (holds for every FullTriple)
were re-derived. `ouFull_strong_gradient_bound_generic = ouFull_strong_gradient_bound := rfl` (OU consistency). No hidden compactness or ρ ≥ 0 (ρ ≥ 0 only in `Main.lean`). Structural: frozen OK; Interp modules recompiled from scratch (0 errors/warnings); axioms standard.
Findings (documentation; ERRATA R15-Interp-audit): false note that the book prints `√(r+ε²) − ε ≤ r` (book: `≤ √r`); stale GAPS rows; 'any ρ, n' phrasing; E6(d) wording on G1/G3/G3'. Medium-depth only: `Nemytskii`, `Pairing`, `Curve` internals (compile-verified, not line-read).
Open: G1 `GradientInterpolation` (not a book statement), G3, G3', weak Cor 3.3.19 (Jensen), ρ<0.
