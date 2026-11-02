# BGL/Theory/Compact: what is proved for compact triples (A = A₀), what remains

Everything below is proved with only `propext`, `Classical.choice`, `Quot.sound` (see `AxiomCheck.lean`),
from F1–F10 of `CompactTriple` (the `esa` field is not used).  Book paraphrased: Def. 3.3.26 and the
remark that for compact triples gradient bounds are much easier.

## Proved (unconditional, every `CompactTriple E`)

* `compact_gradientInterpolation : C.toFullTriple.GradientInterpolation` (G1 of `Theory/GAPS.md`).
* `compact_entropyInterpolation : C.toFullTriple.EntropyInterpolation` (G3 of `Theory/GAPS.md`).
* Hence unconditionally on compact triples:
  `compact_gradient_bound` (`CD(ρ,n) ⇒ Γ(P_t f) ≤ e^{-2ρt} P_t Γ(f)`, weak form),
  `compact_logSobolev` (`CD(ρ,n)`, `ρ>0` ⇒ `LS(1/ρ,0)`), `CompactTriple.fisher_decay`
  (`I(s) ≤ e^{-2ρs} I(0)`, any `ρ ∈ ℝ`), `CompactTriple.fisher_antitone` (`ρ ≥ 0`).
* Circle (`CD(0,∞)`): `Circle.circle_gradient_bound` (`Γ(P_t f) ≤ P_t Γ f`), `Circle.circle_entropy_deriv`
  (`e' = -I`), `Circle.circle_fisher_antitone` (`I' ≤ 0`).

## Method (files)

* `Product.lean`: trilinear form `tri a b c = ∫ abc` on `L²` and its Leibniz rule for `L²`-differentiable,
  uniformly essentially bounded curves (no `L^∞` regularity of derivatives needed).
* `Flow.lean`: orbit `s ↦ P_s[ψ]` is `L²`-differentiable (`d/ds = P_s[Lψ]`, `s>0`), continuous, bounded by
  `‖ψ‖_∞` (sub-Markov), and `L (Pt s ψ) = P_s[Lψ]` a.e. (`L_Pt`; uses `P_s 𝒜₀ ⊂ 𝒜₀` and commutation of
  `P_s` with the generator).
* `Algebra.lean`: `2∫ k Γ₂(g) = ½∫L²k g² − 2∫Lk g Lg + ∫k(Lg)² + ∫k g L²g` by symmetric integration by parts on `𝒜₀`.
* `Gradient.lean`: `Φ(s) = ∫P_s h Γ(P_{t-s}f) = ½tri(L K_s,G_s,G_s) − tri(K_s,G_s,LG_s)`, differentiated.
* `Chain.lean`, `Smooth.lean`: `d/dr ∫F(G_r)V_r` for smooth compactly supported `F` (Taylor remainder in `L¹`
  against the bounded factor; `F∘G_r` is not `L²`-differentiable in general).
* `Entropy.lean`: `e = ∫Θ(g_s)`, `I = −∫Λ(g_s) L g_s`, `I' = −2J` from the one-variable chain rules for `L`
  (`L_comp`, from F6 with `k=1`) and `Γ` plus F7 (no Leibniz rule for `Γ` needed).

## Not done

* (Update) `ρ > 0` witness with `CD(1,∞)`: `Instances/OUCompact/` (Ornstein–Uhlenbeck with `𝒜 = 𝒜₀ = ℬ`; space not compact, see ERRATA BGL-V1). Still no genuinely compact space and no finite-`n` witness.
* (Original note) `ρ > 0` witnesses.  No compact triple with `ρ > 0` is built (the round sphere `S²` would need the whole
  Legendre/`SO(3)` smooth structure and the `𝒜₀`-invariance F8; judged not cheap).  The circle gives only
  `ρ = 0`, so `compact_logSobolev` is not instantiated on a concrete space here (the machinery is proved for all
  compact triples with `CD(ρ,n)`, `ρ>0`).
* Strong (√) gradient bound `Γ(P_t f) ≤ e^{-2ρt}(P_t√Γ f)²` (needs the Hessian inequality, as in `GAPS.md` G1).
* Non-compact triples: G1, G3 remain hypotheses there (`Theory/GAPS.md`).
