# Audit: Sphere S³, OUCompact, GoodMeasure/Complete, Conservation (Thm 3.3.23)

Independent hostile audit; prior docs not trusted. Book text: scratchpad `bgl.txt`.
Method: read every field discharge, recomputed the maths by hand, `#print axioms` via a scratch
file outside the repo (`.../scratchpad/aud_ax.lean`), grep for `sorry|native_decide|maxHeartbeats|axiom|set_option`.

## Mechanical results

* grep over `Instances/Sphere`, `Instances/OUCompact`, `Frozen/GoodMeasure.lean`, `Frozen/Complete.lean`,
  `Theory/Conservation`: no `sorry`, `native_decide`, `maxHeartbeats`, `set_option`, or `axiom` declaration
  (only comment/`#print axioms` hits).
* `#print axioms` on all 22 headline declarations (sCompact, sphere_CD_two_three, sphere_Γ_ne_zero, sphere_PI',
  sphere_LS, sphere_gradient_bound, sphere_fisher_decay, the 7 OUCompact analogues,
  ExtendedAlgebra.{conservative_of_complete,isFiniteMeasure_of_complete}, FullTriple.{conservative_of_complete,
  isFiniteMeasure_of_complete,extendedAlgebra}, CompactTriple.{isComplete,hasGradientBound},
  IsGoodMeasure.of_countablyGenerated): all `[propext, Classical.choice, Quot.sound]` only.

## (1) Sphere S³ (`sCompact`): FAITHFUL

Checked by hand:
* Measure: `μZ = (cos)_* ((2/π) sin²θ dθ|_(0,π])`, a probability measure (normalisation proved).
  Law of x₀ on S³ ⊂ ℝ⁴ is ∝ (1−x²)^{(4−3)/2} = √(1−x²), i.e. (2/π)√(1−x²)dx. Correct.
* `L f = F'' + 2cotθ F'` (Laplace–Beltrami on zonal functions of S³; exponent n−1 = 2), `Γ = F'G'`. Correct.
  `ibpZ` proves ∫ g Lf dμ = −∫Γ(f,g) dμ for real, via θ-side integration by parts (not assumed).
* 𝒜 = {f : [−1,1]→ℝ | θ ↦ f(cos θ) is C^∞}: not vacuous (contains x, U_k, constants; `AC_sep` +
  Stone–Weierstrass gives L^p density). Equals zonal-smooth functions (even smooth F = g∘cos). A₀ = 𝒜 as
  non-unital subalgebra; `A_eq := Iff.rfl` is genuinely definitional, `1 ∈ 𝒜₀`.
* Every FullTriple/Standard field is discharged by a real argument: ergodic (spectral, `sphere_ergodic`),
  conservative (`semigroup_one`), pos_detect (smoothTransition test function), connected (energy_zero_const),
  esa (`core_of_invariant` from invariance of 𝒜 under P_t, with `semigroup_cls_mem` proved via C^∞ convergence of
  the eigen-series), diffusion_Γ_A / diffusion_L_A (chain rules `GZ_comp`, `LZ_comp`).
* CD statement `FullTriple.CD ρ n` = Def 3.3.14 (`1 ≤ n ∧ ∀ f∈𝒜, Γ₂(f) ≥ ρΓ(f) + (1/n)(Lf)²`). With n=3, ρ=2:
  recomputed Γ₂(f) = F''² + 2(F'/sinθ)² (Bochner: |Hess|² + Ric(∇f,∇f), Ric = 2 g), and
  Γ₂ − 2Γ − (Lf)²/3 = (2/3)(F'' − cotθ F')² ≥ 0. Correct, pointwise everywhere, all of 𝒜.
  `sphere_CD` for all ρ ≤ 2, n ≥ 3 (incl. ∞) is correct (weaker conditions).
* Lichnerowicz constant: ρ n/(n−1) = 3, `PI((1−1/3)/2) = PI(1/3)`. Correct. LS(1/2,0) is C = 1/ρ. Correct.
* Non-degeneracy: `sphere_Γ_ne_zero` with f = x₀. Real.

Findings:
* [LOW / doc] "Lichnerowicz sharp: λ₁ = 3" (Consequences.lean header) is NOT a Lean theorem. The ingredients exist
  (`LZ_UZ 1`: L U₁ = −3 U₁, with U₁ = 2x ∈ 𝒜) but no statement "PI(c) fails for c < 1/3" or
  "Var(U₁) = (1/3)∫Γ(U₁)" is proved. Fix: either add `sphere_PI_sharp : ¬ PI c` for c < 1/3 (compute
  ∫U₁² = 1, ∫Γ(U₁) = 3 from `ibpZ` and `LZ_UZ`), or reword the docstring to "equality is attained by U₁
  (eigenvalue 3 proved in `LZ_UZ`)". Do not call it a verified sharpness claim.
* [LOW / info] "μ is the S³ coordinate law" is a modelling statement documented in prose; nothing in Lean ties
  `Zon`/`μZ` to the actual round S³ (no Riemannian structure exists in the library). It is correct (see above)
  but should be described as "zonal reduction", which the file header does. No action beyond keeping wording.
* [INFO] The triple is the zonal (SO(3)-invariant) *reduction* of S³, not S³ itself; "S³" claims for
  non-zonal functions are not covered. CD(2,3) for the reduction is the same inequality as for S³ restricted
  to zonal f, so this is honest.

## (2) OUCompact: FAITHFUL (naming caveat)

* E = ℝ, μ = γ = N(0,1), L f = f'' − x f', Γ = f'g'; 𝒜 = 𝒜₀ = ℬ = {f C^∞ bounded, f' Schwartz}. ℬ is an algebra
  (`Bm.mul` via Schwartz bilinLeftCLM), closed under L, Γ, smooth ψ (`Bm.comp`), contains constants and C_c^∞,
  dense in L^p (via C_c^∞), P_t-invariant (Mehler). Non-vacuous: Γ ≠ 0 witnessed by x·bump(x).
* CD(1,∞): Γ₂ = f''² + f'² ≥ Γ. Correct (Bakry–Émery). PI(1), LS(1,0), e^{−2t}: correct constants.
* [LOW / naming] `CompactTriple` here means 𝒜 = 𝒜₀ (BGL Def 3.3.26 as frozen), not topological compactness.
  The OU docstrings say this explicitly. OK. Consequence: `CompactTriple.isComplete` (ζ_k = 1) holds trivially for
  ouBCompact because 1 ∈ ℬ; it says nothing about the *non-compact* OU triple of `Instances/OU` (see (4)).

## (3) Frozen/GoodMeasure.lean, Frozen/Complete.lean, DiffusionTriple.good

* `IsGoodMeasure μ`: ∃ countable family of measurable sets 𝒢 such that every measurable s is μ-a.e. equal to a
  σ(𝒢)-set. Honest and clearly documented as only the "countably generated mod null sets" half of the book's
  "good" notion (the measure-decomposition half is not encoded).
* [LOW] The new field `good` is inert: it is consumed only by `Guards.lean`
  (`DiffusionTriple.isGoodMeasure`); no theorem in the library uses it (no separability-of-L^p proof goes through
  it). For any E with `CountablyGenerated` (all instances) it is automatic, so it is a vacuous strengthening in
  practice: it adds no real constraint on instances. Acceptable, but docs must not claim it "enforces" D1.
* [LOW / usage hazard] The default `good := by exact IsGoodMeasure.of_countablyGenerated _` is an autoParam:
  (a) positional/anonymous-constructor `⟨…⟩ : DiffusionTriple E` now needs an extra argument; (b) generic
  constructions over an abstract `E` without a `CountablyGenerated E` instance fail to elaborate with an
  unhelpful error. The whole library currently builds, so no live breakage; the hazard is for future code
  (e.g. product/quotient triples). Fix: document in the structure docstring (partly done) or provide
  `DiffusionTriple.mk'`.
* `IsComplete` vs Def 3.3.9 (checked against book lines 8328, 9093, and 7541/7792 where the lost glyph is
  explicitly √Γ(ζ_k) = |∇ζ_k| ≤ 1/k):
  - index shift k≥1 → k+1 with k : ℕ: faithful (reindex ζ'_k = ζ_{k+1}); bound √Γ(ζ_k) ≤ 1/(k+1),
    i.e. Γ(ζ_k) ≤ 1/(k+1)², a.e.: faithful to √Γ ≤ 1/k. (Had the book meant Γ ≤ 1/k, the Lean hypothesis would
    be stronger, but 7792 shows √Γ is meant.)
  - "positive" = 0 ≤ a.e. (BGL convention), "increasing" a.e., "ζ_k → 1" a.e.: faithful.
  - Γ taken is the field `T.Γ` on 𝒜₀ (ζ_k ∈ 𝒜₀): faithful. Non-vacuous: `CompactTriple.isComplete`.
  - No implicit extra strength (ζ_k ≤ 1 is derived, `IsExhaustion.le_one_ae`).
* Effect on `DiffusionTriple`: none besides the extra `good` field; all downstream instances still compile.

## (4) Theory/Conservation: SOUND, but narrower than Thm 3.3.23 as stated in the book

* `ExtendedAlgebra D A` is an honest Prop bundle: A₀ ⊂ A, F5, F6 (Γ chain rule), F7 second equality, F8. It omits
  F1–F4 (ideal, positivity detection, A_comp, L(A) ⊂ A) and F9/F10, and requires no integrability; omitting
  hypotheses only makes the theorems stronger, and the proofs do not rely on junk-valued Bochner integrals
  (integrability of Γ(g,η²) comes from the pointwise bound `ΓA_sq_bound`, g·Lξ ∈ L¹ by L²·L²; integral_mono uses
  only the integrable majorant). No hidden strong hypothesis found. Satisfiable: `FullTriple.extendedAlgebra`
  (so sphere/OUCompact give inhabitants). Verified Cauchy–Schwarz for ΓA is derived from F5+F6, not assumed.
* `ExtendedAlgebra.conservative_of_complete` proves S11 for *every* exhaustion sequence u, without S11 as a
  hypothesis, following the book's proof (Duhamel + IBP + gradient bound + dominated convergence, with Young
  `2|η|√Γη ≤ η²+Γη` replacing ‖√Γ ξ‖₁‖√Γ ζ_k‖_∞). The step ℓ = 1 from ∫(1−ℓ)η² = 0 for η = ζ_j is correct.
  `conservative_transfer` reduces from the completeness sequence to arbitrary exhaustions. Faithful to the proof of
  Thm 3.2.6/3.3.23.
* MEDIUM — hypotheses differ from the book's statement. Book Thm 3.3.23: Diffusion Markov Triple with extended
  algebra, completeness + ESA + CD(ρ,∞) ⇒ conservative; ρ>0 ⇒ μ(E)<∞. Lean takes `HasGradientBound D A ρ`
  (Cor 3.3.19's conclusion) as a hypothesis, not ESA + CD. The bridge CD ⇒ gradient bound is
  `FullTriple.hasGradientBound`, which needs the extra hypothesis `GradientInterpolation` (G1); that is proved
  only for compact triples (`compact_gradientInterpolation`) and OU (`ouFull_GradientInterpolation`). So the
  book theorem "CD(ρ,∞) + ESA + complete ⇒ conservative" is NOT proved for a general Full triple; only
  "gradient bound + complete ⇒ conservative". Docstrings state this ("conditional on GradientInterpolation"), but
  CORRESPONDENCE/README must not list Thm 3.3.23 as fully proved. Fix: record as "proved modulo G1 / Cor 3.3.19".
* MEDIUM — `FullTriple.conservative_of_complete` is vacuous as a *consequence*: `FullTriple` extends
  `StandardTriple`, so S11 is already a field; the theorem's conclusion is available without completeness. Only the
  `ExtendedAlgebra` form has content. The docstring in ExtAlgebra.lean notes this for the bundle, but the
  FullTriple wrapper's docstring ("completeness gives conservativeness without S11") is misleading since S11 is
  in the structure. Fix: reword or drop the wrapper; mark as consistency check only.
* MEDIUM — no non-compact witness. `IsComplete` is proved only for CompactTriples (ζ_k = 1). Neither the
  non-compact OU triple (`Instances/OU`, ζ_k = cutoff ψ(x/k)·scale) nor Lebesgue is proved complete, and no
  `ExtendedAlgebra` inhabitant exists that is not already a FullTriple with S11. So the hypothesis combination
  {ExtendedAlgebra, HasGradientBound, IsComplete} is satisfiable but only in cases where the conclusion is
  already a field; the theorem has never been exercised in a regime where it adds information. Fix: prove
  `IsComplete` for OU (ζ_k(x) = χ(x/(k+1)), Γ(ζ_k) ≤ ‖χ'‖²/(k+1)², so scale χ with ‖χ'‖_∞ ≤ 1) and add
  `OU: conservative_of_complete` as an independent re-derivation of `ouB_conservative`.
* `isFiniteMeasure_of_complete` (ρ>0 ⇒ μ finite): proof is the book's (S10 ⇒ P_t u → 0 in L² for infinite μ;
  uniform-in-t estimate K(η)/(ρ(k+1)) via e^{−ρs} decay; then ∫ζ_j² = 0 contradicts ζ_j → 1). Faithful, with
  these differences: (i) ergodicity is an explicit hypothesis `herg` (S10), which the book gets from
  connexity + weak hypo-ellipticity (Prop 3.3.10) — in the FullTriple form `T.ergodic` supplies it, fine;
  (ii) same G1/HasGradientBound caveat as above; (iii) conclusion `IsFiniteMeasure`, then probability by
  `finite_prob`. Note the key use of ρ > 0 is in the strict decay of e^{−ρ s} (integrable on [0,∞)); sign
  conventions (HasGradientBound has e^{−2ρt}) are consistent with Cor 3.3.19.
* [LOW] `AxiomCheck.lean` imports and `#print axioms` lines live in the library tree and execute at build;
  harmless but noisy.

## Severity summary

| # | Sev | Item | Fix |
|---|-----|------|-----|
| 1 | MEDIUM | Thm 3.3.23 proved only with `HasGradientBound` / `GradientInterpolation`, not from CD+ESA | Record as conditional in CORRESPONDENCE; finish G1 in general (other agents' Theory/ work) |
| 2 | MEDIUM | `FullTriple.conservative_of_complete` conclusion already a structure field (S11) | Reword / mark as consistency check |
| 3 | MEDIUM | `IsComplete` proved only for compact triples; no non-compact witness, theorem never non-trivially applied | Prove OU complete with cutoff ζ_k; derive OU conservativeness from it |
| 4 | LOW | "Lichnerowicz sharp" for S³ is prose, not a theorem | Add `¬ PI c` for c<1/3 via U₁, or reword |
| 5 | LOW | `good` field inert (used only by Guards), automatic for all instances; autoParam hazard for generic E | Document; optional `mk'` |
| 6 | LOW | "Compact" = 𝒜=𝒜₀, OU on ℝ is "compact" | Already documented; keep |
| 7 | INFO | Sphere is zonal reduction of S³; μ-is-S³-coordinate-law not formalised geometrically | Keep "zonal reduction" wording |

No CRITICAL or HIGH findings. All definitions faithful (CD, IsComplete, A, μ, Γ, L); no hidden hypotheses,
no axioms beyond the standard three.
