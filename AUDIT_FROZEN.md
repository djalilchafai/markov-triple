# AUDIT_FROZEN (hostile audit of MarkovTriple/Frozen/*)

Lean evidence: `MarkovTriple/Audit/TwoPoint.lean` (compiles with `lake env lean`, no sorry).
BGL page/number citations below are from memory and marked (unverified) unless stated; no copy of the book was available.

## F1 [HIGH] No ergodicity/connectedness: CD(rho,inf) with rho>0 does NOT imply PI/LSI
Files: Frozen/MarkovTriple.lean:24-73, Frozen/CD.lean:21, Poincare.lean:15, LSI.lean:16 (FullMarkovTriple.lean:21-63 also).
Counterexample (formalised, `Audit/TwoPoint.lean`): E = Bool, mu uniform probability, L = 0, Gamma = 0, i.e. `Sanity.trivialFull`
(a `FullMarkovTriple`, not just a `MarkovTriple`). Then
 * `T2_CD : ∀ rho, T2.CD rho ∞` (also every finite n>0), e.g. rho = 1 or 10^6;
 * `T2_not_PI : ∀ C, ¬ PoincareIneq C`, `T2_not_LSI : ∀ C, ¬ LogSobolevIneq C` (test f = indicator of `true`: energy 0, variance 1/4, Ent(f^2) = (log 2)/2 > 0).
Same phenomenon for any disjoint union of two Gaussian-like components (e.g. two intervals with C_c^infty-plus-locally-constant test algebra).
So the theorems "CD(rho,inf), rho>0 => LSI(1/rho)" (Bakry-Emery), "CD(rho,n) => Lichnerowicz PI" are FALSE as stated over these structures.
BGL's theorems carry an ergodicity / "kernel of L = constants" / Gamma(f)=0 => f const hypothesis (unverified where exactly: ch. 4 and 5.7 hypotheses and the definition of ergodic Markov triple in ch. 3). The frozen structure has no such field.
Fix: do not put it in the structure (many triples are non-ergodic); add a predicate, e.g.
`Ergodic T := ∀ f ∈ T.A₀, T.Γ f f = 0 → ∃ c, f =ᵐ[T.μ] fun _ => c` (or, better for the semigroup proof, "ker of the L²-closure of L is the constants" for a FullMarkovTriple), and require it in every CD => PI/LSI theorem. Note a.e.-version of the Gamma-form is weaker than the closure-kernel form; the Bakry-Emery proof needs P_t f -> ∫f in L2, i.e. the latter. State the theorem with the closure form.

## F2 [MEDIUM] CD is only imposed on A₀, not on the extended algebra A
FullMarkovTriple.lean (no CD-related field), CD.lean:21-23. Semigroup proofs apply Gamma_2 >= rho Gamma to P_t f ∈ A (semigroup_stable), which need not lie in A₀, but `CD` quantifies only over `T.A₀`. Nothing in `FullMarkovTriple` transfers the inequality to A. I could not build a counterexample (unverified that it is false), but the gap is a likely obstruction to the proof. In BGL the CD condition is stated on the extended class in the full-triple setting (unverified numbering). Fix: add `CD_A`-style definition `FullMarkovTriple.CD` over `A`, or a field/lemma "CD on A₀ ⇒ CD on A", used by the theorems.

## F3 [MEDIUM, scope/faithfulness] Constants in A₀ forces mu finite
MarkovTriple.lean:30 (Subalgebra), :38 (memLp). Excludes Lebesgue measure on R^n, hyperbolic space, any infinite-measure Markov triple that BGL's sigma-finite Def 3.1.1 admits (BGL ask stability under smooth Phi with Phi(0)=0 for this reason; unverified). Author already notes this (FROZEN_REVIEW 2). Not a vacuity problem; PI/LSI need probability anyway. Suggest NonUnitalSubalgebra + constants only in the full triple if infinite-measure results (CD(0,n) volume growth, heat kernel) are ever wanted.

## F4 [LOW] Fisher information junk values
Fisher.lean:14-15. `fisherInfo T h` has no hypothesis on h. For h ∈ A₀ with sign changes, `Γ h h / h` can be non-integrable (e.g. OU, h = x: integrand 1/x on the real line) and Bochner returns 0, a silently wrong value; for h<0 it is negative. Fine on h ≥ 0 in A₀ (Glaeser-type bound) but not enforced. Fix: any theorem using it must assume `∀ x, 0 < h x` (or ≥ 0 plus Integrable), or define as `ENNReal`/lintegral of `ofReal`.

## F5 [LOW] Weak/unchecked points (no counterexample found)
 * Diffusion guard `ψ(f) ∈ A₀` (MarkovTriple.lean:67-73): does not make genuine instances impossible (true diffusion generators satisfy the unguarded chain rule, so OU/polynomials, torus/trig polynomials are instances), and on a finite set it forces L = Γ = 0 (indicators f give Γ(f,g) = 2fΓ(f,g)). I found no pathological instance exploiting it beyond F1.
 * Null-set junk: pointwise Gamma_nonneg/carre_du_champ is stronger than BGL's a.e. but harmless; I checked that f = 0 a.e., f ∈ A₀ implies Γ f f = 0 a.e. (ibp), Γ(f,g)=0 a.e. (pointwise Cauchy–Schwarz from bilinearity+nonneg) and L f = 0 a.e. (ibp + density), so L,Γ are well defined on a.e.-classes. No flaw.
 * `μ = 0` is a valid MarkovTriple (and CD holds for all rho,n); harmless since PI/LSI demand IsProbabilityMeasure.
 * Chain rule at k = 0 gives L 1 = 0, Γ(1,·) = 0 as claimed (ψ ≡ 1 is `ContDiff`; `Fin 0 → ℝ`).
 * `ContDiff ℝ (⊤:ℕ∞)` is C^∞ (not analytic), as intended. `p=0` in `memLp` harmless.
 * Variance: Mathlib `variance f μ = (evariance f μ).toReal`; for f ∈ A₀ ⊂ L², finite, no toReal-of-∞ junk. Ent(f^2), f ∈ A₀: f² log f² is integrable (|t log t| ≤ C(1+|t|^{3/2})... , all moments), so no junk in LSI. Energy integrand Γ f f ∈ A₀ ⊂ L¹: no junk.
 * CD: `(n⁻¹).toReal` is correct for n = ∞ (0) and finite n>0; `n = 0` excluded. n<1 allowed (BGL, n ≥ 1 unverified) – only makes CD(rho,n) stronger-looking for small n, no false theorem found.
 * esa: range criterion is legitimate: L|A₀ symmetric (ibp + Γ_symm), −L ≥ 0 (Γ_nonneg), densely defined; for a semibounded symmetric operator e.s.a. ⇔ Ran(−L+λ) dense for one λ>0 (Reed–Simon X.26 / corollary). `{u | ∃ f ∈ A₀, u =ᵐ f − L f}` is Ran(1−L) in L²(R-Hilbert space) — real vs complex immaterial for this criterion. ok.
 * IsSemigroupOf: generator of such P is self-adjoint, contains L|A₀, hence equals closure of L|A₀ when esa holds: uniqueness claim correct. Symmetric+positive+P1=1 ⇒ L²-contraction, so omission of contractivity is fine.
 * FullMarkovTriple is stated outside `namespace MarkovTriple` like MarkovTriple (consistent). `sigmaFinite` is a non-instance field: users must `haveI`. Redundant with finiteness (F3).
 * Gamma₂ docstring numbering (BGL 1.4.2), CD (1.16.1), Ent (5.1.1), LSI (5.1.1/5.1.3), Fisher (5.7), PI (4.2.1), Def 3.1.8: all unverified by me. LSI form Ent(f²) ≤ 2C∫Γ(f) is equivalent (via f ↦ √f) to Ent(f) ≤ (C/2) I(f), Gaussian C=1: mathematically consistent.

## Verdicts
 * PartialDeriv: ok. Gamma2: ok. Energy: ok. Ent: ok (as intended for f² with f ∈ A₀). Poincare: ok as a definition (see F1 for use). LSI: ok as a definition (F1 for use).
 * CD: ok as a definition; needs F2 for full triples.
 * Fisher: needs fix/hypothesis (F4).
 * Semigroup: ok.
 * MarkovTriple: ok as a definition (F3 scope note); no contradiction found; nontrivial satisfiability (L≠0) argued on paper only (OU/polynomials; not formalised).
 * FullMarkovTriple: needs fix (F1 at theorem level, F2).
