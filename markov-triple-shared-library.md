# A shared Lean library around the Bakry–Émery Markov triple

*Notes from a Claude Code session, 25 October 2026.*

**Repositories examined.** All are shallow clones of each repository's current `main`.
- The three projects: `cutoff-rigidity-diffusions`, `cutoff-fastdiff`, `ginibre-poincare`.
- Scott Armstrong's `MarkovProcess`, `DeGiorgi`, `SuperdiffusionCLT` and `LeanAutoformalizationSkills`, plus READMEs and manifests of his other repositories.
- `RemyDegenne/brownian-motion`.

**Caveat.** File and line references come from automated inventories. They are accurate as pointers, but they are not a substitute for reading the code. The proposed design is a plan, not compiled code.

---

## 0. Summary

**Findings about the three repositories:**

- **Same Lean and Mathlib version everywhere.** All three use Lean `v4.35.0-rc2` with Mathlib `065356127b`, and depend on nothing but Mathlib. A shared library can start at that exact version with no migration pain.
- **`cutoff-rigidity-diffusions` is already most of a Bakry–Émery library**, but tied to weighted Riemannian manifolds and to Gibbs measures on ℝᵈ. It has:
  - Γ, Γ₂ and CD(ρ,∞) (`Statements.lean:218–240`);
  - log-Sobolev from CD(ρ,∞) (`lsi_of_CD`) and Poincaré from CD(ρ,∞);
  - a construction of the diffusion kernel without Brownian motion;
  - Dirichlet forms on a Hilbert space with the Friedrichs extension;
  - total variation, Pinsker, Wasserstein distance with Kantorovich duality, Talagrand, hypercontractivity.
- **`ginibre-poincare` duplicates large parts of it independently:**
  - another log-Sobolev proof under Bakry–Émery, by transfer from the Gaussian log-Sobolev inequality (which it proves from scratch);
  - another construction of the semigroup from a resolvent;
  - its own Brownian motion, entropy, and Γ/Γ₂ on finite-dimensional spaces;
  - a generic Brascamp–Lieb.

  Across the two repositories there are at least three proofs of the Bakry–Émery log-Sobolev inequality and two Friedrichs constructions.
- **`cutoff-fastdiff` has no Markov-semigroup content.** It contributes Wasserstein/Gelbrich formulas, Gaussian and sphere laws, and Stirling and polar-coordinate lemmas.
- **What none of them has:** an abstract Markov triple, that is, a Γ-calculus independent of the space. That is the new core.

**Findings about the surrounding ecosystem:**

- **Armstrong's `MarkovProcess`** is a clean, reusable, sorry-free library on the same Lean and Mathlib version as these projects. It covers kernel semigroups, Hille–Yosida, Feller processes, the strong Markov property and Dynkin's formula.
- **It lacks exactly what a Bakry–Émery library adds:** Γ, Dirichlet forms, reversibility, invariant probability measures, Poincaré and log-Sobolev. Its roadmap does not plan them.
- **Armstrong's Sobolev spaces** exist in four separate copies, all with Lebesgue measure. His diffusions are built from PDE resolvents rather than SDEs.
- **His `LeanAutoformalizationSkills`** documents a workflow suited to a shared library: frozen statements approved by the author, hostile auditor agents, comparator checks.
- **Degenne's `brownian-motion`** has no Itô calculus yet and is on a different Mathlib revision, so it stays out of the core.

**The plan** (§4–§5) follows Bakry–Gentil–Ledoux, Chapter 3. The order is:
1. Extract the low-risk divergences (total variation, Kullback–Leibler, Wasserstein, entropy).
2. Seal the `MarkovTriple` / `FullMarkovTriple` definitions. **The author approves them before any proof work starts.**
3. Merge the two Hilbert-space semigroup constructions.
4. Port the Bakry–Émery proofs from the manifold setting to the abstract triple.
5. Build the instances: Gibbs measures on ℝᵈ, Gaussian/Ornstein–Uhlenbeck, Riemannian, discrete.
6. Add the stochastic layer as a separate library, with an optional bridge to `MarkovProcess`.

The current versions of the projects stay as tagged releases, because the Palomar registration of `ginibre-poincare` is tied to a specific commit.

**Decisions still open** (§7):
- the name of the repository and the Lean namespace;
- whether the triple is a structure or a class (structure recommended);
- whether L is primary and Γ derived, Γ primary and L derived, or both kept as fields tied by integration by parts (both as fields recommended);
- whether finite-dimension CD(ρ,n) is in scope from the start;
- whether to depend on `MarkovProcess` directly or only through the optional bridge (bridge recommended).

**Next step.** Once these decisions are taken, draft the frozen `MarkovTriple` statement files for the author's review.

---

## 1. The question and the first answers

**Question 1.** Is it a good idea to factor part of the three formalizations into general modules, in a new repository that the new versions of the projects would depend on?

**Answer: yes, with one rule.** Before putting code in a new repository, ask whether it belongs in Mathlib. The benefits:
- no duplicated proofs to keep in sync;
- a Mathlib bump is repaired once instead of three times;
- the projects become easier to read;
- the shared library is a staging area for Mathlib PRs.

The costs specific to Lean:
- **Lock-step versions.** Lake needs one toolchain and one Mathlib revision across the whole dependency graph.
- **Two-step changes.** Every change goes into the library first and then into each project.
- **Premature APIs.** Unstable definitions get frozen too early.

**Rule of thumb.** Extract only what at least two projects use and what has stabilized. Mirror Mathlib's paths in a `ForMathlib/` folder, pin dependencies by tag or commit, and run CI.

**Question 2.** The common topics are diffusion processes, stochastic calculus, log-Sobolev inequalities, Bakry–Émery theory and Sobolev spaces.

**Answer.** These are coherent, but not equally mature in the wider ecosystem.
- **Brownian motion and stochastic calculus.** Degenne et al.'s project already covers this. Use it or contribute to it rather than duplicating it.
- **Sobolev spaces.** Several groups are working on these. Keep a thin layer that can be replaced later.
- **Markov semigroups, Γ-calculus, Bakry–Émery, Poincaré and log-Sobolev.** Almost nobody else is working on this. It is the natural core of the new library.

The most important design decision is the formal definition of the Markov triple. Its density and closability requirements should be fields that every instance proves, never axioms.

**Question 3** (the request behind this file). Inventory the three repositories, find out what Scott Armstrong is doing, and build the plan on the Bakry–Émery Markov triple.

---

## 2. What the three repositories contain

All three use Lean `v4.35.0-rc2` with Mathlib `065356127b1d` (the `v4.35.0-rc2` tag). All three depend on nothing but Mathlib. All three use the Palomar `Challenge.lean` / `Solution.lean` layout: the only `sorry`s are in `Challenge.lean`, there are no custom `axiom`s, and the comparator checks that only `propext`, `Classical.choice` and `Quot.sound` are used. Having one shared toolchain is a significant advantage: a common library can start on that exact pin.

### 2.1 `cutoff-rigidity-diffusions` (Chafaï–Fathi, arXiv:2412.15969; about 119k lines, 760 files)

This repository is already, in effect, a Bakry–Émery library, though it is tied to Riemannian manifolds and Euclidean Gibbs measures.

**Γ-calculus on a weighted Riemannian manifold** (`CutoffRigidity/Statements.lean:218–290`):
- `mgrad`, `mlaplacian` (built on Mathlib's `leviCivitaConnection`), `mgenerator V f = Δf − ⟨∇V,∇f⟩`.
- `carre f g = ⟨∇f,∇g⟩`, `carre2 V f = ½ L Γ(f) − Γ(f, Lf)`, `CD ρ V`.
- `IsWeightedVolume`, `IsDiffusionSemigroup` (a Markov kernel family satisfying Chapman–Kolmogorov and Kolmogorov's equation on C_c^∞).

**Bakry–Émery results** (`Riemann/`):
- `weightedBochnerIneq_of_CD`.
- `BEStrong` / `BEPointwise` (`DiffBEMain`).
- `entL` and `LSI` (`DiffTight.lean:113–118`).
- `lsi_of_CD` (`DiffLSI.lean:37`).
- `poincare_of_CD`.
- Interface predicates `WeightedIBP`, `WeightedBochnerIneq`, `WeightedRegular`, `WeightedCutoffs` (`WeightedInterface.lean`). These are proved for complete weighted manifolds.

**Analytic construction of the diffusion kernel, without Brownian motion:**
- `exists_kernel` (`DiffKer10.lean:94`) and uniqueness `bridge_final` (`DiffPerron6.lean:39`).
- `structure CanonicalDiffusion` (`DiffAPI.lean:33`).
- Kuwada duality, which turns a gradient bound into W₂ contraction (`DiffKuw*`).

**Abstract Hilbert-space Dirichlet forms:**
- `structure FormData H` = (dense domain `D`, symmetric nonnegative `A`), from which it builds the Friedrichs extension (`DiffFriedrichs.lean:26`).
- `DirFormData` (a mirror copy in `DiffMarkov.lean`).
- `cfcSemigroup` via continuous functional calculus (CFC) of the resolvent (`DiffCfcSemigroup.lean:148`).
- `positiveResolventOperator` (`GibbsSelfAdjoint.lean:44`).

**Euclidean Gibbs measure μ = e^{−V}dx** (general d and V; curvature is the raw hypothesis `hHess`):
- `gibbsMeasure`.
- `closedGibbsGradient` and the H¹(μ) graph (`GibbsSobolev.lean`).
- A self-adjoint generator, compact embedding, spectral gap, and the heat semigroup as the limit of implicit Euler steps.
- `relativeFisherInformation` and `logSobolev_relativeFisherInformation` (KL ≤ I/2ρ).
- Fisher decay, de Bruijn, Talagrand (via Hopf–Lax), Gross hypercontractivity, Harnack inequalities.
- `cd_euclid_iff` (`Extra/Temperature.lean:93`).

**Divergences and distances:**
- `totalVariationDistance`, Pinsker.
- Relative Lᵖ distance, χ², Hellinger, varentropy.
- Donsker–Varadhan-type variational formulas for Mathlib's `klDiv`.
- W₂ with Kantorovich duality (compact, Euclidean Lipschitz and proper metric cases).
- Gaussian W₂.

**Langevin dynamics:**
- A pathwise SDE with additive noise and no Itô integral (`IsLangevinPathOn`, `langevinSolution`).
- `langevinKernel`, a semigroup that is invariant for the Gibbs measure and Feller.
- The Markov property and the Dynkin martingale (proved via Gaussian averages).
- The OU/Mehler kernel.

**Brownian motion:** `IsEuclideanBrownian`, built on Mathlib's `IsBrownianReal`. It is always a hypothesis; existence is not proved here.

**Duplication inside the repository:**
- Two form structures, `FormData` and `DirFormData`.
- Two Laplacians.
- Three versions of W₂: `squaredWasserstein`, `wasserstein2`, `cost2`.
- Euclidean and "NoBm" copies of the LSI proof.

**Also missing:** a Γ-calculus that does not depend on the manifold. Many definitions carry proof arguments (`hV hprob`) as parameters.

### 2.2 `ginibre-poincare` (arXiv:2608.19358; about 187k lines, 1,727 files, Theorem 1.1 registered on Palomar)

This repository has strong generic pieces, mostly with Ginibre-specific names.

**Entropy:**
- `squareEntropy μ f = ∫f² log f² − (∫f²) log ∫f²` (`Analysis/GinibreEntropy.lean:19`).
- Tensorization over finite products and integrals, L² lower semicontinuity, linearization from LSI to Poincaré.
- The two-point LSI and the Bernoulli-cube LSI.

**Gaussian LSI from scratch**, via Bernoulli variables and the CLT, using Mathlib's `gaussianReal`:
- `gaussianReal_lsi_C2`, scaling, products, `Measure.pi` over any `Fintype`.
- An H¹-completion version, `weightedH1Completion_lsi_of_C2`.
- Transport by Lipschitz maps and quantile transport (`StrongConvex*`).

**Bakry–Émery LSI for κ-convex Gibbs measures** (`AlternativeBakryEmery*`, about 108 files). The proof follows the Langevin endpoint: the endpoint is a Lipschitz function of Gaussian noise, the Gaussian LSI transfers to it, and the time is sent to ∞. Brownian motion is constructed in the repository (Lévy dyadic construction). The headline theorem is stated on `Configuration n`, but the method is generic.

**Γ and Γ₂ on a finite-dimensional space E:**
- `bakryEmeryGibbsGenerator` / `bakryEmeryGibbsCarré`, with integration by parts and an entropy–Fisher identity.
- `bochnerGamma` / `bochnerGammaTwo` with the Bochner identity.
- `OperatorSquareCompletion` (integrated Γ₂ from Poincaré).

**Brascamp–Lieb.** Fully generic, including a weak-derivative version (`CorrespondenceBrascampLieb*`, about 30 files).

**Hilbert-space semigroup from a resolvent:** `resolventGenerator` (self-adjoint, closed, densely defined) and `resolventCfcEvolution` (CFC). This is a second, independent copy of what `cutoff-rigidity-diffusions` has.

**Stochastic layer:**
- `IsBrownianVectorProcess` (Hilbert-valued).
- The augmented Brownian filtration.
- Itô integrals as limits in measure of left Riemann sums, with continuous L² martingale modifications.
- `FiniteDimensionalIto*` Taylor lemmas.
- Finite-grid Girsanov.
- CIR, OU.
- The singular Ginibre SDE: martingale problem, strong Markov property, uniqueness of the invariant law.

**Weak-gradient H¹** as the closure of core pairs `(f, ∇f)` in L²×L², plus mollification and truncation tools. Mathlib's `MemSobolev` appears in two files.

**Missing:**
- An abstract Markov triple, a CD predicate, and abstract Poincaré/LSI predicates. Each inequality is stated inline.
- A Fisher-information definition.
- KL, total variation and W₂.

### 2.3 `cutoff-fastdiff` (Chafaï–Fathi–Simonov, arXiv:2503.11770; about 9k lines)

This repository has no Markov-semigroup, Γ or stochastic content. Its entropy and Fisher information are the Tsallis-type quantities of the porous-medium/fast-diffusion equation, so they are not Γ-based.

Reusable pieces:
- `wassersteinSq` with the affine-map formula and the Gelbrich/Bures formula.
- `densityMeasure`.
- The Laplacian of radial functions.
- Polar coordinates, beta integrals, Stirling bounds.
- Gaussian/sphere projection laws, Student mixtures.
- Bregman/Tsallis convexity.
- `tendsto_iSup_*` helpers for cutoff statements.
- The Mehler density as the m→1 limit.

### 2.4 Duplication across the three projects

| Concept | cutoff-rigidity-diffusions | ginibre-poincare | cutoff-fastdiff |
|---|---|---|---|
| Gibbs / density measure | `gibbsMeasure` | `bakryEmeryNormalizedGibbs`, `bakryEmeryScalarMeasure` | `densityMeasure` |
| Γ, Γ₂, generator | `carre`, `carre2`, `mgenerator` (Riemannian) | `bakryEmeryGibbsCarré`, `bochnerGamma(Two)` (on E) | — |
| Curvature | `CD ρ V`, `hHess` | κ-convexity of `W − κ/2‖x‖²` | — |
| Entropy | `entL`, `klDiv` | `squareEntropy` | Tsallis `relEntropy` |
| Fisher information | `relativeFisherInformation`, `fisherInfo` | inline only | Tsallis `fisherInfo` |
| LSI under BE | `lsi_of_CD` (semigroup), `logSobolev_relativeFisherInformation` (Langevin) | `bakryEmeryConfigurationGibbs_square_lsi` (Gaussian transfer) | — |
| Self-adjoint generator and semigroup | `FormData`, `cfcSemigroup` | `resolventGenerator`, `resolventCfcEvolution` | — |
| H¹(μ) | closure of `compactGibbsGradient` | closure of core pairs | — |
| W₂ | three versions + duality | — | `wassersteinSq` + Gelbrich |
| Brownian vector | `IsEuclideanBrownian` (hypothesis) | `IsBrownianVectorProcess` + existence | — |
| Langevin SDE | `IsLangevinPathOn`, `langevinKernel` | `bakryEmeryLangevinPath` | — |
| OU / Mehler | `ouKernel` | Hermite/OU eigenfunctions | Mehler limit |
| Mollification | `EuclideanL2Mollification*`, `WeightedMollify` | `LebesgueL2Mollification*`, `WeakDerivativeMollification` | — |

There are at least three independent proofs of the Bakry–Émery LSI and two independent Friedrichs/CFC constructions. This is the strongest argument for the library.

---

## 3. The surrounding ecosystem

### 3.1 Scott Armstrong (`scottnarmstrong`)

**`MarkovProcess`** is a real reusable library.
- About 46k lines, with no `sorry` or axioms. It is on the same pin as these projects (Lean and Mathlib `v4.35.0-rc2`, `065356127b`) and depends only on Mathlib.
- It has a consumer guide, `CORRESPONDENCE.md`, `CONTRIBUTING.md` with hard rules, and comparator CI.

Contents:
- `SubMarkovKernelSemigroup α`: `ℝ≥0 → Kernel α α`, with Chapman–Kolmogorov and kernels that are each sub-Markov.
- `IsSubInvariant μ` and contractions on Lᵖ.
- Feller semigroups.
- `StronglyContinuousContractionSemigroup`, generator, resolvent, Hille–Yosida, Trotter–Kato.
- Existence and uniqueness of continuous-path processes, the strong Markov property, Dynkin, Feynman–Kac.
- Killed semigroups, excessive functions.

What it does not have:
- Γ, Dirichlet forms, symmetric or reversible semigroups.
- Invariant *probability* measures (it has only sub-invariance).
- Poincaré, LSI, Itô.
- The multidimensional heat semigroup.

Its roadmap does not plan any of these. Its users are SuperdiffusionCLT, Superdiffusion and GMCExplicitDelta.

**Sobolev.** There are four separate copies:
- `DeGiorgi`: Lean `v4.29`, `HasWeakGrad`, `MemW1p`, `MemH1`.
- `CoarseGraining`: `Homogenization/Sobolev`, `W1pFunction`/`H1Function`, the most complete and on the current pin.
- `EllipticRegularityLean`: `PDEFoundation`, which adds Nash, Nash–Aronson and Prékopa–Leindler.
- `Critical2DKPZ`.

All are Euclidean with Lebesgue measure. None has weighted or Gaussian H¹(μ).

**Diffusions.** His diffusions are built analytically: PDE resolvent → Feller semigroup → law on path space. For example, SuperdiffusionCLT's divergence-form diffusion goes through `IsDivergenceFormFeller`. There are no SDEs, no Itô calculus and no Kipnis–Varadhan.

**Brownian motion.** Three copies: MarkovProcess (1-D), SuperdiffusionCLT (d-D), DOZZ.

**Shared hubs.** `CoarseGraining` (about 570k lines) and `MarkovProcess` are pinned by commit hash. Everything else is duplicated project by project.

**Workflow** (`LeanAutoformalizationSkills`, Claude Code / Codex skills):
- An orchestrator that writes no code and delegates bounded tasks with disjoint write sets.
- **Frozen statements.** An independent audit, then the author's approval, then a one-declaration file plus a manifest checked by a script.
- Hostile auditors who try to refute results; a prover never certifies its own work.
- An errata ledger.
- Mathlib-only comparator challenges and `leanchecker` kernel replay in CI.
- `formalization.yaml` metadata.

These can be installed with `scripts/install_skills.py --agent claude`.

**Relevance.** Armstrong's work and a Bakry–Émery library are complementary. His kernel and C₀-semigroup layer is exactly what the Markov triple sits on, and the Markov triple adds exactly what his layer lacks. His Dynkin martingale (`f(X_t) − ∫Lf` with bracket `2∫Γ(f)`) is the natural meeting point.

### 3.2 Degenne et al., `brownian-motion`

- Lean `v4.35.0` (stable), with a different Mathlib revision (`e91b128`) brought in through `kolmogorov_extension4`.
- Brownian motion is complete, and the core definitions (`IsBrownianReal`, Gaussian processes, independent increments) are already in our pinned Mathlib.
- The stochastic-integral part has 19 `sorry`s, and Doob–Meyer is unfinished. The Itô integral exists only as an axiomatic specification; the Itô isometry and Itô formula are on the roadmap but not yet formalized.
- There are no SDEs, Markov property or generators.

**Conclusion.** Do not make the core library depend on it. Reconsider for a stochastic layer once Itô lands upstream.

### 3.3 Other projects

- **`MarkovSemigroups`** (`mrdouglasny`, listed on Reservoir; the GitHub repository could not be cloned). It covers Markov semigroups, Bakry–Émery ⇒ LSI on manifolds and Gross's LSI, but appears to treat Γ partly through axioms. Its soundness needs checking before it is used for anything.
- **Mathlib (pinned revision).** It has `Analysis/Distribution/{Sobolev,TestFunction,TemperedDistribution}.lean` (so `MemSobolev` exists), `klDiv`, `gaussianReal`/`multivariateGaussian`, `IsBrownianReal`, Kernel composition, CFC, `LinearPMap.closure`, and `leviCivitaConnection`.

---

## 4. Design: the Markov triple first

### 4.1 Mathematical target

The target follows Bakry–Gentil–Ledoux, *Analysis and Geometry of Markov Diffusion Operators* (2014), Chapter 3.

**A Markov triple (E, μ, Γ)** consists of:
- a measure space (E, 𝓕, μ) with μ σ-finite (often a probability);
- an algebra 𝒜₀ of bounded real functions, stable under C^∞ calculus, dense in every Lᵖ(μ);
- a symmetric bilinear Γ : 𝒜₀ × 𝒜₀ → 𝒜₀ with Γ(f,f) ≥ 0;
- the generator L, defined by integration by parts: ∫ g Lf dμ = −∫ Γ(f,g) dμ, with L : 𝒜₀ → 𝒜₀;
- the **diffusion property**: Γ(ψ(f₁,…,f_k), g) = Σ ∂ᵢψ Γ(fᵢ, g).

Derived objects:
- the Dirichlet form ℰ(f) = ∫Γ(f) dμ and its closure (domain 𝒟(ℰ));
- the self-adjoint extension of L (Friedrichs);
- the semigroup P_t = e^{tL} via spectral calculus.

**Standard and full triples** (BGL §3.3–3.4) add:
- an extended algebra 𝒜 ⊇ 𝒜₀ containing constants, where the Γ-calculus still holds;
- essential self-adjointness / "P_t maps a stable class into 𝒜".

This is the hypothesis that makes semigroup interpolation (d/ds P_s(φ(P_{t−s} f)) arguments) legitimate. In Lean it must be a structure with fields that every instance **proves**. On a complete weighted manifold, `cutoff-rigidity-diffusions` already proves the corresponding facts (`WeightedRegular`, `WeightedCutoffs`, `exists_kernel`).

**Curvature and functional inequalities:**
- Γ₂(f) = ½(LΓ(f) − 2Γ(f, Lf)).
- CD(ρ, n): Γ₂(f) ≥ ρΓ(f) + (Lf)²/n.
- Poincaré PI(C): Var_μ(f) ≤ C ℰ(f).
- LSI(C): Ent_μ(f²) ≤ 2C ℰ(f).
- Fisher information I_μ(h) = ∫ Γ(h)/h dμ.
- Talagrand T₂(C).

**Theorems to formalize abstractly:**
1. CD(ρ,∞) ⇒ local inequalities ⇒ LSI(1/ρ) ⇒ PI(1/ρ). Also the gradient bound Γ(P_t f) ≤ e^{−2ρt} P_t Γ(f).
2. PI(C) ⇔ exponential L² decay. LSI(C) ⇔ exponential entropy decay. LSI ⇔ hypercontractivity (Gross).
3. LSI ⇒ T₂ (Otto–Villani), LSI ⇒ Gaussian concentration (Herbst).
4. Tensorization of PI and LSI. Bounded perturbation (Holley–Stroock).

### 4.2 How it should look in Lean (sketch, not compiled)

```lean
/-- Bakry–Gentil–Ledoux Definition 3.1.8. Every analytic requirement is a field to be proved. -/
structure MarkovTriple (E : Type*) [MeasurableSpace E] where
  μ        : Measure E
  [sf      : SigmaFinite μ]
  A₀       : Subalgebra ℝ (E → ℝ)            -- test functions
  Γ        : (E → ℝ) → (E → ℝ) → (E → ℝ)
  Γ_symm   : ∀ f g, Γ f g = Γ g f
  Γ_bilin  : ...                              -- bilinear on A₀
  Γ_nonneg : ∀ f ∈ A₀, 0 ≤ Γ f f
  L        : (E → ℝ) → (E → ℝ)
  L_mem    : ∀ f ∈ A₀, L f ∈ A₀
  ibp      : ∀ f ∈ A₀, ∀ g ∈ A₀, ∫ x, g x * L f x ∂μ = -∫ x, Γ f g x ∂μ
  dense    : ∀ p, 1 ≤ p → p < ∞ → Dense {u : Lp ℝ p μ | ∃ f ∈ A₀, u =ᵐ[μ] f}
  diffusion: ...                              -- chain rule for smooth ψ

namespace MarkovTriple
def Γ₂ (T : MarkovTriple E) (f : E → ℝ) : E → ℝ := fun x => (T.L (T.Γ f f) x - 2 * T.Γ f (T.L f) x) / 2
def CD (T) (ρ : ℝ) (n : ℝ≥0∞) : Prop := ∀ f ∈ T.A₀, ∀ᵐ x ∂T.μ, ρ * T.Γ f f x + (T.L f x)^2 / n ≤ T.Γ₂ f x
def energy (T) (f) : ℝ := ∫ x, T.Γ f f x ∂T.μ
def Ent (μ) (f) : ℝ := ∫ x, f x * log (f x) ∂μ - (∫ x, f x ∂μ) * log (∫ x, f x ∂μ)   -- unify entL / squareEntropy
def PoincareIneq (T) (C : ℝ) : Prop := ∀ f ∈ T.A₀, variance f T.μ ≤ C * T.energy f
def LogSobolevIneq (T) (C : ℝ) : Prop := ∀ f ∈ T.A₀, Ent T.μ (f^2) ≤ 2 * C * T.energy f
end MarkovTriple

/-- BGL §3.3–3.4: the extra hypotheses that make semigroup interpolation legitimate. -/
structure FullMarkovTriple (E) [MeasurableSpace E] extends MarkovTriple E where
  A        : Subalgebra ℝ (E → ℝ)    -- extended algebra, contains A₀ and constants
  ...                               -- P_t (stable class) ⊆ A, essential self-adjointness, ...
```

Points to decide when sealing these definitions:
- **Where Γ and L live.** `E → ℝ` with properties restricted to 𝒜₀, which is convenient for instances, or functions out of `A₀`, which is safer.
- **How "a.e." is handled.** Γ₂ ≥ ρΓ pointwise or μ-a.e. Instances usually have it pointwise.
- **Domain of the inequalities.** Inequalities on 𝒜₀ plus a separate theorem extending them to 𝒟(ℰ) by closure. This is what both `cutoff-rigidity-diffusions` (`testSub`) and `ginibre-poincare` (core pairs → closure) already do.
- **Time type.** `ℝ≥0`, to match `MarkovProcess` and Mathlib kernels.
- **The semigroup.** Defined through the Hilbert layer (§4.3), and identified with kernels only when kernels exist.

### 4.3 Layers and where the code comes from

| Layer | Content | Main sources |
|---|---|---|
| `Divergences` | `Ent`, KL bridge (`klDiv`), TV, Pinsker, relative Lᵖ, χ², Hellinger, varentropy, W₂ (one definition on `PseudoEMetricSpace`), couplings, Kantorovich duality, Gaussian W₂ / Gelbrich, entropy tensorization | CR `TotalVariation`, `Pinsker`, `RelativeLpDistance`, `KL*`, `Transport*`, `*TransportDuality*`; GP `squareEntropy`, `*EntropyTensorization`, `EntropyL2Closure`; CF `wassersteinSq_map_affine'`, `wassersteinSq_elliptic'` |
| `Hilbert` | Symmetric nonnegative form → Friedrichs extension → resolvent → CFC semigroup; self-adjoint generator from resolvent; spectral gap ⇔ L² decay | CR `FormData`/`DirFormData` (merge), `cfcSemigroup`, `positiveResolventOperator`; GP `resolventGenerator`, `resolventCfcEvolution`, `OperatorSquareCompletion` |
| `MarkovTriple` | `MarkovTriple`, `FullMarkovTriple`, Γ₂, CD, Dirichlet form and its domain, P_t, Markov property of P_t, invariance and symmetry of μ | new, abstracted from CR `Riemann/WeightedInterface`, `DiffAPI` |
| `FunctionalInequalities` | PI, LSI, Fisher information, CD ⇒ gradient bounds ⇒ LSI ⇒ PI, decay equivalences, hypercontractivity, Herbst, T₂, tensorization, Holley–Stroock, Brascamp–Lieb | CR `DiffBEMain`, `DiffLSI`, `LangevinGrossHypercontractivity`, `Talagrand`, `HopfLax*`; GP `CorrespondenceBrascampLieb*`, `SquareEntropyLinearization` |
| `Instances` | (a) Euclidean Gibbs e^{−V}dx; (b) Gaussian / OU (Mehler, Hermite); (c) weighted Riemannian manifold; (d) discrete: two-point, cube, products | (a) CR `Gibbs*`, `GibbsSobolev*`, `cd_euclid_iff`, GP `bakryEmeryGibbs*`; (b) CR `OUKernel`, GP `GaussianLSI*`, `HermiteOrnsteinUhlenbeck`; (c) CR `Riemann/*`; (d) GP `TwoPointLSI`, `BernoulliCubeLSI` |
| `Stochastic` (separate `lean_lib`) | Brownian vector processes and existence, augmented filtration, Riemann-sum Itô integrals, Langevin SDE for κ-convex V, Langevin kernel = P_t, Dynkin martingale, LSI via Gaussian transfer | CR `Brownian`, `Langevin*`, `LangevinDynkinMartingale`; GP `AlternativeBakryEmeryBrownian*`, `IsBrownianVectorProcess`, `BrownianIntegral*`, `FiniteDimensionalIto*`, `bakryEmeryLangevinPath` |
| `Bridge/MarkovProcess` (optional `lean_lib`) | Markov triple with kernel representation → `SubMarkovKernelSemigroup`; invariant measure ⇒ `IsSubInvariant` | Armstrong's `MarkovProcess` |
| `Analysis` / `ForMathlib` | Polar coordinates, beta integrals, Stirling, mollification, truncation, radial Laplacian, Gaussian/sphere laws, `tendsto_iSup_*` | CF `Radial`, `Sphere`, `Asymptotics`, `PDE`; CR/GP mollification files |

*Abbreviations: CR = `cutoff-rigidity-diffusions`, GP = `ginibre-poincare`, CF = `cutoff-fastdiff`.*

**Sobolev spaces stay out of the core.** In the Markov-triple approach, the Sobolev space is the domain 𝒟(ℰ), obtained abstractly by closure. Identifying it with a concrete space such as H¹(e^{−V}dx) is a theorem about one instance. Unweighted ℝⁿ Sobolev theory and elliptic regularity (CR `DiffSobolevRn*`, `DiffEllipticRn*`) are only needed to construct the Riemannian instance. They should go into an `Instances/Riemann/Regularity` folder, kept small, and be replaced by Mathlib's `MemSobolev` and by the Armstrong / van Doorn–Nuccio material once it settles.

**Dependency rule.**
- `Divergences`, `Hilbert`, `MarkovTriple` and `FunctionalInequalities` depend only on Mathlib.
- `Stochastic` and `Bridge` are separate Lake libraries in the same repository, so trouble in either cannot break the core.

---

## 5. Migration plan

**Phase 0. Repository and conventions.**
- Pin Lean and Mathlib to `v4.35.0-rc2` / `065356127b1d`, the same as the three projects and `MarkovProcess`.
- Add a `CORRESPONDENCE.md` that maps BGL numbered results (and Ané et al., Villani where relevant) to Lean names and status.
- Adopt the comparator / `Challenge.lean` pattern already used in the three projects, frozen statements, and Armstrong's `CONTRIBUTING` hard rules (no `maxHeartbeats` increases in library code, at most 1,500 lines per file, an axiom check on every public theorem).
- Mathlib bump policy: tag the library at each bump, and the projects pin tags.

**Phase 1. Low-risk extraction with no design decisions: `Divergences` and `Analysis`.**
- Merge the three W₂ definitions, TV, Pinsker, KL bridges, Gelbrich, entropy and its tensorization.
- Rewrite the corresponding files in the projects as thin wrappers.

**Phase 2. Seal the Markov-triple definitions.**
- Write `MarkovTriple`, `FullMarkovTriple`, Γ₂, CD, PI, LSI, Fisher information and P_t as a one-declaration-per-file frozen surface.
- Have independent audits check them against BGL.
- **The user approves the statements** before any proof work begins.

**Phase 3. `Hilbert`.** Merge CR `FormData`/`cfcSemigroup` with GP `resolventGenerator`/`resolventCfcEvolution` into one construction: form → self-adjoint operator → semigroup.

**Phase 4. Abstract Bakry–Émery theory.**
- Port the semigroup-interpolation proofs of CR `DiffBEMain`/`DiffLSI` from the manifold setting to `FullMarkovTriple`.
- Then add the decay equivalences, hypercontractivity, Herbst, T₂ and tensorization.

**Phase 5. Instances.**
- Euclidean Gibbs and Gaussian/OU first: the cheapest check that the abstraction can be instantiated.
- Then the weighted complete Riemannian manifold, by repackaging CR `Riemann/*`.
- Then the discrete examples.
- Each instance proves the `FullMarkovTriple` fields, so the abstract theorems apply to it.

**Phase 6. Stochastic layer and bridges.**
- Merge the two Brownian-vector and Langevin developments.
- Prove that the Langevin kernel equals P_t of the Gibbs triple (CR `langevinCompactTestLp_eq_gibbsHeatSemigroup` already does this concretely).
- Add the optional `MarkovProcess` bridge.

**Phase 7. New versions of the three projects.**
- Each `require`s the library at a tag, deletes duplicated files and keeps the paper-specific material.
- **Keep the current versions as tagged releases.** The Palomar registration of `ginibre-poincare` Theorem 1.1 is tied to a specific commit, and the comparator challenges must still verify. If a project's `Challenge.lean` is rebuilt from scratch on Mathlib alone, it does not need to change; only `Solution.lean` changes.

**Mathlib upstreaming candidates**, to be submitted as the material matures:
- total variation and Pinsker;
- W₂ and couplings;
- `Ent`, and the LSI and tensorization for the Gaussian, two-point and Bernoulli-cube cases;
- Brascamp–Lieb;
- the Friedrichs extension;
- the Gaussian/sphere projection laws.

---

## 6. Coordination with Scott Armstrong

**Topics to raise:**
1. Whether he would welcome a symmetric / Dirichlet-form / Γ layer **next to** `MarkovProcess`, a sibling package that the Markov-triple library owns. It would give his divergence-form generators a variational description.
2. A single multidimensional heat / OU semigroup and a single Brownian vector process, replacing the current copies: three in his repositories (`MarkovProcess` 1-D, `SuperdiffusionCLT` d-D, `DOZZ`) and two in these projects.
3. A shared Mathlib bump schedule. Both ecosystems are currently on `v4.35.0-rc2`.

**Design compatibility to keep now, at no cost:**
- `ℝ≥0` time.
- `ProbabilityTheory.Kernel` families with `Kernel.comp` for the Chapman–Kolmogorov law.
- Real Lᵖ spaces.

---

## 7. Open decisions for the author

- **Name** of the repository and of the Lean namespace (e.g. `MarkovTriple`, `BakryEmery`, `DiffusionOperators`).
- **Whether `MarkovTriple` is a `structure` (data) or a `class` on (E, μ).** A structure is recommended, because several triples on the same space are common: generators at different temperatures, and products.
- **Whether L is primary and Γ derived, or Γ primary and L derived** (BGL takes Γ and L together and requires integration by parts). Recommended: both are fields, with integration by parts as an axiom of the structure.
- **Whether CD(ρ, n) with finite n is in scope from the start**, or only CD(ρ, ∞).
- **Whether to depend on `MarkovProcess`** directly or through the optional bridge only. The bridge is recommended for now.

---

## Sources

- Degenne et al., *Formalization of Brownian motion in Lean*, arXiv:2511.20118 — <https://arxiv.org/html/2511.20118v2>
- Degenne, *Towards stochastic calculus in Lean* (Cambridge talk) — <https://www.dpmms.cam.ac.uk/node/64847>
- *A Machine-Checked Itô Calculus for Brownian Motion*, arXiv:2606.15089 — <https://huggingface.co/papers/2606.15089>
- *A Formally Verified Library of Mathematical Finance in Lean 4*, arXiv:2606.01356 — <https://arxiv.org/pdf/2606.01356>
- Armstrong–Kempe, *Formalization of De Giorgi–Nash–Moser Theory in Lean*, arXiv:2604.05984 — <https://arxiv.org/pdf/2604.05984>
- DeGiorgi on Reservoir — <https://reservoir.lean-lang.org/@scottnarmstrong/DeGiorgi>
- *Formalizing Schwartz functions and tempered distributions*, arXiv:2510.24060 — <https://arxiv.org/html/2510.24060v1>
- MarkovSemigroups on Reservoir — <https://reservoir.lean-lang.org/@mrdouglasny/MarkovSemigroups>
- GitHub: `djalilchafai/{cutoff-rigidity-diffusions,cutoff-fastdiff,ginibre-poincare}`, `scottnarmstrong/{MarkovProcess,DeGiorgi,SuperdiffusionCLT,LeanAutoformalizationSkills,CoarseGraining,EllipticRegularityLean}`, `RemyDegenne/brownian-motion`
- D. Bakry, I. Gentil, M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*, Springer, 2014
