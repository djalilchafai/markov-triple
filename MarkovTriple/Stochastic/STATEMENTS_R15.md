# Round 15 (stochastic layer, "full fix"): frozen target statements

Written BEFORE any proof (Armstrong method).  Later changes only by a logged erratum in `ERRATA.md`.
Namespace `MarkovTriple.Stochastic` (`.OU`, `.Circle` for instances).  All existing Stochastic files are untouched.
`E` is a measurable space, `T : DiffusionTriple E`; `P_t = T.semigroup t` is the Friedrichs `L²(T.μ)` semigroup;
"`rep`" is the field of `KernelRepresentation`/`KernelBridge`:
`rep := ∀ t g, Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ hL : MemLp g 2 T.μ,
  (T.semigroup t (hL.toLp g) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(κ t x)`.

## S1. Generic extension (file `RepExtend.lean`)  — classical: contractivity by Jensen/Cauchy–Schwarz + invariance, density

```
theorem kernelRep_of_dense {T : DiffusionTriple E} (κ : ℝ≥0 → Kernel E E)
    (hsub : ∀ t x, κ t x Set.univ ≤ 1)
    (hinv : ∀ t, T.μ.bind (κ t) ≤ T.μ)
    (D : Set (E → ℝ))
    (hDmeas : ∀ f ∈ D, Measurable f) (hDbdd : ∀ f ∈ D, ∃ C, ∀ x, |f x| ≤ C)
    (hDL : ∀ f ∈ D, MemLp f 2 T.μ)
    (hDdense : Dense {u : Lp ℝ 2 T.μ | ∃ f ∈ D, (u : E → ℝ) =ᵐ[T.μ] f})
    (hD : ∀ t, ∀ f (hf : f ∈ D),
      (T.semigroup t ((hDL f hf).toLp f) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂(κ t x)) :
    ∀ (t : ℝ≥0) (g : E → ℝ), Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ hL : MemLp g 2 T.μ,
      (T.semigroup t (hL.toLp g) : E → ℝ) =ᵐ[T.μ] fun x => ∫ y, g y ∂(κ t x)
```
Also `lintegral_sq_kernel_le` : `∫⁻ ofReal((∫ h dκ_x)^2) dμ ≤ ∫⁻ ofReal(h^2) dμ` under `hsub`, `hinv`
(L²(μ)-contractivity of `h ↦ κ h`).

```
def KernelBridge.ofTestClass {T} (S : SubMarkovKernelSemigroup E) (hinv : S.IsInvariant T.μ)
    (h : IsTestClassRep T S.κ) : KernelBridge T
```
(`IsTestClassRep` = representation on `T.A₀`; uses `T.measurable/bounded/memLp/dense` for p = 2.)

## S2. OU (file `OUFull.lean`)

```
noncomputable def ouKernelBridge : KernelBridge ouDiff        -- toSubMarkovKernelSemigroup = ouSemigroup
theorem ouKernelBridge_κ : ouKernelBridge.κ = ouKernel
theorem ouKernelBridge_isMarkov : ouKernelBridge.toSubMarkovKernelSemigroup.IsMarkov
noncomputable def ouKernelRepresentation : KernelRepresentation ouDiff  -- := ouKernelBridge.toKernelRepresentation
theorem ou_rep_full : ∀ t g, Measurable g → (∃ C, ∀ x, |g x| ≤ C) → ∀ hL : MemLp g 2 γ,
    (Pt t (hL.toLp g) : ℝ → ℝ) =ᵐ[γ] fun x => ∫ y, g y ∂(ouKernel t x)
```
(Plus joint measurability `Measurable fun p : ℝ≥0 × ℝ => ouKernel p.1 p.2` for the Armstrong-shaped data, S5.)

## S3. Circle (file `Circle.lean`, namespace `MarkovTriple.Stochastic.Circle`), `𝕋 = AddCircle (1:ℝ)`, `cT : DiffusionTriple 𝕋`, `μ₀` Haar probability

Wrapped Gaussian (periodised heat kernel, generator `L = d²/dx²`, so `e^{-(2πn)² t}` on `e_n`):
`circleKernel t : Kernel 𝕋 𝕋`, `circleKernel t x = (gaussianReal 0 (2 t)).map (fun z : ℝ => x + (z : 𝕋))`.
```
instance : IsMarkovKernel (circleKernel t)
theorem circleKernel_zero : circleKernel 0 = Kernel.id
theorem circleKernel_comp (s t) : circleKernel t ∘ₖ circleKernel s = circleKernel (s + t)     -- exact CK
theorem circleKernel_invariant (t) : μ₀.bind (circleKernel t) = μ₀
theorem circleKernel_mode (t n x) : ∫ y, mc n y ∂(circleKernel t x) = Real.exp (-lam n * t) * mc n x   -- and ms
theorem circleKernel_rep_trigSpan : ∀ t f, f ∈ trigSpan → ∀ u : Lp ℝ 2 μ₀, u =ᵐ f →
    (cT.semigroup t u : 𝕋 → ℝ) =ᵐ[μ₀] fun x => ∫ y, f y ∂(circleKernel t x)
noncomputable def circleKernelBridge : KernelBridge cT
```
(`rep` for all bounded measurable `L²` functions via S1 with `D = trigSpan`, dense by `dense_Atrig` + `Atrig_le_V`.)

## S4. General Riesz construction (files `RieszFunctional.lean`, `RieszKernel.lean`)

Setting: `X` topological, `[CompactSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]`
(compact metrizable), `T : DiffusionTriple X` with `[IsFiniteMeasure T.μ]`.  No relation between the triple's
`Γ, L` and the topology is assumed: only positivity preservation and sub-Markov property of `P_t` (theorems of the repo).
```
noncomputable def rieszKernelRep (T : DiffusionTriple X) [IsFiniteMeasure T.μ] : KernelRepresentation T
theorem rieszKernelRep_continuous (t) (f : C(X, ℝ)) (u : Lp ℝ 2 T.μ) (hu : u =ᵐ f) :
    (T.semigroup t u : X → ℝ) =ᵐ[T.μ] fun x => ∫ y, f y ∂((rieszKernelRep T).κ t x)
theorem rieszKernelRep_subInvariant (t) : T.μ.bind ((rieszKernelRep T).κ t) ≤ T.μ
theorem rieszKernelRep_markov_of_conservative (h : ∀ t, T.semigroup t one2 = one2) :
    ∃ K : KernelRepresentation T, K.IsMarkovRep         -- if proved
theorem CompactTriple.isFiniteMeasure_μ (T : CompactTriple X) : IsFiniteMeasure T.μ
noncomputable def CompactTriple.kernelRep [compact metrizable X] (T : CompactTriple X) : KernelRepresentation T.toDiffusionTriple
```
Honest scope: Chapman–Kolmogorov for this `κ` is only the a.e. form already derived in `KernelRepresentation.ck_integral/ck_ae`;
it is NOT claimed exactly (`SubMarkovKernelSemigroup`/`KernelBridge` needs exact CK, `κ_0 = id`; not provided by Riesz).
Pointwise-in-`x` functionals are built on a countable `ℚ`-subspace `V ⊂ C(X)` off a `μ`-null set; `κ_t x := 0` off it.

## S5. MarkovProcess interface (file `MarkovProcessInterface.lean`), no dependency

Armstrong's `MarkovProcess.SubMarkovKernelSemigroup α` (read as TEXT from an untrusted source tarball found at
`/tmp/lsi-armstrong-audit/sources/MarkovProcess`, commit 666cda02; not buildable here: Mathlib-module-system project, not in
our lakefile) has fields `kernel`, `measurable_kernel : Measurable fun p : ℝ≥0 × α => kernel p.1 p.2`, `kernel_zero`,
`kernel_add : kernel (s+t) = (kernel t).comp (kernel s)`, `isSubMarkovKernel`.
```
structure MarkovProcessSemigroupData (E) [MeasurableSpace E]    -- verbatim field mirror
def MarkovProcessSemigroupData.toSubMarkovKernelSemigroup : SubMarkovKernelSemigroup E
structure MarkovProcessBridge (T : DiffusionTriple E) extends MarkovProcessSemigroupData E  -- + rep, invariant
def MarkovProcessBridge.toKernelBridge : KernelBridge T
def KernelBridge.toMarkovProcessBridge (B : KernelBridge T) (hm : Measurable fun p : ℝ≥0 × E => B.κ p.1 p.2) : MarkovProcessBridge T
```
Instances OU (and circle if time): `Measurable fun p => ouKernel p.1 p.2`, hence `MarkovProcessBridge ouDiff`.
BLOCKED on the external library: the identification of `MarkovProcessSemigroupData` with Armstrong's actual structure.

## Axioms
Every new declaration depends only on `propext, Classical.choice, Quot.sound`; checked in `AxiomCheckR15.lean`.
