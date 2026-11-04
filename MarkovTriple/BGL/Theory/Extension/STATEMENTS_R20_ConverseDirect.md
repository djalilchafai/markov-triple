# Round 20, Stream D3 (abstract direct converse of BGL Prop. 3.3.17): statements fixed BEFORE the proofs.

Change only by a logged deviation in a `Status` section below and an erratum in `ERRATA.md` (prefix `R20-D3-`).
Setting: `T : FullTriple E` (F1-F10), `G = ΓA`, `K(f) = Γ₂(f) - ρΓ(f)`.  File: `Extension/ConverseDirect.lean`.

## DIFFERENCE FROM BGL (explicit)

* **What BGL does** (Prop. 3.3.17, p. 161-162, converse): shows `|∫ f L h| ≤ C ‖h‖` on `(L²+Id)𝒜₀` via `K(f,h)² ≤ K(f)K(h)`,
  Riesz in `𝒟(L)`, then extends the functional to all of `L²` using that `𝒜₀` is a core for `L²` and ergodicity (density of
  `{L h}` in `L²₀`).  That core-for-`L²` step is silently used (ERRATA R15-1; formal name `FullTriple.Core2`), and we could prove it
  only under growth conditions (Rounds 17-19).
* **What we do instead**: we never touch `L²`.  We prove `L f ∈ L²` directly for `f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹`, by the
  CUT-OFF technique of BGL Prop. 3.2.1 (p. 142, essential self-adjointness) applied to `Γ₂`: the completeness cut-offs `ζ_k`
  (Def. 3.3.9) give the exact identity
  `∫ χ² (Lf)² = ∫ χ² Γ₂(f) + ∫ χ Γ(Γ f, χ) - 2 ∫ χ Lf Γ(f,χ)`  (`χ = ζ_k ∈ 𝒜₀`, F7 only),
  the cross term is controlled by the Hessian inequality `Γ(χ,Γf)² ≤ 4 K(f) Γ(χ) Γ(f)` (BGL (3.3.7), already in the repo as
  `hessian_general_ineq`; `Γ(χ,Γf) = 2 H(f)(χ,f)`), and `Γ(χ,f)² ≤ Γ(χ)Γ(f)`; Fatou as `k → ∞`.  Then `f ∈ 𝒟(L)`, `L f = [Lf]`
  by ESA via the maximal-domain lemma (BGL Prop. 3.3.6 (i); already `mem_domain_of_ESA`).
* **Why**: `Core2` (essential self-adjointness of `L²` on `𝒜₀`) is hard; the converse only needs `Lf ∈ L²`.
* **Hypotheses that differ**: BGL needs: ESA, `CD(ρ,∞)`, ergodicity, [and tacitly the `L²`-core step].  We need: ESA (F10),
  completeness (Def. 3.3.9, hypothesis `IsComplete`), `CD(ρ,n)` (any `n`).  NOT needed: `Core2`, ergodicity (S10), any growth or
  Hessian-boundedness hypothesis.  **`Core2` is not needed here.**  No extra named hypothesis `HessCS` is needed: it is a THEOREM
  (`FullTriple.hessCS`) of the abstract calculus under `CD(ρ,n)`.
* **Completeness is new as a hypothesis** relative to the existing `mem_domain_of_Γ₂` (which has `Core2` but no completeness).
  The two hypothesis sets are incomparable.

## Statements

```lean
/-- maximal-domain lemma (BGL 3.3.6 (i), ESA): alias of `mem_domain_of_ESA`. -/
theorem FullTriple.mem_domain_of_maximal (hf : f ∈ T.A) (hf2 : MemLp f 2 T.μ) (hLf2 : MemLp (T.L f) 2 T.μ) :
    ∃ hF : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain,
      T.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ = hLf2.toLp (T.L f)

/-- Hessian Cauchy-Schwarz (HessCS, DERIVED not assumed): `CD(ρ,n)`, `f χ ∈ 𝒜` ⇒ a.e.
`Γ(χ, Γ f)^2 ≤ 4 (Γ₂(f) - ρ Γ(f)) Γ(χ) Γ(f)`. -/
theorem FullTriple.hessCS (hCD : T.CD ρ n) (hf : f ∈ T.A) (hχ : χ ∈ T.A) :
    ∀ᵐ x ∂T.μ, G T χ (G T f f) x ^ 2 ≤ 4 * (Γ₂ f f x - ρ * G T f f x) * (G T χ χ x * G T f f x)

/-- cut-off Γ₂ identity (F7 only; χ ∈ 𝒜₀, f ∈ 𝒜). -/
theorem FullTriple.cutoff_Γ₂_identity (hχ : χ ∈ T.A₀) (hf : f ∈ T.A) :
    ∫ χ² (L f)² = ∫ χ² Γ₂ f f + ∫ χ Γ(Γ f, χ) - 2 ∫ χ (L f) Γ(f, χ)

/-- `L f ∈ L²` from completeness + `CD(ρ,n)` + `Γ(f), Γ₂(f) ∈ L¹`. -/
theorem FullTriple.memLp_L_of_Γ₂ (hC : T.toDiffusionTriple.IsComplete) (hCD : T.CD ρ n) (hf : f ∈ T.A)
    (hG : Integrable (G T f f) T.μ) (hG2 : Integrable (Γ₂ f f) T.μ) : MemLp (T.L f) 2 T.μ

/-- **Direct converse of BGL Prop. 3.3.17** (no `Core2`). -/
theorem FullTriple.mem_domain_of_Γ₂_direct (hC : T.toDiffusionTriple.IsComplete) (hCD : T.CD ρ n) (hf : f ∈ T.A)
    (hf2 : MemLp f 2 T.μ) (hG : Integrable (G T f f) T.μ) (hG2 : Integrable (Γ₂ f f) T.μ) :
    ∃ hF : hf2.toLp f ∈ T.toDiffusionTriple.generator.domain,
      ((T.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 T.μ) : E → ℝ) =ᵐ[T.μ] T.L f
```
(Same conclusion as `mem_domain_of_Γ₂`.)

## Status
PROVED, all statements above as written (no weakening).  Files: `Extension/ConverseDirect.lean` (all five theorems, plus
`cutoff_bound`: for `0 ≤ χ ≤ 1`, `Γχ ≤ 1`: `∫χ²(Lf)² ≤ 4∫(Γ₂f−ρΓf) + 2(|ρ|+3)∫Γf`), `ConverseDirectInst.lean` (applications: OU incl.
the concrete `f = id`, circle, Lebesgue, every `EllData d` / `RiemData d` with `Curv ρ` but WITHOUT `CoreCut`), `ConverseDirectAxioms.lean`.
Axioms: propext, Classical.choice, Quot.sound only.  Deviations: none.  Additions: `cutoff_bound`, and `mem_domain_of_maximal` is the existing
`mem_domain_of_ESA` (Prop 3.3.6 (i)) re-exported.  `HessCS` was NOT needed as a hypothesis (it is `hessCS`, from `hessian_general_ineq`).
