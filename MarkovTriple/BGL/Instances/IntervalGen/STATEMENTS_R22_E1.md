# STATEMENTS R22 E1 -- bounded open sets of R (incl. intervals (a,b)): non-complete, non-ESA diffusion triples; two Round-20 leftovers

Method "Armstrong": this file was written before any proof; deviations/changes are logged in `## Status`.
Namespace `MarkovTriple.BGL.Instances.IntervalGen`, files `MarkovTriple/BGL/Instances/IntervalGen/*.lean`
(part (c) lives in `IntervalGen/DirectEllConst.lean`, `IntervalGen/DirectSpiky.lean`).

Scope decision: I treat a GENERAL bounded nonempty open `Omega ⊂ ℝ` directly (no affine transport); `(a,b)` is the special case
`Omega = Ioo a b`.  So (a) and (b) are one development; no restriction to finite/countable unions of intervals is needed.

## Data (parts a, b)

```lean
structure BddOpen where
  carrier : Set ℝ
  isOpen : IsOpen carrier
  isBounded : Bornology.IsBounded carrier
  nonempty : carrier.Nonempty
def BddOpen.Ioo (a b : ℝ) (h : a < b) : BddOpen          -- carrier := Set.Ioo a b
/-- normalised Lebesgue measure on Omega (a probability measure, as D1 `finite_prob` demands) -/
noncomputable def BddOpen.μ (Ω : BddOpen) : Measure ℝ := (volume Ω.carrier)⁻¹ • volume.restrict Ω.carrier
/-- C_c^∞(Ω): smooth f : ℝ → ℝ with tsupport f ⊆ Ω -/
def BddOpen.A₀ (Ω : BddOpen) : NonUnitalSubalgebra ℝ (ℝ → ℝ)   -- carrier {f | Lebesgue.Sm f ∧ tsupport f ⊆ Ω.carrier}
/-- L f = f'', Γ(f,g) = f' g' -/
noncomputable def BddOpen.diff (Ω : BddOpen) : DiffusionTriple ℝ   -- μ := Ω.μ, A₀ := Ω.A₀, Γ := Lebesgue.Gf, L := Lebesgue.Lf
```

## Statements

* **G1** `Ω.diff : DiffusionTriple ℝ`, every field proved (D1: `Ω.μ` is a probability measure; D2: density of `Ω.A₀` in every
  `Lᵖ(Ω.μ)`, `1 ≤ p < ∞`; exhaustion by smooth cut-offs built from the distance to `Ωᶜ` (Mathlib smooth Urysohn)).
* **G2** (`Γ₂` and curvature).
  `theorem BddOpen.ΓA_eq (Ω) {f g} (hf : Sm f) (hg : Sm g) (x) : Ω.diff.ΓA f g x = deriv f x * deriv g x`,
  `theorem BddOpen.Γ₂_eq (Ω) {f} (hf : Sm f) (x) : Ω.diff.Γ₂ f f x = (deriv (deriv f) x)^2`,
  `def BddOpen.GenCD (Ω) (ρ : ℝ) (n : ℝ≥0∞) : Prop := 1 ≤ n ∧ ∀ f, Sm f → ∀ x, ρ * Ω.diff.ΓA f f x + (n⁻¹).toReal * (Ω.diff.L f x)^2 ≤ Ω.diff.Γ₂ f f x`,
  `theorem BddOpen.diff_CD (Ω) {ρ n} (hρ : ρ ≤ 0) (hn : 1 ≤ n) : Ω.GenCD ρ n`.
* **G3** `theorem BddOpen.not_complete (Ω : BddOpen) : ¬ Ω.diff.IsComplete`.
  Proof (no case distinction on components, no boundary point needed): if `ζ ∈ A₀`, `Γ(ζ) ≤ c²` a.e. then `|ζ'| ≤ c` on all of `ℝ`
  (continuity of `ζ'`, `Ω` open, `ζ' = 0` off `tsupport ζ ⊆ Ω`), hence `|ζ(x)| ≤ c |x - y|` for every `y ∉ Ω` (`ζ y = 0`; MVT);
  `Ωᶜ ≠ ∅` since `Ω` is bounded.  For `x` with `ζ_k(x) → 1` this gives `ζ_k(x) ≤ |x-y|/(k+1) → 0`.
  (This is the claimed `|ζ(x)| ≤ dist(x,∂Ω) sup|ζ'|` argument, with `y` any point of `Ωᶜ`, a weaker but sufficient form.)
* **G4** `theorem BddOpen.not_esaProp (Ω) : ¬ Ω.diff.ESAProp`;
  `theorem BddOpen.no_fullTriple (Ω) (T : FullTriple ℝ) : T.toDiffusionTriple ≠ Ω.diff`;
  `theorem BddOpen.exp_orth (Ω) : ∃ u : Lp ℝ 2 Ω.μ, u ≠ 0 ∧ ∀ a : Ω.diff.A₀, inner ℝ u (Ω.diff.Lcls a - Ω.diff.cls a) = 0`
  (`u = exp|_Ω`, bounded since `Ω` is bounded).
* **G5** intervals: for `a < b`, with `I := BddOpen.Ioo a b h`: the specialisations
  `Ioo_not_complete`, `Ioo_not_esaProp`, `Ioo_no_fullTriple`, `Ioo_Γ₂_eq`, `Ioo_diff_CD`, plus the consistency lemma
  `BddOpen.Ioo_zero_one_μ : (BddOpen.Ioo 0 1 _).μ = Interval.ivμ` (the Round 21 measure).
  (Aliases; nothing new is proved for `(a,b)` beyond G1-G4.)

## Statements (part c: Round 20 leftovers)

* **C1** (`DirectEllConst.lean`) for every `E : EllData d` and `ρ` with `E.Curv ρ`, the constant function `f ≡ 1` (not in `𝒜₀` for `d ≥ 1`)
  satisfies the hypotheses of `EllData.ell_mem_domain_of_Γ₂_direct`, which is applied (not re-derived):
  `theorem EllData.ell_const_mem_domain_direct {ρ} (hρ : E.Curv ρ) : ∃ hf2 : MemLp (fun _ => (1:ℝ)) 2 E.μ, ∃ hF : hf2.toLp _ ∈ E.fullU.toDiffusionTriple.generator.domain,
  ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp _, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ] E.fullU.L (fun _ => 1)`,
  and `E.fullU.L (fun _ => 1) = 0`.
* **C2** (`DirectSpiky.lean`) for `spikyData d`: non-`𝒜₀` functions `f` for which `gibbsRd_mem_domain_of_Γ₂_direct` is applied:
  `spikyData_const_mem_domain (d)` (`f ≡ 1`) and, if affordable, a non-trivial bounded function `f(x) = sin(x₀)` (`d ≥ 1`),
  `spikyData_sin_mem_domain`, with conclusion `∃ hF, generator ⟨toLp f, hF⟩ =ᵐ gibbsRdFull_unconditional.L f`
  (`Γ f = cos² x₀ ≤ 1`, `Γ₂ f = sin² x₀ + spk(x₀) cos² x₀`, bounded, hence integrable).
  If the `sin` case is too costly it is logged in Status and only the constant is claimed.

## DIFFERENCE FROM BGL

1. `μ` is normalised: `μ = |Ω|⁻¹ dx|_Ω` (BGL: a finite `μ` is a probability measure).  `L, Γ` unaffected.  For `Ω = (0,1)` this is the Round 21 measure.
2. `E = Ω` is modelled on `ℝ` with functions extended by `0` (as in Round 21).
3. `GenCD` instead of `FullTriple.CD` (no `FullTriple` over `Ω.diff`, G4); the inequality is pointwise on `C^∞`, with equality `Γ₂ = (Lf)²`.
4. Completeness (G3): `¬ IsComplete` verbatim from the library's `IsComplete` (BGL Def. 3.3.9); the proof uses only `Ωᶜ ≠ ∅`.
5. Only bounded open `Ω` (finite measure; `exp ∈ L²`); no claim for unbounded `Ω`.

## Status
ALL of G1-G5, C1, C2 PROVED, statements as written (nothing weakened).  `lake build` of every module: 0 errors, 0 warnings, no `sorry`,
no `set_option`; axioms of every theorem (`AxiomCheckR22E1.lean`, 19 `#print axioms`): only `propext`, `Classical.choice`, `Quot.sound`.
No frozen file / `lakefile.toml` / `lake-manifest.json` / toolchain / ERRATA / GAPS / `MarkovTriple.lean` touched.

Files (all `MarkovTriple/BGL/Instances/IntervalGen/`): `Basic.lean` (`BddOpen`, `μ`, `A₀`, `K n`, smooth cut-offs `cut n`),
`Dense.lean` (`BddOpen.A₀_dense`), `Diffusion.lean` (`BddOpen.diff`, `ΓA_eq`, `Γ₂_eq`, `GenCD`, `diff_CD`), `NotComplete.lean`
(`abs_deriv_le`, `abs_le_of_Γ`, `BddOpen.not_complete`), `NotESA.lean` (`exp_ibp`, `memLp_exp`, `exp_orth`, `not_esaProp`, `no_fullTriple`),
`Ioo.lean` (`iooDiff`, `Ioo_zero_one_μ`, `Ioo_Γ₂_eq`, `Ioo_diff_CD`, `Ioo_not_complete`, `Ioo_not_esaProp`, `Ioo_no_fullTriple`),
`DirectEllConst.lean` (`EllData.ell_const_mem_domain_direct`, `EllData.fullU_L_const_fn`, `Riemannian.hypRiem_const_mem_domain_direct`),
`DirectSpiky.lean` (`spikyData_mem_domain_of_formulas`, `spikyData_const_mem_domain`, `spikyData_sin_mem_domain`), `AxiomCheckR22E1.lean`.

Notes / deviations / honest scope:
* (b) is done for ARBITRARY bounded nonempty open `Ω ⊂ ℝ` (not only finite/countable unions of intervals); nothing is missing there.
  Unbounded `Ω` (infinite Lebesgue measure, so no `finite_prob`/probability normalisation) and empty `Ω` are NOT covered.
* Differences from the plan: (i) `Ioo_diff_CD` is stated for `(BddOpen.Ioo a b h).GenCD`, and `Ioo_zero_one_μ` is `BddOpen.Ioo_zero_one_μ`.
  (ii) The Round 21 triple `ivDiff` is NOT literally rewritten as `(Ioo 0 1).diff` (they have the same `μ`, `A₀`, `L`, `Γ`; only the cut-off
  sequence differs, so the structures are not syntactically equal; no equality statement is claimed).
  (iii) The cut-offs are not explicit: smooth Urysohn (`exists_contDiff_zero_iff_one_iff_of_isClosed`) between `{dist(·,Ωᶜ) ≤ 1/(n+2)}` and
  `K n = {dist(·,Ωᶜ) ≥ 1/(n+1)}`; selected with `Classical.choose`.
* G3 does not use a boundary point or `dist(x,∂Ω)`: any `y ∉ Ω` works (`|ζ(x)| ≤ c|x-y|`).  It proves `¬IsComplete` verbatim; only
  `Ωᶜ ≠ ∅` and `μ ≠ 0` are used (so it would hold for any open `Ω ⊊ ℝ` of positive measure, but we state the bounded case only).
* C1/C2: `f ≡ 1` has `Γ = Γ₂ = L f = 0`; the conclusion is trivial mathematically; the value is that the hypotheses of the R20 theorems
  (`ell_mem_domain_of_Γ₂_direct`, via `spikyData_mem_domain_of_Γ₂` = `gibbsRd_mem_domain_of_Γ₂_direct`) are discharged outside `𝒜₀`.  `sin x₀`
  is a nontrivial one: `Γ f = cos² x₀`, `Γ₂ f = sin² x₀ + spk(x₀) cos² x₀` (verified in `Γ₂form_sinF`), `f ∉ A₀` (not compactly supported),
  but it is bounded; it does NOT exercise `L²`-integrability of unbounded functions (no moment bounds for `μ_spiky` were proved).
  `E.fullU.L (fun _ => 1) = 0` is the separate lemma `fullU_L_const_fn` (not a conjunct of C1).
* The existing lemma name `EllData.L_const` already existed; mine is `L_const_fn`.

### Proposed ERRATA rows (for the maintainer; ERRATA.md/GAPS.md NOT edited)
| id | severity | finding | resolution |
|---|---|---|---|
| R22-E1-1 | INFO (generalisation) | R21 I5 (bounded open `Ω ⊂ ℝ`, in particular `(a,b)`) is closed: for every bounded nonempty open `Ω`, `Ω.diff` is a `DiffusionTriple` (μ normalised Lebesgue), `Γ₂ = (Lf)²`, `¬IsComplete`, `¬ESAProp`, no `FullTriple`.  GAPS R21 "I5 open" can be removed. | `Instances/IntervalGen/*` |
| R22-E1-2 | INFO (scope) | `μ` normalised `= |Ω|⁻¹ dx` (probability) since `finite_prob`; `GenCD` replaces `FullTriple.CD`. | `Basic.lean`, `Diffusion.lean` |
| R22-E1-3 | INFO (non-vacuity) | R20 leftovers: `f ≡ 1` for `EllData` (`ell_const_mem_domain_direct`, `hypRiem`) and `f ≡ 1`, `f = sin x₀` for `spikyData` exercise `…_Γ₂_direct` outside `𝒜₀`; weak (bounded `f`). | `DirectEllConst.lean`, `DirectSpiky.lean` |

### Import lines for `MarkovTriple.lean` (not edited by me)
```
import MarkovTriple.BGL.Instances.IntervalGen.Basic
import MarkovTriple.BGL.Instances.IntervalGen.Dense
import MarkovTriple.BGL.Instances.IntervalGen.Diffusion
import MarkovTriple.BGL.Instances.IntervalGen.NotComplete
import MarkovTriple.BGL.Instances.IntervalGen.NotESA
import MarkovTriple.BGL.Instances.IntervalGen.Ioo
import MarkovTriple.BGL.Instances.IntervalGen.DirectEllConst
import MarkovTriple.BGL.Instances.IntervalGen.DirectSpiky
import MarkovTriple.BGL.Instances.IntervalGen.AxiomCheckR22E1
```
and a `proposed` entry in `frozen-manifest.json` for this file.
