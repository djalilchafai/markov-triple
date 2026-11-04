# AUDIT R22 E4 (hostile): non-compact CD on (R, Lebesgue) and the hypRiem RadialJets obstruction

Audited commit 6e3e9fe (merged into b44dbee). Files: `R22/{NonCompactCD,HypCutObstruction,AxiomCheckR22E4}.lean`, `STATEMENTS_R22_E4.md`.

## Verdict
No soundness defect, no vacuity. Mathematics and Lean are correct as claimed. Two documentation problems (one MEDIUM: the proposed
erratum R22-E4-1 partly attacks a strawman; one LOW-MEDIUM: wording of what the RadialJets failure refutes). The honest reading of the
deliverable is: (a) a small sharpness lemma for an already existing instance, (b) formalisation of a quantity already computed by hand in
AUDIT_R19_CORE2ELL §6, not a Core2 result.

## Verified
* Build of the three modules (my own run, `lake build`): success, no warnings/errors/sorry in the new files (the only infos are pre-existing
  `Heat.lean:236` ring_nf hint and the old `#print axioms`).  No `set_option`, no `sorry`, no `axiom` in R22 files (grep).
* `#print axioms` (run by me) on lebesgue_CD_iff, lebesgueFull_noncompact, lebesgueFull_A_ne_A₀, hypRiem.hyp_L_V, hyp_Γ_V, hyp_L_V_unbounded,
  hyp_L_psi_unbounded, hyp_not_radialJets_V, hyp_not_radialJets_psi: only propext, Classical.choice, Quot.sound.
* `python3 scripts/check_frozen.py`: OK.  `git diff b44dbee 6e3e9fe --name-only`: only the four new R22 files plus `frozen-manifest.json`, whose
  diff is exactly one added `proposed` entry for `STATEMENTS_R22_E4.md`. No fenced file touched, lakefile/manifest/toolchain untouched.
* `FullTriple.CD` (`Frozen/CD.lean:20`) is `1 ≤ n ∧ ∀ f ∈ A, ∀ᵐ x ∂μ, ρ Γ_A f f + (n⁻¹).toReal (L f)² ≤ Γ₂ f f`. `lebesgue_CD_iff` is a genuine
  iff in this CD (no re-encoding): the proof takes the test function `f = id ∈ 𝒜` (smooth, unbounded, NOT in 𝒜₀), `L f = 0`, `Γ₂ = 0`, `Γ = 1`,
  obtains `ρ ≤ 0` a.e. on Lebesgue (positive measure) hence `ρ ≤ 0`; `1 ≤ n` is the first conjunct.  The reverse is the pre-existing `lebesgue_CD`.
  The sharpness genuinely uses 𝒜 ⊋ 𝒜₀ (id ∉ 𝒜₀), which is the point of N2.
* `lebesgueFull_noncompact`: `NoncompactSpace ℝ ∧ volume univ = ⊤`; `lebesgueFull_A_ne_A₀`: `1 ∈ 𝒜` (A.one_mem), `1 ∉ 𝒜₀` (compact support fails). Correct.
* Hyperbolic plane, by hand: `V = 2u = 2cosh d` (`HypExample.lean:73`, `W := V` at line 272), `Δ cosh d = cosh d + sinh d coth d = 2cosh d`, so
  `ΔV = 2V`; `Γ(V) = 4 sinh² d = V² - 4`; `L = Δ - ∇W·∇` gives `LV = 2V - (V²-4) = -V²+2V+4`. Matches `hyp_L_V`, `hyp_Γ_V`, and `Δg_V : Δg V = 2V`.
  Also `Lψ = LV/(1+V) - ΓV/(1+V)²` for ψ = log(1+V) (chain rule), ≤ -(V-5): checked, matches `L_psi`, `L_psi_le`.
  The unboundedness proofs evaluate at the point `(x,0)` with `V = 2+x²`; arithmetic checked.
* Line estimates in STATEMENTS: Lebesgue heat/identify/ODE ≈ 2600 lines: actual `wc` of `Instances/Lebesgue/*.lean` = 2555. OK. Other estimates are heuristic and labelled so.

## Findings

### MEDIUM-1 (docs): ERRATA row R22-E4-1 mischaracterises the existing notes (partly a strawman)
`STATEMENTS_R22_E4.md` (section N background, section (iii), proposed row R22-E4-1) says "R16/R17 scope notes say no non-compact finite-n CD
instance with 𝒜 ≠ 𝒜₀ exists ... accurate only for ρ>0 or d≥2".  What the notes actually say:
* ERRATA `R16-Ext-audit` (ERRATA.md:177): "no non-compact, finite-n, **ρ>0** instance of `logSobolev_dim_unconditional`" — already qualified by ρ>0 (and by finite measure, since that theorem needs `IsFiniteMeasure`).  Not contradicted by `lebesgueFull`.
* `Theory/GAPS.md:206` scope note: "the non-compact instances (OU, Lebesgue, Gibbs) have n=∞ **or infinite measure**" — it already names Lebesgue as the infinite-measure non-compact case, in the context of ρ ≥ 0, finite-measure LSI-dim.  Not contradicted.
* ERRATA `R17-M2` (ERRATA.md:208): "does NOT close the R16 gap 'no non-compact finite-n CD instance with A ≠ A₀'" — unqualified; and GAPS.md:233 "NOT closed: non-compact finite-n CD instance".  THESE two are loose and are genuinely corrected by `lebesgueFull` (CD(ρ,n), ρ ≤ 0, n ∈ [1,∞], A ≠ A₀, infinite μ), provided one reads "instance" as including infinite-measure, ρ ≤ 0 ones — which is not the context in which the R16 gap (needed by `ext`/Thm 5.7.4, finite measure, ρ ≥ 0, n<∞) was posed.
* "d ≥ 2" appears in none of the notes.
* "ρ>0 remains open": for a complete non-compact space finite-n CD(ρ>0) is impossible (Bonnet-Myers type), so "open" is misleading; the only live cases are incomplete spaces (SphereOpen, cosmetic) and Gegenbauer n ≥ 4 genuine boundary case.
Also note `lebesgue_CD` (ρ ≤ 0 ∧ 1 ≤ n ⇒ CD) already existed in `Lebesgue/Full.lean:137`; only the converse direction and the 𝒜 ≠ 𝒜₀ / non-compact statements are new.
Recommended R22-E4-1 text: "INFO (precision). ERRATA R17-M2 / GAPS Round 17 closing line ('non-compact finite-n CD instance not closed') should read: no non-compact finite-n CD instance with ρ>0 and finite μ (as needed for `logSobolev_dim_unconditional`); with ρ ≤ 0 and infinite μ, `lebesgueFull` is one, and `lebesgue_CD_iff` shows ρ ≤ 0 is sharp. R16-Ext-audit and GAPS:206 were already correctly qualified."  (Applied nowhere; ERRATA untouched by me.)

### MEDIUM-2 (scope wording): what `¬RadialJets` refutes
`RadialJets E ψ α β` (`GibbsRd/Core2EllRadial.lean:23`) fixes ψ; the quantification in `hyp_not_radialJets_V/psi` is over all α, β, but for only TWO specific exhaustions V and log(1+V).  So "the RadialJets criterion fails for every α,β" is true but the theorem does NOT show `EllData.RadialExh hypRiem.toEll` (∃ψ α β) fails, still less that `CoreCut` fails or that no `CutFamily` exists.  The statement file does say "for the two natural exhaustions" and does not claim CoreCut false, so this is honest, but the task-level description "the radial route fails" overstates unless "for these ψ" is kept.  (My heuristic check: for any radial ψ(d), `Lψ ≈ -e^d ψ'` forces ψ' ≲ (1+ψ)e^{-d}, hence bounded ψ, contradicting `proper`; so the whole route probably fails for radial ψ, but that is not formalised, and non-radial ψ are not covered.)  Also, the obstruction was already stated by hand in AUDIT_R19_CORE2ELL §6 (line 67: `Lψ ~ -e^ψ` violating RadialJets growth); R22-E4 formalises it, it does not discover it.  The Status text acknowledges this; fine.

### LOW-1
STATEMENTS Status says "`AxiomCheckR22E4.lean`: only propext, ... " — correct (confirmed above), but the implementer note that it had not re-run is replaced by my run.
### LOW-2
Proposed R22-E4-3 (naming in `hypRiem` namespace) is accurate: theorems are `hypRiem.hyp_L_V` etc.; the file's `open Hyp` plus `namespace hypRiem` works. No action.
### LOW-3 (cosmetic)
`lebesgue_CD_iff` implicit `{ρ} {n}` with `n : ℝ≥0∞`; for `n = ∞` the second summand vanishes, so the iff correctly includes n = ∞ (CD(0,∞)). No issue.

## Not checked / limits
No attempt to verify the by-hand "no CutFamily" claim (R19 §6) beyond the radial heuristic above; nothing in this stream proves it.
