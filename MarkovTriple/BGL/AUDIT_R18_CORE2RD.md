# AUDIT R18 (Stream A3): `Core2` and the converse of BGL Prop. 3.3.17 for Gibbs measures on `ℝ^d` (hostile self-audit)

Statements: `Instances/GibbsRd/STATEMENTS_R18_Core2Rd.md`.  The BGL book PDF was not located on this machine (the `find` for `*bakry*`/`*BGL*` PDFs only returned unrelated
Bakry research papers), so book numbering is quoted from the repository's own notes (Prop. 3.3.17 p. 161-162, ESA 3.3.11, (1.16.5));
nothing below depends on a page number.

## 1. What is proved (all in `MarkovTriple.BGL.Instances.GibbsRd`)
| item | name | file |
|---|---|---|
| hypothesis | `GibbsRdData.BddHess3` (`∂ᵢ∂ⱼV`, `∂ᵢ∂ⱼ∂ₖV` bounded) | `Core2RdDefs` |
| calculus | `Lr_mul`, `Lr_Gr` (polarised Bochner), `Lr_remainder` | `Core2RdCalc` |
| cut-offs | `BddHess3.grad_growth` (`|∂ᵢV| ≤ C(1+Σ|xⱼ|)`), `cut_bounds` (uniform `K` for `χ, ∂χ, ∂²χ, Lχ, ∂Lχ, LLχ`), `cut_vanish` | `Core2RdCut` |
| resolvent | `exists_resolvent_smooth` (no hypothesis on `V`) | `Core2RdResolvent` |
| energy | `memLp_grad_resolvent` (no hyp.), `memLp_hess_resolvent` (`HessGe V ρ`, `ρ` any sign, `|Lχ_n| ≤ K`) | `Core2RdEnergy` |
| bookkeeping | `ZL`, `Good`, `cutoff_ZL`, `core2_of_ZL` | `Core2RdZL`, `Core2RdCutZL`, `Core2RdAssemble` |
| **main** | `GibbsRdData.gibbsRd_core2 (hb : G.BddHess3) : G.gibbsRdFull_unconditional.Core2`; `gibbsRd_mem_domain_of_Γ₂ (hb) (hρ : HessGe G.V ρ) …` | `Core2RdMain` |
| witnesses | `gaussData_witness`, `cosData_witness`, `{gauss,cos}Data_core2`, `{gauss,cos}Data_mem_domain_of_Γ₂` | `Core2RdExample`, `Core2RdWitness` |
`#print axioms` (`AxiomCheckR18Core2Rd.lean`): only `propext`, `Classical.choice`, `Quot.sound`.  No `sorry`, no `set_option`, no new axiom;
new files compile with 0 warnings; full `lake build` OK; `scripts/check_frozen.py` OK.

## 2. Faithfulness
* `Core2` is the repository's `FullTriple.Core2` (`Extension/Converse.lean`), applied to `gibbsRdFull_unconditional` (the Full Markov Triple
  built from the proved `WeakHypo`/`F8`); the converse is `FullTriple.mem_domain_of_Γ₂` with `gibbsRdFull_CD_unconditional hρ` — no new
  hypothesis on `f` beyond the book's (`f ∈ 𝒜`, `f ∈ L²`, `Γ(f), Γ₂(f) ∈ L¹`).
* The Lean `L` on `𝒜₀` is `Lr V = Δ − ∇V·∇` (`toEll_L`); the theorem is about the Friedrichs generator of `𝒜₀`, as in the book.
* Method (book-faithful where the book has an argument; the book has none for `Core2`, ERRATA R15-1): resolvent solution `v = (1−L)⁻¹[a]`,
  smoothness from the proved `EllReg`, cut-off Caccioppoli, cut-off Bochner `Γ₂ = ‖Hess v‖² + Hess V(∇v,∇v) ≥ ‖Hess v‖² + ρ|∇v|²` (the
  `Γ₂ ≥ ρΓ` step; `ρ` may be negative), and cut-offs `χ_n v` in the graph norm of `L²`.

## 3. Are the hypotheses contradictory?  No (explicit ρ>0 witnesses)
* `BddHess3` does not bound `∇V`; it is the weakest hypothesis our proof uses.  `HessGe V ρ` is a separate (curvature) hypothesis of the converse.
* `gaussData d`: `V = |x|²/2`, `HessGe V 1`, `Hess V = I`, `∇³V = 0`, and `∇V(x) = x` unbounded (`gaussData_witness`).
* `cosData d` on `ℝ^{d+1}`: `V = |x|²/2 + cos(x₀)/2`, `|∂ᵢ∂ⱼV| ≤ 2`, `|∂ᵢ∂ⱼ∂ₖV| ≤ 1`, `HessGe V (1/2)` (so `ρ = 1/2 > 0`), not a quadratic form
  (`cosData_witness`).  `cosData_core2` and `cosData_mem_domain_of_Γ₂` are instantiated theorems, so the main theorems are applied to a `ρ>0`,
  non-Gaussian potential.  (Contrast R17-M1: the 1-D `BddJet` hypothesis forced `ρ ≤ 0`.)
* The conclusion's hypotheses on `f` are satisfiable (e.g. `f ∈ 𝒜₀`, where `Γ, Γ₂` are compactly supported).

## 4. Hostile checks and limits
1. *Edge case `d = 0`*: index-free families (`Lχ`, `LLχ`) are treated separately (`Lr = 0` on the empty index set) in `coeffGood`, `hessGe`, `gibbsRd_core2`.
2. *Where is `BddHess3` really used?*  (i) `|Lχ_n|, |∂Lχ_n|, |LLχ_n|, |Σ V_ij χ_i| ≤ K` uniformly: needs `|∇V| ≲ 1+|x|` (bounded `Hess V`, integrate along rays) against `|∇χ_n| ≲ 1/n` on `n ≤ |x| ≤ √2 n`, and `∇³V` bounded in `L(Lχ)`, `∂(Lχ)`;
   (ii) bounded `Hess V` gives some `ρ` with `HessGe V ρ` (`BddHess3.hessGe`), used only to feed the Hessian estimate.  The converse takes its own `ρ`.
3. *Not proved*: unbounded `Hess V` (e.g. `V = |x|⁴`: `|∇V||∇χ_n|` is unbounded on the annulus; no replacement argument found); general smooth `V`
   (≡ e.s.a. of `L²` on `C_c^∞`, possibly false); `EllData d`, `RiemData d` (commutators involve `∂a`; needs growth/bounded-geometry hypotheses on `a`); 1-D without `BddJet` (Stream A2).
   We do not claim `Core2` is false anywhere; we have no counterexample and no proof beyond the class above.
4. *Not a replacement of Bakry's abstract argument*: Γ₂ ≥ ρΓ enters only through the Hessian estimate (no abstract ESA-of-`L²` argument from `CD(ρ,∞)` was found; the derivation of `Core2` uses the explicit commutators).
5. *Statement drift*: none (ERRATA R18-2 lists the renamings; `final_arith` was renamed to avoid a clash).
6. `ContDiff` is taken in the `(⊤ : ℕ∞)` sense (`Sm`), not analytic.
