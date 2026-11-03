# Round 15 (Core2) self-audit

Statements: `Theory/Extension/STATEMENTS_R15_Core2.md` (written before the proofs).  Files: `Theory/Extension/Core2Reduce.lean`,
`Instances/OU/Core2{Tail,Cut,}.lean`, `Instances/Lebesgue/Core2{Cut,}.lean`, `Instances/AxiomCheckCore2.lean`.

## 1. Decision on `Core2` (part A): not derivable by book means
Book, p. 161-162 (Prop 3.3.17 last claim): ℓ_f(h) = ∫ K(f,h), |ℓ_f(h)| ≤ C‖h‖_{𝒟(L)} for `h ∈ 𝒟(L)`; Riesz gives `g ∈ 𝒟(L)`;
"easily seen from the spectral decomposition g = Lk, k = (L²+Id)^{-1}(L+ρId)f"; then ℓ_f(h) = ∫(Lg+k)Lh, |·| ≤ C‖Lh‖₂ for `h ∈ 𝒜₀`;
"the linear form ℓ_f can be extended to L²".  Two facts hide here: (i) the identification ℓ_f(h) = ∫(Lf+ρf)Lh holds for `h ∈ 𝒜₀` only
(it uses ∫Γ₂(f,h) = ∫ Lf·Lh, F7 twice), so the bound is on the vectors `Lh`, `h ∈ 𝒜₀` (`L𝒜₀ ⊂ 𝒜₀`); (ii) the conclusion `f ∈ 𝒟(L*)=𝒟(L)`
needs the bound `|⟨f, L u⟩| ≤ C‖u‖` on a *core* of `L`, while the bound lives on `L𝒜₀` (resp. `(1−L)𝒜₀`).  Prop 3.3.6/3.3.11/Cor 3.2.2/A.5-A.6
(ESA) only say `𝒜₀` is a core for `L`; "(1−L)𝒜₀ (equivalently L𝒜₀ ∩ …) is a core for `L`" is the extra input.  We tried: ESA + F8 (`P_t𝒜₀ ⊂ 𝒜`)
+ CD: no derivation (`P_t 𝒜₀ ⊄ 𝒜₀` outside compact triples; an abstract ES operator `L` on an `L`-invariant domain need not have `L²` ES).
We did not find a counter-model satisfying F1-F10 either.  The `ρ ≥ 0` remark of p. 162 does not touch this step.
Hence: hidden hypothesis = `Core2` ⇔ `(1−L)²𝒜₀` dense in `L²` ⇔ `𝒜₀` core for `L²` (book p. 162, "g = Lk" and "extended to L²").

## 2. What is proved
* `core2_of_dense`: dense `(1−L)²𝒜₀` ⇒ `Core2` (elementary: `‖[c]‖,‖[Lc]‖ ≤ ‖[c]−[Lc]‖` for `c ∈ 𝒜₀`).
* `CompactTriple.mem_domain_of_A`: for `𝒜 = 𝒜₀` the converse is trivial (no CD, no Core2, no integrability).  Applies to circle, `OUCompact`, sphere
  (all `CompactTriple`s).  NB `Core2` itself is not proved for them (not needed).
* OU: `cutoff_approx2` (g_k = χ(x/(k+1))·f ∈ C_c^∞; g_k→f, Lg_k→Lf, L²g_k→L²f in L²(γ) for smooth f with f,f',f'',Lf,(Lf)',L f',L²f ∈ L²), via the
  inductive class `Tl` of rescaled cut-off derivatives (closed under d/dx, x·d/dx, L; uniform bound; vanishing on |x|<1/c) and the pointwise
  expansion `LoLo_mul`; polynomials satisfy the hypotheses (`pf_approx2`); Hermite basis ⇒ `ou_dense_Ψ`; `ouFull_core2`; `ou_mem_domain_of_Γ₂`
  (uses `ouFull_CD : CD(1,∞)` and `mem_domain_of_Γ₂`).
* Lebesgue: `cutoff4_tendsto` (fourth-order cut-off convergence) + `exists_resolvent_solution` ⇒ `lebesgueFull_core2`; `lebesgue_mem_domain_of_Γ₂`
  for `CD(ρ,n)`, `ρ ≤ 0`, `1 ≤ n` (`lebesgue_CD`).

## 3. Not proved (exact)
* `Core2` for an arbitrary `FullTriple`.
* `Core2` for the Gibbs triple `gibbsFull_unconditional` (general smooth `V`): would need `H⁴_w` regularity of the resolvent and a cut-off with
  control of `V'·χ'` terms in `L²(e^{-V})`; not attempted.  The Gibbs converse stays conditional on `Core2`.

## 4. Self-attack
* Vacuity: the hypotheses (`f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹`) are satisfied e.g. by every polynomial in OU/Lebesgue-type examples and by test functions; the theorem
  says all such `f` lie in `𝒟(L)` (already known for `f ∈ 𝒜 ∩ 𝒟(L)` by R14), so it is a genuine converse; non-triviality of the hypothesis class is only exercised through `Core2`.
* Junk values: `Ψₗ`, `Iₐ` are defined on the subtype `𝒜₀`; `L` total but only applied to `𝒜₀ ⊂ 𝒜`; no division by zero (cut-off scales `c_k = 1/(k+1) > 0`,
  `Rn n ≥ 1`).  `Tl` has no semantic content beyond the Prop-valued closure; all bounds are real inequalities.
* Instance hypotheses actually satisfied: `ouFull`, `lebesgueFull` are the library's own full triples; `ouFull_CD`, `lebesgue_CD` proved there.
* `core2_of_dense` does not assume density of anything but the stated range; `Dense (Set.range Ψₗ)` is proved in OU (Hermite span is dense via
  `hbasis.dense_span`), not assumed.
* ESA is not used in the new instance proofs beyond what `FullTriple` already packages inside `mem_domain_of_Γ₂`.

## 5. Attack surface (for the independent hostile audit)
1. The claim that no book argument avoids `Core2` (section 1): is there an argument using `ρ`, ergodicity or the extension of `Γ₂` to `𝒟(L)`
   (Prop 3.3.16) that reaches `f ∈ 𝒟(L)` directly?
2. `core2_of_dense`: the use of `Φₗ`/`Iₐ` identities `cls (Iₐ b) = cls b − Lcls b`, `Lcls (Iₐ b) = Lcls b − LLₗ b` (a.e. linearity of `L` on `𝒜₀`).
3. OU `LoLo_mul` and the bookkeeping of the eight terms; `Tl` closure lemmas (`Tl.D`, `Tl.X`, `Tl.Lop`), especially base case `x·deriv(c^jθ(c·)) = c^j (yθ')(c·)`.
4. `pf_approx2`: the memLp hypotheses for `deriv (Lo f)`, `Lo (deriv f)` (rewritten via `Lo_pf`, `deriv_pf`).
5. `Ψ_ae` identification `Ψₗ b = [g − 2Lg + L²g]` and `hL_mem_closure_Ψ` (scaling `((1+n)²)⁻¹`).
6. Lebesgue `LL_mul` (sixth-order bookkeeping 1,4,6,4,1), `iter_chiR`, `cutoff4_tendsto` (dominating function `6K·Σ|v^{(j)}|`),
   `lebesgueFull_core2` (identification `v'' − v⁗ = a''` from `v − v'' = a`).
7. Statement of `Core2` (unchanged from the previous round).
