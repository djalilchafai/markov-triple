# STATEMENTS R16 Elliptic (Armstrong method): elliptic half of interior regularity — written BEFORE the proofs

Namespace `MarkovTriple.BGL.Instances.GibbsRd.Elliptic`; files `EllipticDefs.lean`, `EllipticDiffQuot.lean`, ...
Textbook: Evans PDE §6.3 Thm 1 (interior H^2), Thm 2 (higher regularity), §5.8.2 Thm 3 (difference quotients);
Gilbarg–Trudinger Thm 8.8, 8.10, Lemma 7.24.  `d` arbitrary (d = 0 allowed: ℝ^0 is a point).

## D. Definitions
D1 `WeakDeriv f g i` (shared text with the Sobolev agent): `LocallyIntegrable f ∧ LocallyIntegrable g ∧
   ∀ φ, ContDiff ℝ (⊤:ℕ∞) φ → HasCompactSupport φ → ∫ f · ∂ᵢφ = −∫ g · φ`.
   **Deviation (erratum R16-E1)**: the shared text writes `ContDiff ℝ ⊤ φ`; in current Mathlib `⊤ : WithTop ℕ∞` is `ω`
   (ANALYTIC), and a compactly supported analytic function on ℝ^d (d ≥ 1) is 0, so the text as given makes the test clause
   vacuous (every locally integrable g would be a weak derivative of every locally integrable f).  We use `C^∞`,
   i.e. `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ` (= `Sm φ` of `Calculus.lean`, Mathlib's `∞`).
D2 `LocL2 f := ∀ K compact, MemLp f 2 (volume.restrict K)`.
D3 `Sobolev : ℕ → (ℝ^d → ℝ) → Prop`: `Sobolev 0 f := LocL2 f`;
   `Sobolev (k+1) f := LocL2 f ∧ ∀ i, ∃ g, WeakDeriv f g i ∧ Sobolev k g`  (all iterated weak partials up to order k+1 exist, are LocL2).

## B. Basic calculus of D (proved in `EllipticDefs.lean`)
B1 `LocL2 f → LocallyIntegrable f`.   B2 uniqueness `WeakDeriv f g i → WeakDeriv f g' i → g =ᵐ g'`.
B3 `Sm f → WeakDeriv f (pderiv f i) i`.   B4 `WeakDeriv` is stable under a.e. modification, sums, scalars.
B5 product rule: `Sm ψ → WeakDeriv f g i → WeakDeriv (ψ f) (ψ g + ∂ᵢψ f) i`.
B6 `Sobolev` mono in k, closed under sums, scalars, `Sm` (all k), products with `Sm ψ`.

## Q. Difference quotients (`EllipticDiffQuot.lean`)  [Evans §5.8.2 Thm 3(i)–(ii)]
Q1 `dq i h f x := (f (x + h e_i) − f x)/h`; IBP `∫ dq i h f · φ = −∫ f · dq i (−h) φ` (f locally integrable, φ continuous compactly supp.).
Q2 (global criterion) f ∈ L²(ℝ^d), hₙ → 0, hₙ ≠ 0, ‖dq i hₙ f‖₂ ≤ C ⇒ ∃ g ∈ L², WeakDeriv f g i, ‖g‖₂ ≤ C
   (Hilbert-space weak sequential compactness; Evans Thm 3(ii)).
Q3 (converse, if time) `WeakDeriv`-L² ⇒ ‖dq i h f‖₂ ≤ ‖∂ᵢf‖₂ (Evans Thm 3(i)).

## E. Elliptic regularity — TARGET (NOT claimed delivered; see "Status")
E0 Weak equation (`resolvent_weak`/`EllReg` form, μ = Z⁻¹ w dx, so the factor Z⁻¹ drops):
   `WeakSol E u h := ∀ a ∈ A₀ d, ∫ u · (E.L a) · w dx = ∫ h · a · w dx`, `u`, `h` `LocL2`.
E1 (interior H¹) hypothesis `Sobolev 1 u` (energy class) added: then for every smooth compactly supported ζ,
   Caccioppoli `∫ ζ² Γ(u) w ≤ C(∫_{supp ζ} (u² + h²) w)`.
E2 (interior H², Evans Thm 1): `WeakSol E u h`, `Sobolev 1 u`, `Sobolev 0 h` ⇒ `Sobolev 2 u`.
E3 (Evans Thm 2): `Sobolev k h`, `Sobolev 1 u`, `WeakSol E u h` ⇒ `Sobolev (k+2) u`.
E4 = `interior_regularity_step` (assignment): same with `Sobolev 1 u` REPLACED by `LocL2 u` only.
   E4 needs in addition the L²_loc ⇒ H¹_loc step (Friedrichs mollifier commutator; see audit): NOT in Evans (Evans assumes u ∈ H¹).

## C. Caccioppoli, SMOOTH solutions only (`EllipticCaccioppoli.lean`) — added during the work, same Armstrong discipline
C1 `EllData.caccioppoli_identity`: `u, ζ` smooth, `ζ` compact support: `∫ w Γ(ζu,ζu) = −∫ w ζ² u Lu + ∫ w u² Γ(ζ,ζ)`.
C2 `EllData.caccioppoli`: `∫ w ζ² Γ(u,u) ≤ −2 ∫ w ζ² u Lu + 4 ∫ w u² Γ(ζ,ζ)`   (Evans §6.3.1 Thm 1 Step 1; G–T (8.28)).
   NOT claimed for `H¹_loc` weak solutions (needs density of `C_c^∞` in `H¹_c`).

## Status at end of the round (honest)
PROVED (Lean, 0 sorry, axioms propext/choice/Quot.sound): D1–D3, B1, B2, B3, B4 (add, const_mul only; no a.e.-congruence lemma),
B5, B6 (`Sobolev.mono/add/of_smooth/smooth_mul`, `LocL2.*`), Q1 (`dq_ibp`, `dq_tendsto`, `memLp_dq`), Q2
(`weakDeriv_of_bounded_dq`, with `weak_subseq`), C1, C2.
OPEN (exact statements in `AUDIT_R16_ELLIPTIC_SELF.md`, section "What remains"): Q3 (derivative ⇒ bounded quotients), localisation/gluing of
Q2 to `L²_loc`, density of `C_c^∞` in `H¹_c` (mollifiers), extension of the weak form to `H¹_c` test functions, E1 (weak Caccioppoli),
E2 (`H²_loc`), E3 (higher regularity, differentiating the equation), E4 (`interior_regularity_step`, from `L²_loc` only: also the
Friedrichs step `L²_loc ⇒ H¹_loc`).  `interior_regularity_step` is therefore NOT delivered.
