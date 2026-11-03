# STATEMENTS R16 Friedrichs (Armstrong method): `L²_loc ⇒ H¹_loc` for very weak solutions — written BEFORE the proofs

Files `EllipticFriedrichs*.lean`, namespace `MarkovTriple.BGL.Instances.GibbsRd.Elliptic` (generic part) and
`MarkovTriple.BGL.Instances.GibbsRd.EllData` (wrapper).  `X := Fin d → ℝ` (sup norm `‖·‖`), `d` arbitrary (`d = 0` allowed, all
statements trivially true there).  Textbook: Friedrichs, *The identity of weak and strong extensions of differential operators*,
Trans. AMS 55 (1944), 132-151 (Lemma 1: mollifier commutator); Gilbarg-Trudinger Lemma 7.1-7.3 (mollifier) and the proof of
Thm 8.8 / Lemma 8.? (interior `H²` via difference quotients; here replaced by mollification since `u ∈ L²_loc` only);
Hörmander, ALPDO I, Thm 4.1.? / Lemma 17.1.? is the same commutator; Evans §6.3.1 (energy estimate), §C.5 Thm 7 (mollifiers),
Hörmander Thm 4.4.? is not used.  (Page numbers are not asserted; the proof below is the standard one and is written out.)

## Setting (generic divergence form)
`b : Fin d → Fin d → X → ℝ`, all `b i j` smooth (`Sm`, Mathlib `∞`).  `Pop b φ := fun x => Σᵢ ∂ᵢ(Σⱼ bᵢⱼ ∂ⱼ φ)(x)` (`φ` smooth).
`b = w·a` for `EllData`: `w·(L φ) = Pop (w a) φ`.   Equation (very weak): `∫ u · Pop b a = ∫ F · a` for all `a ∈ C_c^∞`.
Ellipticity: for every compact `K` there is `λ > 0` with `Σ bᵢⱼ ξᵢ ξⱼ ≥ λ Σ ξᵢ²` on `K` (all `ξ`).  Symmetry `bᵢⱼ = bⱼᵢ` IS used (erratum R16-F3).

## K. Kernel
K1 `IsFrMollSeq ρ` : `IsMollSeq ρ` (smooth, compact support, `≥ 0`, `∫ = 1`, support in `‖x‖ < 1/(n+1)`), plus
   even `ρ n (-x) = ρ n x`, plus `∃ C₁ ≥ 0, ∀ n i, ∫ |∂ᵢρ_n(z)|·‖z‖ dz ≤ C₁` (scaling: `ρ_n(x) = (n+1)^d ρ_0((n+1)x)`).
   `exists_frMollSeq d : ∃ ρ, IsFrMollSeq ρ`.     [GT Lemma 7.1-7.2 + change of variables]
## Y. Young (L² form)
Y1 `k ≥ 0` integrable, `G ≥ 0` continuous with compact support (erratum R16-F2; `L²` only would not suffice pointwise), `c := ∫k`: `∫_x (∫_t k(t) G(x−t) dt)² ≤ c² ∫ G²` and the inner function is `L²`.
## C. Friedrichs commutator   [Friedrichs 1944 Lemma 1; GT Lemma 7.? ; Hörmander]
C1 (formula) `ρ` smooth cs, `φ` smooth cs, `gⱼ := ∂ⱼφ`:
   `moll ρ (Pop b φ) x − Pop b (moll ρ φ) x
      = Σᵢⱼ [ ∫(∂ᵢρ)(x−y)(bᵢⱼ(y)−bᵢⱼ(x)) gⱼ(y) dy − ∂ᵢbᵢⱼ(x)·moll ρ gⱼ x ]`.
C2 (estimate) for every `R₀ ≥ 0`, `C₁ ≥ 0` there is `C ≥ 0` (depending on `b, R₀, C₁, d`) such that for all `ρ` smooth cs `≥ 0`,
   `∫ρ = 1`, support in the unit ball, `∫|∂ᵢρ|‖z‖ ≤ C₁`, and all smooth `φ` supported in `closedBall 0 R₀`:
   `∫ (moll ρ (Pop b φ) − Pop b (moll ρ φ))² ≤ C · ∫ Σⱼ (∂ⱼφ)²`.   CONSTANT UNIFORM IN `ρ` (i.e. in `ε`).
   (Local, not global, Lipschitz bound: only `b` on `closedBall 0 (R₀+1)` enters.)
## E. Energy estimate
E1 (equation for the mollified function, test function `ρ⋆φ`) `u, F ∈ L²_loc`, `ρ` even smooth cs `≥0` `∫ρ=1` supp in unit ball,
   `φ` smooth cs: `∫ (ρ⋆u) · Pop b φ = ∫ (ρ⋆F) · φ + ∫ u · T_ρ φ`, `T_ρ φ := moll ρ (Pop b φ) − Pop b (moll ρ φ)`.
E2 (uniform H¹ bound; as proved, see erratum R16-F1: energy of `ζ·(ρ⋆u)`, global `L²` data) `ζ` smooth cs, `K ⊇ supp ζ` compact: `∃ C, ∀ n, ∫ ζ² |∇(ρ_n⋆u)|² ≤ C (∫_{K₁}u² + ∫_{K₁}F²)`, `K₁ = K + closedBall 0 1`;
   `C` independent of `n`.
## M. Main
M1 `sobolev_one_of_veryWeak` (generic): `b` smooth, locally uniformly elliptic, `u, F ∈ LocL2`, `∀ a ∈ A₀, ∫ u Pop b a = ∫ F a` ⇒ `Sobolev 1 u`.
M2 `EllData.sobolev_one_of_veryWeak`: `E : EllData d`, `u h ∈ LocL2`, `E.VeryWeakSol u h` ⇒ `Sobolev 1 u`   (the form feeding `EllReg`).
   (`F = h·w`, `b = w·a`; ellipticity of `w·a` on compacts from `local_ellipticity` and `exists_dens_lower`.)
Conclusion bound: for each cut-off `ζ` the `L²` norm of `∂ᵢ(ζ u)` is controlled by `‖u‖_{L²(K₁)}+‖F‖_{L²(K₁)}` (inside E2/M1).

## Honest limits (to be updated at the end)
Not claimed: any statement for non-smooth `a, w`; only `C^∞` coefficients (as in `EllData`).  `u ∈ H¹_loc` only: `H²_loc` etc. are the
other agent's files (`EllipticE*.lean`).

## STATUS (end of the round)
ALL of K1, Y1, C1, C2, E1, E2, M1, M2 PROVED (0 sorry; axioms propext/choice/Quot.sound; `AxiomCheckR16Friedrichs.lean`):
`exists_frMollSeq`, `conv_sq_le`/`integral_conv_sq`, `comm_formula`, `comm_bound`, `integral_moll_swap`, `test_eq`, `energy_identity`,
`energy_est`, `weakDeriv_of_approx`, `cutoff_h1`, `Elliptic.sobolev_one_of_veryWeak`, `EllData.sobolev_one_of_veryWeak`.
Proof route as in the statements (mollify; test with `ρ⋆(ζ²ρ⋆u)`; Friedrichs commutator; Caccioppoli; weak compactness; `weakDeriv_of_local`).
Not claimed: `H²_loc` / higher regularity (other agent), and the application to `EllReg` itself (the `EllReg` chain/Sobolev-embedding glue).
