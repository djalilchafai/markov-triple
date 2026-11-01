# Brownian triple on (R, Lebesgue) as a BGL FullTriple: findings

Result: `MarkovTriple.BGL.Lebesgue.lebesgueFull : FullTriple ℝ` (A0 = C_c^∞, A = C^∞, L f = f'', Γ = f'g'),
all of D1-D8, S10, S11, F1-F10 proved; also `lebesgue_CD ρ n` (ρ ≤ 0, 1 ≤ n ≤ ∞), `lebesgue_CD_zero_infty`,
`lebesgue_CD_zero_one`. No frozen field was unsatisfiable. Axioms: propext, Classical.choice, Quot.sound.

Proof architecture (no Fourier transform needed):
* Cutoff lemma: smooth u with u,u',u'' ∈ L² lies in D(L), Lu = u'' (closed generator + χ(x/n)).
* F10: Nelson-type argument using the explicit solution of v - v'' = ψ (ODE.lean), no regularity theory.
* S10: via `ergodic_iff_energy` + du Bois-Reymond (energy form of the closed form on D(E)).
* Semigroup = Gaussian smoothing on C_c^∞ (Identify.lean): Duhamel pairing <P_s f, Q_{t-s} ψ>; needs the
  strong L²-derivative of Gaussian smoothing (Heat.lean). S11 and F8 follow from this.
Audit remarks: none blocking. F2/F5/F9 read a.e. as in the surface; they hold (F2 proved via continuity).
Note `lebesgueDiffusion` is `@[reducible]` so that `Lp ℝ 2 lebesgueDiffusion.μ` unifies with `Lp ℝ 2 volume`.
