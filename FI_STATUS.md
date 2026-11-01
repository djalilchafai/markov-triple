# FunctionalInequalities status (Phase 4)

Files (MarkovTriple/FunctionalInequalities/): GapFromSquare, TripleSquare, Poincare, AxiomCheck (axioms: propext, Classical.choice, Quot.sound only).

Proved, no missing frozen field and no extra hypothesis:
- `Hilbert.gap_of_square` (abstract: UnitOp R, rho*<w-Rw,Rw> <= ||w-Rw||^2 for all w  ==>  rho||Rw||^2 <= <w-Rw,Rw> for w orthogonal to {Rn=n}; continuous functional calculus only).
- `FullMarkovTriple.integral_L`, `integral_Γ₂`, `rho_integral_le(_dim)` (finite mu), `Hilbert.fixed_const` (ErgodicL2 => fixed space of Friedrichs resolvent = constants), `square_all`, `rho_var_le`.
- `Hilbert.poincare_of_CD_infty` : [IsProbabilityMeasure F.μ], 0<ρ, F.toMarkovTriple.CD ρ ∞, ErgodicL2 ==> PoincareIneq (1/ρ).
- `Hilbert.poincare_of_CD_dim` : same with CD ρ n, 1<n≤∞ ==> PoincareIneq ((1-(n⁻¹).toReal)/ρ) (= (n-1)/(ρ n)).
Not done: extension of PI from A₀ to D(L̄) (needs Γ-integrability for f ∈ D(L̄) \ A₀; ibp_A only gives it against A₀).
