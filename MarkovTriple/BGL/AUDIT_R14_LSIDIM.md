# Hostile audit: round 14, finite-dimensional LSI (BGL Thm 5.7.4)

Independent auditor (did not write the code; compared against the book text pp. 270-272). Branch commit `dcf9a56`.

**Result: no soundness defect, no misformalization, no vacuity.** Three minor documentation findings (all fixed, ERRATA R14-3):
1. `LogSobolevDim.lean` header named Prop. 5.7.3 as the route; the proof is the Prop. 5.7.1 argument with decay `I' <= -2 kappa I`.
2. The `e^{g/2} in A0` hypothesis of (5.7.8)-(5.7.12) (book: via Prop. 3.3.17, unstated) is a scope caveat; discharged on compact triples.
3. `FiniteDimInterpolation kappa` is parametrized by arbitrary kappa (vacuous for kappa > rho n/(n-1)); the headline theorem pins kappa.

Checked correct: (5.7.6) `Gamma2_exp`, (5.7.7), (5.7.8) at a=1/2, the a = 3/(2(n+2)) step, (5.7.10)-(5.7.12) coefficients (rho n/(n-1), (4n-1)/(4(n+2)^2)); `dimLSConst`, LS convention Ent(f^2) <= 2C E(f) (Def. 5.1.1); n <= 1 and n = infinity excluded; `FiniteDimInterpolation` neither trivial nor contradictory (proved for every `CompactTriple`); `sphere_LS_dim : LS (1/3) 0` matches the sharp S^3 constant 1/n.
Structural: frozen check OK; the 3 new modules recompiled from scratch with 0 errors/warnings; axioms only propext, Classical.choice, Quot.sound; no sorry/admit/axiom/native_decide/set_option.
Not inspected: the proofs inside pre-existing `BE.*` / `entE` infrastructure.
