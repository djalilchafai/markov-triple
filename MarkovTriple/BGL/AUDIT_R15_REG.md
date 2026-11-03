# Hostile audit: round 15, Gibbs weak hypo-ellipticity and F8 proved (branch commit a79a2ca)

Independent auditor. **Result: no soundness defect, misformalization or vacuity.** `WeakHypo` (Def 3.3.8) and `F8` (Def 3.3.1 (viii)) are
proved for every `GibbsData`; the definitions were not weakened (all lambda, all t : NNReal, all f in A0; conclusion is a smooth representative,
non-trivial; premise satisfiable; `afull_rep_unique` holds by full support).
Findings (documentation only, both addressed): (1) `RegHypo.lean` header cited Sect. 1.12 as p. 157 (that page is Def 3.3.8; Sect 1.12 is p. 49): fixed.
(2) `DiffusionTriple.resolvent_weak` is general but lives in a Gibbs file: noted for a later move, no change.
Checked: frozen OK; 8 modules recompiled from scratch, 0 errors/warnings; axioms only propext/Classical.choice/Quot.sound; bridge `resolvent_weak`
sign conventions and use of the library's Friedrichs resolvent and `cfcSemigroup_eq_pow_mul`; du Bois-Reymond / AC integration by parts; a.e. to
mu-a.e. transfer; C-infinity orders and casts. Moderate depth only on `FunctAlgebra`/`FunctESA` definitions (grepped), `formA_apply` not re-derived.
