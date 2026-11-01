# OU as a BGL `FullTriple` — findings

Files: `Diffusion.lean` (D1–D8), `Semigroup.lean` (Friedrichs semigroup facts, F10, S10, S11),
`Full.lean` (`ouStandard`, `ouFull`, `ouFull_CD`).  No frozen field was unsatisfiable; nothing is
postponed.

## Audit observations (none blocking)
* Exhaustion (Def 3.1.1): the old cutoff `ψ0(c x)` (Mathlib `ContDiffBump`) cannot be shown radially
  monotone (the bump base is abstract), so a new explicit exhaustion is used:
  `u_n(x) = smoothTransition(2 − (x/(n+1))²)` — pointwise increasing, in `C_c^∞`, `→ 1` pointwise.
* S10/F10 route: F10 (core) is derived from density of `(1 − L)C_c^∞` in `L²` (old `ou_esa`, Hermite
  basis + `cutoff_approx`) and `R = (1−G)⁻¹` of the Friedrichs generator (`R_cls_sub`); S10 then follows
  from F10 + the old Hermite orthogonality argument (`ou_ergodic_aux`).  The BGL `semigroup`/`generator`
  satisfy `IsSG` + the generator clause on `C_c^∞`, which is all the old Hermite/Mehler machinery used,
  so eigenfunction (`Pt_hL`), smoothing (`Pt_smooth`, F8), Mehler (`Pt_mehler`) transfer verbatim.
* S11 uses the finite-measure criterion `conservative_of_semigroup_one` with `P_t 1 = 1`
  (`He_0 = 1` is the eigenvalue-0 eigenfunction); holds for every exhaustion sequence, not only
  nonnegative ones.
* F2 `pos_detect` (a.e. reading) and F9 `connected` (a.e. reading) hold; they use that `γ` charges open sets.
* `Instances/OU` imports old `Sanity/OU/*` (which import old `Frozen/*`); the old and new `pderiv`,
  `pderiv₂` are definitionally equal (checked by `rfl`).
