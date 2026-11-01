# Circle instance: findings

`BGL.Circle.circleCompact : CompactTriple 𝕋` is fully proved (D1–D8, S10, S11, F1–F10, `𝒜 = 𝒜₀ = C^∞(𝕋)`,
Haar probability, `L f = f''`, `Γ(f,g) = f'g'`, `Γ ≠ 0`).  No frozen field is unsatisfiable for the circle;
no change to `BGL/Frozen/` is needed.

Remarks on the surface (not defects):
* F10 (`esa`) was proved from F8 through `DiffusionTriple.core_of_invariant` (the content of
  `CompactTriple.esa_auto`); `esa_auto` itself cannot be used to *build* the structure since it takes a
  `CompactTriple` that already contains `esa`.  A variant of `esa_auto` stated for a `FullTriple`-minus-`esa`
  (or just `core_of_invariant`, as used here) is what instance builders need.
* The `DiffusionTriple.semigroup` (Friedrichs) is tied to the Fourier action by
  `DiffusionTriple.semigroup_cls_eigen` (eigenvector of `L` in `𝒜₀` => eigenvector of `P_t`, via the resolvent),
  and the self-adjointness of `P_t`; no uniqueness theorem is needed.
* `FullTriple.CD` is on all of `𝒜`; on the circle it holds for every `ρ ≤ 0`, `n ∈ [1, ∞]`
  (`Γ₂(f) = (f'')²`).
* Elaboration note: `cT.μ` (a projection of a `def`) is not reducibly `μ₀`; the code uses wrappers
  `semigroupC`, `RC`, `one2C` stated on `Lp ℝ 2 μ₀`.
