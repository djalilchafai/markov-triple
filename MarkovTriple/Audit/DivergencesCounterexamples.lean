import MarkovTriple
/-! Junk-value witnesses for the hostile audit of `Divergences` (not imported by the root). -/
open MeasureTheory MarkovTriple
open scoped ENNReal

/-- `Ent` is not nonnegative / does not vanish on constants for non-probability `μ`. -/
example : Ent (2 • Measure.dirac (0:ℝ)) (fun _ => (1:ℝ)) = -(2 * Real.log 2) := by
  have h : (2 • Measure.dirac (0:ℝ)).real Set.univ = 2 := by simp [Measure.real]
  simp [Ent, h]

/-- `wassersteinSq μ μ = 0` for a mass-2 measure, whereas the cutoff-fastdiff variant
(probability couplings only) is `⊤` there: the infimum is over the empty family. -/
example : Gelbrich.wassersteinSqP (d := 1)
    (2 • Measure.dirac (0 : EuclideanSpace ℝ (Fin 1))) (2 • Measure.dirac 0) = ⊤ := by
  unfold Gelbrich.wassersteinSqP
  refine le_antisymm le_top (le_iInf fun γ => le_iInf fun hγ => le_iInf fun h1 => le_iInf fun h2 => ?_)
  exfalso
  have := congrArg (fun m => m Set.univ) h1
  simp [Measure.map_apply measurable_fst MeasurableSet.univ] at this

example : wassersteinSq (2 • Measure.dirac (0 : ℝ)) (2 • Measure.dirac 0) = 0 :=
  wassersteinSq_self _

/-- Total variation junk value for an infinite measure: the set of values is unbounded, `sSup = 0`. -/
example : totalVariationDistance (volume : Measure ℝ) 0 = 0 := by
  unfold totalVariationDistance
  apply Real.sSup_of_not_bddAbove
  rintro ⟨B, hB⟩
  obtain ⟨n, hn⟩ := exists_nat_gt B
  have := hB ⟨Set.Icc 0 (n:ℝ), measurableSet_Icc, rfl⟩
  simp [Measure.real] at this
  linarith
