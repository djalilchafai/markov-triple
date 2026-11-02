import MarkovTriple.BGL.Instances.Discrete.Obstruction
import MarkovTriple.BGL.Instances.Gibbs.Convex
import MarkovTriple.BGL.Instances.Gibbs.FunctFull

/-! Axiom audit of `BGL/Instances/Discrete` and `BGL/Instances/Gibbs` (the build log must show only `propext`,
`Classical.choice`, `Quot.sound`). -/

#print axioms MarkovTriple.BGL.Instances.Discrete.finite_Γ_ae_zero
#print axioms MarkovTriple.BGL.Instances.Discrete.finite_L_ae_zero
#print axioms MarkovTriple.BGL.Instances.Discrete.finite_standard_const
#print axioms MarkovTriple.BGL.Instances.Gibbs.diffusion_g
#print axioms MarkovTriple.BGL.Instances.Gibbs.Γ₂_eq
#print axioms MarkovTriple.BGL.Instances.Gibbs.Γ₂_ge
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsDiff
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsDiff_isComplete
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsDiff_Γ₂_ge
#print axioms MarkovTriple.BGL.Instances.Gibbs.quad_lower
#print axioms MarkovTriple.BGL.Instances.Gibbs.integrable_of_convex
#print axioms MarkovTriple.BGL.Instances.Gibbs.gibbs_convex
#print axioms MarkovTriple.BGL.Instances.Gibbs.ouData_μ
#print axioms MarkovTriple.BGL.Instances.Gibbs.ouData_L

-- Gibbs functional-inequality route (Funct*.lean)
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.ibp_sm
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.Lg_eq_of_weak
#print axioms MarkovTriple.BGL.Instances.Gibbs.zero_of_cutoff
#print axioms MarkovTriple.BGL.Instances.Gibbs.cutoff_ineq
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.cutoff_conclusion
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsDiff_esaProp
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsDiff_ergodic
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_integral_Γ₂
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_integrated_CD
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_integrated_CD_cls
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_poincare
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_spectralGap
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_expDecay
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.pos_detect_aux
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsStandard
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsFull
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsFull_CD
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsFull_poincare
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsFull_logSobolev
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsFull_gradient_bound
#print axioms MarkovTriple.BGL.DiffusionTriple.esaProp_of_orth
