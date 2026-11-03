import MarkovTriple.BGL.Instances.Discrete.Obstruction
import MarkovTriple.BGL.Instances.Gibbs.Convex
import MarkovTriple.BGL.Instances.Gibbs.FunctFull
import MarkovTriple.BGL.Instances.Gibbs.RegMain

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
#print axioms MarkovTriple.BGL.PreFull.cutoff_estimate
#print axioms MarkovTriple.BGL.PreFull.gradient_eq_zero
#print axioms MarkovTriple.BGL.PreFull.const_of_weak
#print axioms MarkovTriple.BGL.DiffusionTriple.core_of_orth
#print axioms MarkovTriple.BGL.DiffusionTriple.ESAProp_of_weakHypo
#print axioms MarkovTriple.BGL.DiffusionTriple.ergodic_of_weakHypo
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_preFull
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_CD_pointwise
#print axioms MarkovTriple.BGL.Instances.Gibbs.exists_antideriv
#print axioms MarkovTriple.BGL.Instances.Gibbs.du_bois_reymond
#print axioms MarkovTriple.BGL.Instances.Gibbs.integral_mul_eq_neg_integral_primitive
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.reg_core
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.reg_core_smooth
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.weak_reg_C1
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.weak_reg_gain
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.weakHypo
#print axioms MarkovTriple.BGL.DiffusionTriple.resolvent_weak
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.resolvent_gain
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.resolvent_pow_reg
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.f8
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsDiff_esaProp_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsDiff_ergodic_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsStandard_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsFull_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsFull_CD_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbsFull_poincare_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_poincare_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_spectralGap_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.gibbs_expDecay_unconditional
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.weakHypo_premise_satisfiable
#print axioms MarkovTriple.BGL.Instances.Gibbs.GibbsData.afull_rep_unique
