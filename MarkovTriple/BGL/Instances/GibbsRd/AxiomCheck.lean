import MarkovTriple.BGL.Instances.GibbsRd.Main
import MarkovTriple.BGL.Instances.GibbsRd.Compat1D
import MarkovTriple.BGL.Instances.GibbsRd.Probes

/-! Axiom audit of `BGL/Instances/GibbsRd` (the build log must show only `propext`, `Classical.choice`,
`Quot.sound`). -/

-- calculus
#print axioms MarkovTriple.BGL.Instances.GibbsRd.pderiv_comp
#print axioms MarkovTriple.BGL.Instances.GibbsRd.pderiv_symm
#print axioms MarkovTriple.BGL.Instances.GibbsRd.integral_pderiv_eq_zero
#print axioms MarkovTriple.BGL.Instances.GibbsRd.comp_mem_A₀
#print axioms MarkovTriple.BGL.Instances.GibbsRd.sum_sq_pderiv_cut_le
-- generic weighted elliptic operator (Part A)
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.ibp_master
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.ibp_sm
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.L_mul
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.Γ_comp
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.L_comp
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.diff
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.ΓA_eq
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.diff_isComplete
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.preFull
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.diff_esaProp
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.diff_ergodic
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.integral_Γ₂
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.integrated_CD
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.ell_poincare
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.ell_spectralGap
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.ell_expDecay
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.standard
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.full
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.full_CD
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.full_poincare
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.full_logSobolev
#print axioms MarkovTriple.BGL.Instances.GibbsRd.EllData.full_gradient_bound
-- Gibbs on ℝ^d (Part B)
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.toEll
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.toEll_Γ
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.toEll_L
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRdDiff
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRdDiff_isComplete
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRd_Γ₂_eq
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRd_curv
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRd_integral_Γ₂
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRd_integrated_CD
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRd_poincare
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRd_spectralGap
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRd_expDecay
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRdFull
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRdFull_CD
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRdFull_poincare
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRdFull_logSobolev
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.gibbsRdFull_gradient_bound
#print axioms MarkovTriple.BGL.Instances.GibbsRd.quad_lower_rd
#print axioms MarkovTriple.BGL.Instances.GibbsRd.integrable_of_convex_rd
#print axioms MarkovTriple.BGL.Instances.GibbsRd.GibbsRdData.ofConvex
#print axioms MarkovTriple.BGL.Instances.GibbsRd.hessGe_gauss
#print axioms MarkovTriple.BGL.Instances.GibbsRd.gaussData
#print axioms MarkovTriple.BGL.Instances.GibbsRd.gaussData_curv
-- consistency with the 1-D Gibbs development
#print axioms MarkovTriple.BGL.Instances.GibbsRd.Gr_restr1
#print axioms MarkovTriple.BGL.Instances.GibbsRd.Lr_restr1
-- self-audit probes
#print axioms MarkovTriple.BGL.Instances.GibbsRd.gauss_not_curv_two
#print axioms MarkovTriple.BGL.Instances.GibbsRd.hess_gauss
