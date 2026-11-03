import MarkovTriple.BGL.Theory.Gamma2Integral
import MarkovTriple.BGL.Theory.ESAOne
import MarkovTriple.BGL.Theory.Poincare
import MarkovTriple.BGL.Theory.ALevel
import MarkovTriple.BGL.Theory.GammaCalculus
import MarkovTriple.BGL.Theory.GradientBound
import MarkovTriple.BGL.Theory.LogSobolev
import MarkovTriple.BGL.Theory.Convergence
import MarkovTriple.BGL.Theory.LogSobolevMain
import MarkovTriple.BGL.Theory.Tests
import MarkovTriple.BGL.Theory.LogSobolevDim
import MarkovTriple.BGL.Theory.LSToPI
import MarkovTriple.BGL.Theory.LogSobolevDimOne

/-! Axiom audit of `BGL/Theory` (the build log must show only `propext`, `Classical.choice`,
`Quot.sound`). -/

-- (1) integrated Γ₂ and CD, extension to D(L)
#print axioms MarkovTriple.BGL.FullTriple.integral_Γ₂
#print axioms MarkovTriple.BGL.FullTriple.integral_CD
#print axioms MarkovTriple.BGL.FullTriple.CD_integrated_domain
#print axioms MarkovTriple.BGL.FullTriple.CD_form_domain
-- (2) Poincaré / Lichnerowicz
#print axioms MarkovTriple.BGL.DiffusionTriple.square_all
#print axioms MarkovTriple.BGL.DiffusionTriple.rho_var_le_of
#print axioms MarkovTriple.BGL.FullTriple.poincare_of_CD_infty
#print axioms MarkovTriple.BGL.FullTriple.poincare_of_CD_dim
#print axioms MarkovTriple.BGL.FullTriple.poincare_extend_domain
-- (4) mass conservation, finite measure: derived from ESA
#print axioms MarkovTriple.BGL.DiffusionTriple.R_one2
#print axioms MarkovTriple.BGL.DiffusionTriple.one2_mem_domain
#print axioms MarkovTriple.BGL.DiffusionTriple.semigroup_one2
#print axioms MarkovTriple.BGL.DiffusionTriple.conservative_of_esa
-- A-level calculus
#print axioms MarkovTriple.BGL.FullTriple.L_congr_A
#print axioms MarkovTriple.BGL.FullTriple.ΓA_congr_A
#print axioms MarkovTriple.BGL.FullTriple.ΓA_comp_comp
#print axioms MarkovTriple.BGL.FullTriple.ΓA_sq
-- (3) gradient bound (conditional on GradientInterpolation)
#print axioms MarkovTriple.BGL.FullTriple.gradient_integrated
#print axioms MarkovTriple.BGL.FullTriple.gradient_bound
-- (5) LSI (conditional on EntropyInterpolation)
#print axioms MarkovTriple.BGL.FullTriple.tendsto_entE
#print axioms MarkovTriple.BGL.DiffusionTriple.hasSpectralGap_of_PI
#print axioms MarkovTriple.BGL.FullTriple.hasSpectralGap_of_CD_dim
#print axioms MarkovTriple.BGL.FullTriple.ent_le_fisher
#print axioms MarkovTriple.BGL.FullTriple.logSobolev_of_CD_infty
#print axioms MarkovTriple.BGL.FullTriple.logSobolev_extend_domain
-- witnesses that the hypotheses are satisfiable
#print axioms MarkovTriple.BGL.Sanity.TT_GradientInterpolation
#print axioms MarkovTriple.BGL.Sanity.TT_EntropyInterpolation
#print axioms MarkovTriple.BGL.Sanity.TT_PI
-- (6) LSI under CD(ρ,n), n < ∞ (BGL Thm 5.7.4); Part A unconditional, Part B conditional on the named structures
#print axioms MarkovTriple.BGL.FullTriple.Γ₂_exp
#print axioms MarkovTriple.BGL.FullTriple.integral_exp_L_Γ
#print axioms MarkovTriple.BGL.FullTriple.integral_exp_sq_L
#print axioms MarkovTriple.BGL.FullTriple.integral_exp_Γ₂_ge
#print axioms MarkovTriple.BGL.FullTriple.integral_exp_Γ₂_ge'
#print axioms MarkovTriple.BGL.dimLSConst_lt
#print axioms MarkovTriple.BGL.dimLSConst_eq
#print axioms MarkovTriple.BGL.dimLSConst_tendsto
#print axioms MarkovTriple.BGL.FullTriple.ent_le_fisher_dim
#print axioms MarkovTriple.BGL.FullTriple.logSobolev_of_finiteDim
#print axioms MarkovTriple.BGL.FullTriple.logSobolev_of_CD_dim
#print axioms MarkovTriple.BGL.CompactTriple.finiteDimInterpolation
#print axioms MarkovTriple.BGL.CompactTriple.compact_logSobolev_dim
-- (7) R15: LS => PI (BGL Prop. 5.1.3), case n = 1 of Thm 5.7.4 (BGL p. 272-273)
#print axioms MarkovTriple.BGL.log_sq_lower
#print axioms MarkovTriple.BGL.DiffusionTriple.Γ_one_left
#print axioms MarkovTriple.BGL.DiffusionTriple.sq_integral_le_of_LS
#print axioms MarkovTriple.BGL.DiffusionTriple.PI_of_LS
#print axioms MarkovTriple.BGL.DiffusionTriple.not_PI_of_eigen_pos
#print axioms MarkovTriple.BGL.DiffusionTriple.not_PI_of_eigen
#print axioms MarkovTriple.BGL.CompactTriple.PI_of_LS
#print axioms MarkovTriple.BGL.FullTriple.integral_Γ_le_of_PI
#print axioms MarkovTriple.BGL.FullTriple.integral_exp_Γ₂_ge_one
#print axioms MarkovTriple.BGL.FullTriple.tendsto_entE_of_PI
#print axioms MarkovTriple.BGL.FullTriple.ent_le_fisher_of_PI
#print axioms MarkovTriple.BGL.FullTriple.logSobolev_of_PI_finiteDim
#print axioms MarkovTriple.BGL.CompactTriple.finiteDimInterpolation_one
#print axioms MarkovTriple.BGL.CompactTriple.compact_logSobolev_one
#print axioms MarkovTriple.BGL.CompactTriple.compact_LS_iff_PI_of_CD_zero_one
