import MarkovTriple.BGL.Theory.Strong.Instances
import MarkovTriple.BGL.Instances.OU.StrongFinal
import MarkovTriple.BGL.Instances.Lebesgue.StrongBound
import MarkovTriple.BGL.Instances.Lebesgue.GradBound
import MarkovTriple.BGL.Theory.Complete.Instances
import MarkovTriple.BGL.Theory.Extension.Main

/-! Axiom audit of the headline results of the strong-gradient / completeness / extension round. -/

#print axioms MarkovTriple.BGL.FullTriple.Γ₂_mul_left
#print axioms MarkovTriple.BGL.FullTriple.hessian_ineq
#print axioms MarkovTriple.BGL.FullTriple.reinforced_cd
#print axioms MarkovTriple.BGL.FullTriple.strong_integrated
#print axioms MarkovTriple.BGL.FullTriple.strong_eps
#print axioms MarkovTriple.BGL.FullTriple.strong_of_eps
#print axioms MarkovTriple.BGL.FullTriple.strong_gradient_bound
#print axioms MarkovTriple.BGL.CompactTriple.hasDerivAt_ucls
#print axioms MarkovTriple.BGL.CompactTriple.strongInterpolation
#print axioms MarkovTriple.BGL.compact_strong_gradient_bound
#print axioms MarkovTriple.BGL.Instances.OU.ouFull_StrongInterpolation
#print axioms MarkovTriple.BGL.Instances.OU.ouFull_strong_gradient_bound
#print axioms MarkovTriple.BGL.Lebesgue.lebesgue_strong_gradient_bound
#print axioms MarkovTriple.BGL.Lebesgue.lebesgue_hasGradientBound
#print axioms MarkovTriple.BGL.lebesgue_conservative_of_complete
#print axioms MarkovTriple.BGL.ouFull_conservative_of_complete
#print axioms MarkovTriple.BGL.lebesgueDiffusion_isComplete
#print axioms MarkovTriple.BGL.ouDiff_isComplete
#print axioms MarkovTriple.BGL.FullTriple.gamma_limits
