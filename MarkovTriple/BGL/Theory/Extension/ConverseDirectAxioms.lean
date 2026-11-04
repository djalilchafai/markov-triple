import Mathlib
import MarkovTriple.BGL.Theory.Extension.ConverseDirectInst

/-!
# Axiom check for Round 20 D3 (`mem_domain_of_Γ₂_direct`, no `Core2`)

## DIFFERENCE FROM BGL

The book's converse of Prop. 3.3.17 uses the `L²`-core step (`Core2`); the theorems checked here replace it by the cut-off
`Γ₂` identity (BGL Prop. 3.2.1 technique) and need completeness instead.  This file only prints axioms (expected:
`propext`, `Classical.choice`, `Quot.sound`).
-/

#print axioms MarkovTriple.BGL.FullTriple.mem_domain_of_maximal
#print axioms MarkovTriple.BGL.FullTriple.hessCS
#print axioms MarkovTriple.BGL.FullTriple.cutoff_Γ₂_identity
#print axioms MarkovTriple.BGL.FullTriple.cutoff_bound
#print axioms MarkovTriple.BGL.FullTriple.memLp_L_of_Γ₂
#print axioms MarkovTriple.BGL.FullTriple.mem_domain_of_Γ₂_direct
#print axioms MarkovTriple.BGL.Instances.OU.ou_mem_domain_of_Γ₂_direct
#print axioms MarkovTriple.BGL.Instances.OU.ou_id_mem_domain
#print axioms MarkovTriple.BGL.Instances.circle_mem_domain_of_Γ₂_direct
#print axioms MarkovTriple.BGL.Instances.lebesgue_mem_domain_of_Γ₂_direct
#print axioms MarkovTriple.BGL.ConverseDirectInst.ell_mem_domain_of_Γ₂_direct
#print axioms MarkovTriple.BGL.ConverseDirectInst.riem_mem_domain_of_Γ₂_direct
