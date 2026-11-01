# `BEStable ouFull` and the Gaussian LSI (files `MarkovTriple/Sanity/OU/Mehler*.lean`, `BEReg.lean`, `BEStable.lean`)

Result: `ouFull_BEStable : BE.BEStable ouFull`, `ou_lsi : ouFull.toMarkovTriple.LogSobolevIneq (1/1)`;
only `propext, Classical.choice, Quot.sound`; no sorry; BEStable was NOT weakened (no BE*.lean edit).
The audit found no obstruction: `BEReg (ψ ∘ g)` holds for ALL smooth `ψ`, since `g = P_sφ` is a Schwartz function.

Route:
1. `Mehler.lean`: `Mh a c f x = ∫ f(a x + c y) dγ(y)`, `f ∈ C_c^∞`; `(Mh f)' = a Mh f'`
   (dominated differentiation), smooth, `(Mh f)^{(n)} = aⁿ Mh f^{(n)}`, `|x|^m |Mh f x| ≤ C_m`
   (from `|a x| ≤ R + |c||y|` on the support), hence `mehlerS : 𝓢(ℝ,ℝ)` (Mathlib `SchwartzMap`).
2. `MehlerHermite.lean`: `∫ He_n(a z + b w) dγ(w) = aⁿ He_n(z)` for `a²+b²=1` (Gaussian IBP + recurrence).
3. `MehlerEq.lean`: `coeff_Mh`: `⟨h_n, Mh f⟩ = aⁿ⟨h_n, f⟩` by Fubini + rotation invariance of `γ⊗γ`
   (`IsGaussian.map_rotation_eq_self`).  `mehler_ae`: `P_t [f] =ᵐ Mh e^{-t} √(1-e^{-2t}) f` for every
   semigroup witness of `IsSemigroupOf ouTriple` and `t : ℝ≥0` (compares Hermite coefficients with
   `hasSum_P`/`eigen_hL`; completeness `eq_zero_of_orth_hL`).
4. `BEReg.lean`: for `G : 𝓢(ℝ,ℝ)`, `ψ` smooth: `(ψ∘G)' = (ψ'∘G) G'` is Schwartz (`ψ'∘G` has temperate growth
   by a bump cutoff `ψ'·χ`, `χ = 1` on the range of `G`); `Lo`, `Γ` of it are Schwartz (operators `Ls`),
   so `ψ∘G, L(ψ∘G), Γ(ψ∘G)` bounded and `LL(ψ∘G), LΓ(ψ∘G)` bounded hence `L²` (probability measure).
5. `BEStable.lean`: a.e. equality of the smooth representative `g` with `Mh` is upgraded to equality
   (continuity + `γ` open-positive), then `beReg_comp_schwartz`.
