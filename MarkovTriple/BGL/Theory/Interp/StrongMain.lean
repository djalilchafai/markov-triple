import Mathlib
import MarkovTriple.BGL.Theory.Interp.Setup

/-!
# `StrongInterpolation` for EVERY `FullTriple` (BGL Lemmas 3.3.20-3.3.21 and proof of Thm 3.3.18, pp. 163-164)

`FullTriple.strongInterpolation : T.CD ρ n → T.StrongInterpolation` (no compactness).  Route of the book:
`G_ε = ψ_ε(Γ(P_{t-s}f)) ∈ 𝒟(ℰ)` (Lemma 3.3.20, `lemma3320`), `d/ds ∫ P_s h G_ε = ∫ L P_s h · G_ε + ∫ P_s h ∂_s G_ε` (`hasDerivAt_pair`,
the justification of the differentiation, which is only sketched in the book), `∫ L k · G = ∫ k L G` (`ibp_of_domain` + `ibp_bdd`,
the "by density" step of Lemma 3.3.21), `∂_s u = -2 Γ(g, Lg)` (`GB`, `hasDerivAt_uK`).
The converse of Prop. 3.3.17 is not used.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal InnerProductSpace

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable {T : FullTriple E}

lemma strongPhi_eq (ε : ℝ) (f h : T.A₀) (t : ℝ≥0) (r : ℝ) :
    T.strongPhi ε f h t r = ∫ x, T.orb h r x * psiS ε (T.ucurve f t r x) ∂T.μ := by
  unfold strongPhi
  refine integral_congr_ae ?_
  filter_upwards [T.Pt_ae r.toNNReal h, T.ucurve_ae f t r] with x a b
  have a' : (T.orb h r : E → ℝ) x = T.Pt r.toNNReal h x := a
  rw [a', b]

theorem strongInterpolation {ρ : ℝ} {n : ℝ≥0∞} (hCD : T.CD ρ n) : T.StrongInterpolation where
  continuousOn := by
    intro ε hε f h _ t
    have hc : Continuous (fun r => ∫ x, T.orb h r x * psiS ε (T.ucurve f t r x) ∂T.μ) :=
      continuous_pair (psiS_measurable hε) (psiS_zero hε) (fun a b ha hb => psiS_hH hε ha hb)
        (continuous_ucurve f t) (ucurve_nonneg f t) (T.continuous_orb h)
    have : T.strongPhi ε f h t = fun r => ∫ x, T.orb h r x * psiS ε (T.ucurve f t r x) ∂T.μ :=
      funext (strongPhi_eq ε f h t)
    rw [this]; exact hc.continuousOn
  hasDerivAt := by
    intro ε hε f h _ t s hs
    obtain ⟨hs0, hst⟩ := hs
    have hτ0 : 0 < (t : ℝ) - s := by linarith
    set g := T.Pt ((t : ℝ) - s).toNNReal f with hg
    set k := T.Pt s.toNNReal h with hk
    have hgA : g ∈ T.A := T.Pt_mem_A _ f
    have hg2 : MemLp g 2 T.μ := T.Pt_memLp _ f
    have hgu := Pt_mem_dom f ((t : ℝ) - s)
    have hkA : k ∈ T.A := T.Pt_mem_A _ h
    have hk2 : MemLp k 2 T.μ := T.Pt_memLp _ h
    have hku := Pt_mem_dom h s
    have hkQ := Pt_mem_Q h s
    have hLg2 : MemLp (T.L g) 2 T.μ := T.memLp_L_Pt f _
    have hLgQ : hLg2.toLp (T.L g) ∈ T.formDomain := by
      rw [show hLg2.toLp (T.L g) = T.orb (T.Lt f) ((t : ℝ) - s) from T.toLp_L_Pt f _]
      exact T.orb_mem_Q _ _
    obtain ⟨hG2, hQG⟩ := lemma3320 hCD hgA hg2 hgu hε
    have hGA := psiS_comp_mem (T := T) (g := g) hgA hε
    have hLG := integrable_L_psi hCD hgA hg2 hgu hε hLg2 hLgQ
    -- bound on k
    obtain ⟨C0, hC0⟩ := T.toDiffusionTriple.bounded h.1 h.2
    have hMpos : 0 < |C0| + 1 := by positivity
    have hkb0 : ∀ᵐ x ∂T.μ, |(T.orb h s : E → ℝ) x| ≤ |C0| + 1 := by
      refine ae_abs_semigroup_le T.toDiffusionTriple hMpos ?_ s.toNNReal
      filter_upwards [DiffusionTriple.coeFn_cls T.toDiffusionTriple h] with x hx
      rw [hx]; exact (hC0 x).trans (by linarith [le_abs_self C0])
    have hkb : ∀ᵐ x ∂T.μ, |k x| ≤ |C0| + 1 := by
      filter_upwards [hkb0, T.Pt_ae s.toNNReal h] with x h1 h2
      have : (T.orb h s : E → ℝ) x = k x := h2
      rw [← this]; exact h1
    -- curves
    have hU : HasDerivAt (T.ucurve f t) (-(GB T (T.cK (T.Lt f) ((t : ℝ) - s)) (T.cK f ((t : ℝ) - s)) +
        GB T (T.cK f ((t : ℝ) - s)) (T.cK (T.Lt f) ((t : ℝ) - s)))) s :=
      HasDerivAt.comp_const_sub (f := fun σ => GB T (T.cK f σ) (T.cK f σ)) (t : ℝ) s
        (T.hasDerivAt_uK f hτ0)
    have hK : HasDerivAt (T.orb h) (T.orb (T.Lt h) s) s := T.hasDerivAt_orb h hs0
    have hP := hasDerivAt_pair (ψ := psiS ε) (ψ' := deriv (psiS ε)) (K1 := 1 / (2 * ε))
      (K2 := 1 / (8 * ε ^ 3)) (by positivity) (by positivity) (psiS_measurable hε)
      (deriv_psiS_measurable hε) (psiS_zero hε) (fun a ha => psiS_deriv_bound hε ha)
      (fun a b ha hb => psiS_rem hε ha hb) (fun a b ha hb => psiS_hH hε ha hb) hU
      (ucurve_nonneg f t) hK hMpos.le hkb0
    have hQg := Pt_mem_Q f ((t : ℝ) - s)
    have hcross : Integrable (G T g (T.L g)) T.μ :=
      (L1.integrable_coeFn _).congr (gammaE_eq_ΓA hgA hg2 hQg (T.L_mem_A g hgA) hLg2 hLgQ)
    have hd'm : AEStronglyMeasurable (fun x => deriv (psiS ε) (G T g g x)) T.μ :=
      ((deriv_psiS_measurable hε).comp (T.A_measurable _ (G_mem hgA hgA))).aestronglyMeasurable
    have hd'b : ∀ᵐ x ∂T.μ, ‖deriv (psiS ε) (G T g g x)‖ ≤ 1 / (2 * ε) := by
      filter_upwards [T.ΓA_nonneg g hgA] with x hx
      rw [Real.norm_eq_abs]; exact psiS_deriv_bound hε hx
    have j1 : Integrable (fun x => deriv (psiS ε) (G T g g x) * G T g (T.L g) x) T.μ :=
      hcross.bdd_mul hd'm hd'b
    have hkm : AEStronglyMeasurable k T.μ := (T.A_measurable _ hkA).aestronglyMeasurable
    have hkb' : ∀ᵐ x ∂T.μ, ‖k x‖ ≤ |C0| + 1 := by
      filter_upwards [hkb] with x hx; rwa [Real.norm_eq_abs]
    have i1 : Integrable (fun x => k x * T.L (fun y => psiS ε (G T g g y)) x) T.μ :=
      hLG.bdd_mul hkm hkb'
    have i3 : Integrable (fun x => k x * (deriv (psiS ε) (G T g g x) * (-2 * G T g (T.L g) x))) T.μ := by
      have := (j1.bdd_mul hkm hkb').const_mul (-2)
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only; ring
    have iA : Integrable (fun x => T.Pt s.toNNReal h x * psiS ε (G T g g x)) T.μ :=
      hk2.integrable_mul hG2
    have iD : Integrable (fun x => T.Pt s.toNNReal h x * T.strongD ε g x) T.μ := by
      refine (i1.add i3).congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.add_apply, strongD]
      ring
    refine ⟨iA, iD, ?_⟩
    -- the derivative of `u`
    have gam_eq := gammaE_eq_ΓA hgA hg2 hQg (T.L_mem_A g hgA) hLg2 hLgQ
    have sub1 : (⟨hg2.toLp g, hQg⟩ : T.formDomain) = T.orbQ f ((t : ℝ) - s) :=
      Subtype.ext (Pt_toLp_eq_orb f _)
    have sub2 : (⟨hLg2.toLp (T.L g), hLgQ⟩ : T.formDomain) = T.orbQ (T.Lt f) ((t : ℝ) - s) :=
      Subtype.ext (T.toLp_L_Pt f _)
    rw [sub1, sub2] at gam_eq
    have e12 : GB T (T.cK f ((t : ℝ) - s)) (T.cK (T.Lt f) ((t : ℝ) - s)) =
        gammaE T (T.orbQ f ((t : ℝ) - s)) (T.orbQ (T.Lt f) ((t : ℝ) - s)) := GB_apply T _ _
    have e21 : GB T (T.cK (T.Lt f) ((t : ℝ) - s)) (T.cK f ((t : ℝ) - s)) =
        gammaE T (T.orbQ f ((t : ℝ) - s)) (T.orbQ (T.Lt f) ((t : ℝ) - s)) := by
      rw [← gammaE_comm]; exact GB_apply T _ _
    have hu' : ((-(GB T (T.cK (T.Lt f) ((t : ℝ) - s)) (T.cK f ((t : ℝ) - s)) +
        GB T (T.cK f ((t : ℝ) - s)) (T.cK (T.Lt f) ((t : ℝ) - s)))) : Lp ℝ 1 T.μ) =ᵐ[T.μ]
        fun x => -2 * G T g (T.L g) x := by
      rw [e12, e21]
      filter_upwards [Lp.coeFn_neg (gammaE T (T.orbQ f ((t : ℝ) - s)) (T.orbQ (T.Lt f) ((t : ℝ) - s)) +
        gammaE T (T.orbQ f ((t : ℝ) - s)) (T.orbQ (T.Lt f) ((t : ℝ) - s))),
        Lp.coeFn_add (gammaE T (T.orbQ f ((t : ℝ) - s)) (T.orbQ (T.Lt f) ((t : ℝ) - s)))
          (gammaE T (T.orbQ f ((t : ℝ) - s)) (T.orbQ (T.Lt f) ((t : ℝ) - s))), gam_eq] with x a b c
      rw [a]; simp only [Pi.neg_apply]; rw [b]; simp only [Pi.add_apply]; rw [c]; ring
    -- identification of the two terms
    have eA : (∫ x, (T.orb (T.Lt h) s : E → ℝ) x * psiS ε (T.ucurve f t s x) ∂T.μ) =
        ∫ x, k x * T.L (fun y => psiS ε (G T g g y)) x ∂T.μ := by
      have step1 : (∫ x, (T.orb (T.Lt h) s : E → ℝ) x * psiS ε (T.ucurve f t s x) ∂T.μ) =
          ∫ x, T.L k x * psiS ε (G T g g x) ∂T.μ := by
        refine integral_congr_ae ?_
        filter_upwards [T.L_Pt_ae h s, T.ucurve_ae f t s] with x a b
        rw [b, ← a]
      rw [step1]
      obtain ⟨-, h1⟩ := T.ibp_of_domain hkA hk2 hku hGA hG2 hQG
      obtain ⟨-, h2⟩ := ibp_bdd hGA hG2 hQG hLG hkA hk2 hkQ hkb
      have h3 : ∫ x, G T k (fun y => psiS ε (G T g g y)) x ∂T.μ =
          ∫ x, G T (fun y => psiS ε (G T g g y)) k x ∂T.μ :=
        integral_congr_ae (Eventually.of_forall fun x => by
          exact congrFun (G_comm (T := T) k (fun y => psiS ε (G T g g y))) x)
      rw [h1, h3, h2, neg_neg]
    have eB : (∫ x, (T.orb h s : E → ℝ) x * (deriv (psiS ε) (T.ucurve f t s x) *
        ((-(GB T (T.cK (T.Lt f) ((t : ℝ) - s)) (T.cK f ((t : ℝ) - s)) +
        GB T (T.cK f ((t : ℝ) - s)) (T.cK (T.Lt f) ((t : ℝ) - s)))) : Lp ℝ 1 T.μ) x) ∂T.μ) =
        ∫ x, k x * (deriv (psiS ε) (G T g g x) * (-2 * G T g (T.L g) x)) ∂T.μ := by
      refine integral_congr_ae ?_
      filter_upwards [T.Pt_ae s.toNNReal h, T.ucurve_ae f t s, hu'] with x a b c
      have a' : (T.orb h s : E → ℝ) x = k x := a
      rw [a', b, c]
    have hfun : T.strongPhi ε f h t = fun r => ∫ x, T.orb h r x * psiS ε (T.ucurve f t r x) ∂T.μ :=
      funext (strongPhi_eq ε f h t)
    rw [hfun]
    have hval : (∫ x, (T.orb (T.Lt h) s : E → ℝ) x * psiS ε (T.ucurve f t s x) ∂T.μ) +
        (∫ x, (T.orb h s : E → ℝ) x * (deriv (psiS ε) (T.ucurve f t s x) *
        ((-(GB T (T.cK (T.Lt f) ((t : ℝ) - s)) (T.cK f ((t : ℝ) - s)) +
        GB T (T.cK f ((t : ℝ) - s)) (T.cK (T.Lt f) ((t : ℝ) - s)))) : Lp ℝ 1 T.μ) x) ∂T.μ) =
        ∫ x, T.Pt s.toNNReal h x * T.strongD ε g x ∂T.μ := by
      rw [eA, eB, ← integral_add i1 i3]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [strongD]
      ring
    rw [← hval]
    exact hP

end FullTriple

end MarkovTriple.BGL
