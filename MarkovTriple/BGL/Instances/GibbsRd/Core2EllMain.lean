import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllZL
import MarkovTriple.BGL.Theory.Extension.Core2Reduce

/-!
# `Core2` and the unconditional converse of BGL Prop. 3.3.17 for `EllData d` (R19, Stream A6)

Statements: `STATEMENTS_R19_Core2Ell.md` (T1, T2).  Hypotheses: a curvature lower bound `Curv ρ` (`ρ ∈ ℝ` of any sign) and a cut-off
family (`CoreCut`: bounded `Γχ_n, Lχ_n, L²χ_n, Γ(Lχ_n), Γ₂(χ_n)`).  Proof: `Core2EllResolvent` (smooth resolvent solution),
`Core2EllEnergy` (`Γ(v), Γ₂(v) - ρΓ(v) ∈ L¹`), `Core2EllZL` (the three graph-norm estimates), and the assembly below.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.BGL (FullTriple DiffusionTriple pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- The Full Markov triple of `E` with `WeakHypo` and `F8` proved (`EllData.ellReg`). -/
noncomputable def fullU : FullTriple (Rd d) := E.full E.weakHypo_unconditional E.f8_unconditional

theorem fullU_CD {ρ : ℝ} (hρ : E.Curv ρ) : E.fullU.CD ρ ∞ :=
  E.full_CD E.weakHypo_unconditional E.f8_unconditional hρ

/-- the abstract assembly: smooth `v` with `L v = v − a` and the three `ZL` estimates give the `Core2` sequence. -/
theorem core2_of_ZL_ell {χ : ℕ → Rd d → ℝ} (hχ : E.CutFamily χ) {a : E.fullU.A₀} {v : Rd d → ℝ} (hv : Sm v)
    (hL : ∀ x, E.L v x = v x - a.1 x)
    (hz : ZL E.μ (fun n x => χ n x * v x - v x) ∧
      ZL E.μ (fun n x => E.L (χ n * v) x - E.L v x) ∧
      ZL E.μ (fun n x => E.L (E.L (χ n * v)) x - E.L (E.L v) x)) :
    ∃ b : ℕ → E.fullU.A₀,
      Tendsto (fun n => E.fullU.toDiffusionTriple.cls (b n) -
        E.fullU.toDiffusionTriple.Lcls (b n)) atTop
        (𝓝 (E.fullU.toDiffusionTriple.cls a)) ∧
      Tendsto (fun n => E.fullU.toDiffusionTriple.Lcls (b n) -
        FullTriple.LLₗ E.fullU (b n)) atTop
        (𝓝 (E.fullU.toDiffusionTriple.Lcls a)) := by
  have ha : a.1 ∈ A₀ d := a.2
  have hLE : ∀ f : Rd d → ℝ, Sm f → E.fullU.toDiffusionTriple.L f = E.L f := fun f _ => rfl
  have hLvf : E.L v = fun x => v x - a.1 x := funext hL
  have hLLvx : ∀ x, E.L (E.L v) x = (v x - a.1 x) - E.L a.1 x := by
    intro x
    have e : E.L v = fun y => v y + (-1 : ℝ) * a.1 y := by rw [hLvf]; funext y; ring
    rw [e, congrFun (E.L_lin hv ha.1 (-1)) x, hL x]; ring
  obtain ⟨⟨m0, t0⟩, ⟨m1, t1⟩, ⟨m2, t2⟩⟩ := hz
  have hmem : ∀ n : ℕ, (χ n * v : Rd d → ℝ) ∈ A₀ d := fun n => ⟨(hχ.smooth n).mul hv, (hχ.cs n).mul_right⟩
  have hLfun : ∀ n : ℕ, E.fullU.toDiffusionTriple.L (χ n * v) = E.L (χ n * v) := fun n => hLE _ (hmem n).1
  have hLmem : ∀ n : ℕ, E.fullU.toDiffusionTriple.L (χ n * v) ∈ A₀ d := fun n => E.L_mem (hmem n)
  have t0' := t0
  have t1' := t1
  have t2' := t2
  refine ⟨fun n => ⟨χ n * v, hmem n⟩, ?_, ?_⟩
  · have key : ∀ n, E.fullU.toDiffusionTriple.cls ⟨χ n * v, hmem n⟩ - E.fullU.toDiffusionTriple.Lcls ⟨χ n * v, hmem n⟩ - E.fullU.toDiffusionTriple.cls a =
        ((m0 n).sub (m1 n)).toLp _ := by
      intro n
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (E.fullU.toDiffusionTriple.cls ⟨χ n * v, hmem n⟩ - E.fullU.toDiffusionTriple.Lcls ⟨χ n * v, hmem n⟩) (E.fullU.toDiffusionTriple.cls a),
        Lp.coeFn_sub (E.fullU.toDiffusionTriple.cls ⟨χ n * v, hmem n⟩) (E.fullU.toDiffusionTriple.Lcls ⟨χ n * v, hmem n⟩),
        E.fullU.toDiffusionTriple.coeFn_cls ⟨χ n * v, hmem n⟩, E.fullU.toDiffusionTriple.coeFn_Lcls ⟨χ n * v, hmem n⟩,
        E.fullU.toDiffusionTriple.coeFn_cls a, ((m0 n).sub (m1 n)).coeFn_toLp] with x e1 e2 e3 e4 e5 e6
      simp only [e1, e2, e3, e4, e5, Pi.sub_apply, Pi.mul_apply]
      refine Eq.trans ?_ e6.symm
      simp only [Pi.sub_apply]
      have h5 : E.fullU.toDiffusionTriple.L (χ n * v) x = E.L (χ n * v) x := by rw [hLfun n]
      have h6 := hL x
      rw [h5]
      linarith
    have : Tendsto (fun n => E.fullU.toDiffusionTriple.cls ⟨χ n * v, hmem n⟩ - E.fullU.toDiffusionTriple.Lcls ⟨χ n * v, hmem n⟩ - E.fullU.toDiffusionTriple.cls a) atTop
        (𝓝 0) := by
      have h := t0.sub t1
      rw [sub_zero] at h
      refine h.congr (fun n => ?_)
      rw [key n]
      exact (MemLp.toLp_sub (m0 n) (m1 n)).symm
    exact tendsto_sub_nhds_zero_iff.1 this
  · have key : ∀ n, E.fullU.toDiffusionTriple.Lcls ⟨χ n * v, hmem n⟩ - E.fullU.toDiffusionTriple.Lcls ⟨E.fullU.toDiffusionTriple.L (χ n * v), hLmem n⟩ - E.fullU.toDiffusionTriple.Lcls a =
        ((m1 n).sub (m2 n)).toLp _ := by
      intro n
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (E.fullU.toDiffusionTriple.Lcls ⟨χ n * v, hmem n⟩ -
          E.fullU.toDiffusionTriple.Lcls ⟨E.fullU.toDiffusionTriple.L (χ n * v), hLmem n⟩) (E.fullU.toDiffusionTriple.Lcls a),
        Lp.coeFn_sub (E.fullU.toDiffusionTriple.Lcls ⟨χ n * v, hmem n⟩) (E.fullU.toDiffusionTriple.Lcls ⟨E.fullU.toDiffusionTriple.L (χ n * v), hLmem n⟩),
        E.fullU.toDiffusionTriple.coeFn_Lcls ⟨χ n * v, hmem n⟩, E.fullU.toDiffusionTriple.coeFn_Lcls ⟨E.fullU.toDiffusionTriple.L (χ n * v), hLmem n⟩,
        E.fullU.toDiffusionTriple.coeFn_Lcls a, ((m1 n).sub (m2 n)).coeFn_toLp] with x e1 e2 e3 e4 e5 e6
      simp only [e1, e2, e3, e4, e5, Pi.sub_apply]
      refine Eq.trans ?_ e6.symm
      simp only [Pi.sub_apply]
      have h5 : E.fullU.toDiffusionTriple.L (χ n * v) x = E.L (χ n * v) x := by rw [hLfun n]
      have h6 : E.fullU.toDiffusionTriple.L (E.fullU.toDiffusionTriple.L (χ n * v)) x = E.L (E.L (χ n * v)) x := by
        rw [hLfun n, hLE _ (E.sm_L (hmem n).1)]
      have h7 : E.fullU.toDiffusionTriple.L a.1 x = E.L a.1 x := by rw [hLE _ ha.1]
      have h8 := hLLvx x
      have h9 := hL x
      rw [h5, h6, h7]
      linarith
    have : Tendsto (fun n => E.fullU.toDiffusionTriple.Lcls ⟨χ n * v, hmem n⟩ - E.fullU.toDiffusionTriple.Lcls ⟨E.fullU.toDiffusionTriple.L (χ n * v), hLmem n⟩ -
        E.fullU.toDiffusionTriple.Lcls a) atTop (𝓝 0) := by
      have h := t1.sub t2
      rw [sub_zero] at h
      refine h.congr (fun n => ?_)
      rw [key n]
      exact (MemLp.toLp_sub (m1 n) (m2 n)).symm
    exact tendsto_sub_nhds_zero_iff.1 this


/-- **T1: `Core2` for `EllData d`** under a curvature lower bound (any sign) and a cut-off family. -/
theorem ell_core2 {ρ : ℝ} (hρ : E.Curv ρ) (hC : E.CoreCut) : E.fullU.Core2 := by
  obtain ⟨χ, hχ⟩ := hC
  intro a
  have ha : a.1 ∈ A₀ d := a.2
  obtain ⟨v, hv, hv2, hL⟩ := E.exists_resolvent_smooth_ell ha
  exact E.core2_of_ZL_ell hχ hv hL (E.cutoff_ZL_ell rfl hρ hχ hv ha hv2 hL)

/-- **T2: the converse of BGL Prop. 3.3.17 (p. 162), unconditional for `EllData d`** (curvature lower bound of any sign and a
cut-off family): `f ∈ 𝒜 ∩ L²(μ)` with `Γ(f), Γ₂(f) ∈ L¹(μ)` implies `[f] ∈ 𝒟(L)`, `L[f] = [Lf]` a.e. -/
theorem ell_mem_domain_of_Γ₂ {ρ : ℝ} (hρ : E.Curv ρ) (hC : E.CoreCut) {f : Rd d → ℝ}
    (hf : f ∈ E.fullU.A) (hf2 : MemLp f 2 E.μ)
    (hG : Integrable (FullTriple.G E.fullU f f) E.μ)
    (hG2 : Integrable (E.fullU.toDiffusionTriple.Γ₂ f f) E.μ) :
    ∃ hF : hf2.toLp f ∈ E.fullU.toDiffusionTriple.generator.domain,
      ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ]
        E.fullU.L f :=
  FullTriple.mem_domain_of_Γ₂ (E.fullU_CD hρ) (E.ell_core2 hρ hC) hf hf2 hG hG2

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
