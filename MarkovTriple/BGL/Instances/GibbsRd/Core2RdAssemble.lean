import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdCutZL
import MarkovTriple.BGL.Instances.GibbsRd.Unconditional
import MarkovTriple.BGL.Theory.Extension.Core2Reduce

/-!
# `Core2` on `ℝ^d`: from the three graph-norm estimates to `Core2` (R18, Stream A3)

Given a smooth `v` with `L v = v − a` and `χ_n v − v`, `L(χ_n v) − L v`, `L L(χ_n v) − L L v → 0` in `L²(μ)`,
`b_n = χ_n v ∈ 𝒜₀` satisfy `(1−L) b_n → a`, `L(1−L) b_n → L a`, i.e. the defining property of `Core2` for `a`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.BGL (FullTriple DiffusionTriple pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- the diffusion triple of the Full triple. -/
noncomputable abbrev DT : DiffusionTriple (Rd d) := G.gibbsRdFull_unconditional.toDiffusionTriple

lemma chi_mem {v : Rd d → ℝ} (hv : Sm v) (n : ℕ) : (chi n * v : Rd d → ℝ) ∈ A₀ d :=
  ⟨(sm_cut _).mul hv, (hcs_cut (by positivity)).mul_right⟩

/-- the abstract assembly: smooth `v` with `L v = v − a` and the three `ZL` estimates give the `Core2` sequence. -/
theorem core2_of_ZL {a : G.gibbsRdFull_unconditional.A₀} {v : Rd d → ℝ} (hv : Sm v)
    (hL : ∀ x, Lr G.V v x = v x - a.1 x)
    (hz : ZL G.toEll.μ (fun n x => chi n x * v x - v x) ∧
      ZL G.toEll.μ (fun n x => Lr G.V (chi n * v) x - Lr G.V v x) ∧
      ZL G.toEll.μ (fun n x => Lr G.V (Lr G.V (chi n * v)) x - Lr G.V (Lr G.V v) x)) :
    ∃ b : ℕ → G.gibbsRdFull_unconditional.A₀,
      Tendsto (fun n => G.gibbsRdFull_unconditional.toDiffusionTriple.cls (b n) -
        G.gibbsRdFull_unconditional.toDiffusionTriple.Lcls (b n)) atTop
        (𝓝 (G.gibbsRdFull_unconditional.toDiffusionTriple.cls a)) ∧
      Tendsto (fun n => G.gibbsRdFull_unconditional.toDiffusionTriple.Lcls (b n) -
        FullTriple.LLₗ G.gibbsRdFull_unconditional (b n)) atTop
        (𝓝 (G.gibbsRdFull_unconditional.toDiffusionTriple.Lcls a)) := by
  have ha : a.1 ∈ A₀ d := a.2
  have hLE : ∀ f : Rd d → ℝ, Sm f → G.DT.L f = Lr G.V f := fun f hf => G.toEll_L hf
  have hLvf : Lr G.V v = fun x => v x - a.1 x := funext hL
  have hLLvx : ∀ x, Lr G.V (Lr G.V v) x = (v x - a.1 x) - Lr G.V a.1 x := by
    intro x
    have e : Lr G.V v = fun y => v y + (-1 : ℝ) * a.1 y := by rw [hLvf]; funext y; ring
    rw [e, Lr_add_smul hv ha.1 (-1) x, hL x]; ring
  obtain ⟨⟨m0, t0⟩, ⟨m1, t1⟩, ⟨m2, t2⟩⟩ := hz
  have hmem : ∀ n : ℕ, (chi n * v : Rd d → ℝ) ∈ A₀ d := fun n => chi_mem hv n
  have hLfun : ∀ n : ℕ, G.DT.L (chi n * v) = Lr G.V (chi n * v) := fun n => hLE _ (hmem n).1
  have hLmem : ∀ n : ℕ, G.DT.L (chi n * v) ∈ A₀ d := fun n => G.toEll.L_mem (hmem n)
  have t0' := t0
  have t1' := t1
  have t2' := t2
  refine ⟨fun n => ⟨chi n * v, hmem n⟩, ?_, ?_⟩
  · have key : ∀ n, G.DT.cls ⟨chi n * v, hmem n⟩ - G.DT.Lcls ⟨chi n * v, hmem n⟩ - G.DT.cls a =
        ((m0 n).sub (m1 n)).toLp _ := by
      intro n
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (G.DT.cls ⟨chi n * v, hmem n⟩ - G.DT.Lcls ⟨chi n * v, hmem n⟩) (G.DT.cls a),
        Lp.coeFn_sub (G.DT.cls ⟨chi n * v, hmem n⟩) (G.DT.Lcls ⟨chi n * v, hmem n⟩),
        G.DT.coeFn_cls ⟨chi n * v, hmem n⟩, G.DT.coeFn_Lcls ⟨chi n * v, hmem n⟩,
        G.DT.coeFn_cls a, ((m0 n).sub (m1 n)).coeFn_toLp] with x e1 e2 e3 e4 e5 e6
      simp only [e1, e2, e3, e4, e5, Pi.sub_apply, Pi.mul_apply]
      refine Eq.trans ?_ e6.symm
      simp only [Pi.sub_apply]
      have h5 : G.DT.L (chi n * v) x = Lr G.V (chi n * v) x := by rw [hLfun n]
      have h6 := hL x
      rw [h5]
      linarith
    have : Tendsto (fun n => G.DT.cls ⟨chi n * v, hmem n⟩ - G.DT.Lcls ⟨chi n * v, hmem n⟩ - G.DT.cls a) atTop
        (𝓝 0) := by
      have h := t0.sub t1
      rw [sub_zero] at h
      refine h.congr (fun n => ?_)
      rw [key n]
      exact (MemLp.toLp_sub (m0 n) (m1 n)).symm
    exact tendsto_sub_nhds_zero_iff.1 this
  · have key : ∀ n, G.DT.Lcls ⟨chi n * v, hmem n⟩ - G.DT.Lcls ⟨G.DT.L (chi n * v), hLmem n⟩ - G.DT.Lcls a =
        ((m1 n).sub (m2 n)).toLp _ := by
      intro n
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (G.DT.Lcls ⟨chi n * v, hmem n⟩ -
          G.DT.Lcls ⟨G.DT.L (chi n * v), hLmem n⟩) (G.DT.Lcls a),
        Lp.coeFn_sub (G.DT.Lcls ⟨chi n * v, hmem n⟩) (G.DT.Lcls ⟨G.DT.L (chi n * v), hLmem n⟩),
        G.DT.coeFn_Lcls ⟨chi n * v, hmem n⟩, G.DT.coeFn_Lcls ⟨G.DT.L (chi n * v), hLmem n⟩,
        G.DT.coeFn_Lcls a, ((m1 n).sub (m2 n)).coeFn_toLp] with x e1 e2 e3 e4 e5 e6
      simp only [e1, e2, e3, e4, e5, Pi.sub_apply]
      refine Eq.trans ?_ e6.symm
      simp only [Pi.sub_apply]
      have h5 : G.DT.L (chi n * v) x = Lr G.V (chi n * v) x := by rw [hLfun n]
      have h6 : G.DT.L (G.DT.L (chi n * v)) x = Lr G.V (Lr G.V (chi n * v)) x := by
        rw [hLfun n, hLE _ (sm_Lr G.smooth (hmem n).1)]
      have h7 : G.DT.L a.1 x = Lr G.V a.1 x := by rw [hLE _ ha.1]
      have h8 := hLLvx x
      have h9 := hL x
      rw [h5, h6, h7]
      linarith
    have : Tendsto (fun n => G.DT.Lcls ⟨chi n * v, hmem n⟩ - G.DT.Lcls ⟨G.DT.L (chi n * v), hLmem n⟩ -
        G.DT.Lcls a) atTop (𝓝 0) := by
      have h := t1.sub t2
      rw [sub_zero] at h
      refine h.congr (fun n => ?_)
      rw [key n]
      exact (MemLp.toLp_sub (m1 n) (m2 n)).symm
    exact tendsto_sub_nhds_zero_iff.1 this

end GibbsRdData

end MarkovTriple.BGL.Instances.GibbsRd
