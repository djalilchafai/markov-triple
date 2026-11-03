import Mathlib
import MarkovTriple.BGL.Instances.Gibbs.Core2Cut
import MarkovTriple.BGL.Instances.Gibbs.RegMain
import MarkovTriple.BGL.Theory.Extension.Core2Reduce

/-!
# Gibbs on `ℝ`: `Core2` and the unconditional converse of BGL Prop. 3.3.17 (R17, Stream A)

Statements: `STATEMENTS_R17_Core2.md` (A3, A4).  For `a ∈ C_c^∞` let `v` be the resolvent solution of `v − L v = a`
(`exists_resolvent_smooth`); with bounded `V', V'', V'''` (`BddJet`) the cut-offs `b_n = χ_n v ∈ C_c^∞` satisfy
`(1−L) b_n → a` and `L(1−L) b_n → L a` in `L²(μ)`: this is `Core2`, and the converse
`FullTriple.mem_domain_of_Γ₂` becomes unconditional for these triples.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.Sanity.OU (Sm)
open MarkovTriple.Sanity.OU hiding A₀ γ φ
open MarkovTriple.BGL.Lebesgue (chiR Rn Rn_pos chiR_smooth chiR_cs)
open MarkovTriple.BGL (FullTriple DiffusionTriple)

local notation "OA₀" => MarkovTriple.Sanity.OU.A₀

namespace MarkovTriple.BGL.Instances.Gibbs

namespace GibbsData
variable (G : GibbsData)

/-- **A3**: `Core2` for the Gibbs Full Markov Triple on `ℝ` with bounded `V', V'', V'''`. -/
theorem gibbsFull_core2 (hb : G.BddJet) : G.gibbsFull_unconditional.Core2 := by
  intro a
  have ha : a.1 ∈ OA₀ := a.2
  obtain ⟨v, hv, hv2, hL⟩ := G.exists_resolvent_smooth ha
  obtain ⟨h1, h2, h3⟩ := G.resolvent_jet_L2 hb hv ha hv2 hL
  have haL : MemLp a.1 2 G.μ := ha.1.continuous.memLp_of_hasCompactSupport ha.2
  have hLa : Lg G.V a.1 ∈ OA₀ := G.Lg_mem ha
  have hLaL : MemLp (Lg G.V a.1) 2 G.μ := hLa.1.continuous.memLp_of_hasCompactSupport hLa.2
  have hLvf : Lg G.V v = fun x => v x - a.1 x := funext hL
  have hLv : MemLp (Lg G.V v) 2 G.μ := by rw [hLvf]; exact hv2.sub haL
  have hLLvx : ∀ x, Lg G.V (Lg G.V v) x = (v x - a.1 x) - Lg G.V a.1 x := by
    intro x
    have e : Lg G.V v = v - a.1 := by rw [hLvf]; rfl
    rw [e, Lg_sub hv ha.1 x, hL x]
  have hLLv : MemLp (Lg G.V (Lg G.V v)) 2 G.μ := by
    have : Lg G.V (Lg G.V v) = fun x => (v x - a.1 x) - Lg G.V a.1 x := funext hLLvx
    rw [this]; exact (hv2.sub haL).sub hLaL
  obtain ⟨⟨m0, t0⟩, ⟨m1, t1⟩, ⟨m2, t2⟩⟩ := G.cutoff_ZL hb hv hv2 h1 h2 h3 hLv hLLv
  have m0' : ∀ n : ℕ, MemLp (fun x => chiR (Rn n) x * v x - v x) 2 G.μ := m0
  have m1' : ∀ n : ℕ, MemLp (fun x => Lg G.V (chiR (Rn n) * v) x - Lg G.V v x) 2 G.μ := m1
  have m2' : ∀ n : ℕ, MemLp (fun x => Lg G.V (Lg G.V (chiR (Rn n) * v)) x - Lg G.V (Lg G.V v) x) 2 G.μ := m2
  have t0' : Tendsto (fun n : ℕ => (m0' n).toLp (fun x => chiR (Rn n) x * v x - v x)) atTop (𝓝 0) := t0
  have t1' : Tendsto (fun n : ℕ => (m1' n).toLp (fun x => Lg G.V (chiR (Rn n) * v) x - Lg G.V v x)) atTop
    (𝓝 0) := t1
  have t2' : Tendsto (fun n : ℕ => (m2' n).toLp
    (fun x => Lg G.V (Lg G.V (chiR (Rn n) * v)) x - Lg G.V (Lg G.V v) x)) atTop (𝓝 0) := t2
  have hmem : ∀ n : ℕ, chiR (Rn n) * v ∈ OA₀ := fun n =>
    ⟨(chiR_smooth _).mul hv, (chiR_cs (Rn_pos n).ne').mul_right⟩
  have hLmem : ∀ n : ℕ, Lg G.V (chiR (Rn n) * v) ∈ OA₀ := fun n => G.Lg_mem (hmem n)
  refine ⟨fun n => ⟨chiR (Rn n) * v, hmem n⟩, ?_, ?_⟩
  · -- (1 - L) b_n → a
    have key : ∀ n, G.gibbsDiff.cls ⟨chiR (Rn n) * v, hmem n⟩ -
        G.gibbsDiff.Lcls ⟨chiR (Rn n) * v, hmem n⟩ - G.gibbsDiff.cls a =
        ((m0' n).sub (m1' n)).toLp _ := by
      intro n
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (G.gibbsDiff.cls ⟨chiR (Rn n) * v, hmem n⟩ -
          G.gibbsDiff.Lcls ⟨chiR (Rn n) * v, hmem n⟩) (G.gibbsDiff.cls a),
        Lp.coeFn_sub (G.gibbsDiff.cls ⟨chiR (Rn n) * v, hmem n⟩)
          (G.gibbsDiff.Lcls ⟨chiR (Rn n) * v, hmem n⟩),
        G.gibbsDiff.coeFn_cls ⟨chiR (Rn n) * v, hmem n⟩, G.gibbsDiff.coeFn_Lcls ⟨chiR (Rn n) * v, hmem n⟩,
        G.gibbsDiff.coeFn_cls a, ((m0' n).sub (m1' n)).coeFn_toLp] with x e1 e2 e3 e4 e5 e6
      simp only [e1, e2, e3, e4, e5, Pi.sub_apply, Pi.mul_apply]
      refine Eq.trans ?_ e6.symm
      simp only [Pi.sub_apply]
      have h5 : G.gibbsDiff.L (chiR (Rn n) * v) x = Lg G.V (chiR (Rn n) * v) x := rfl
      have h6 := hL x
      rw [h5]
      linarith
    have : Tendsto (fun n => G.gibbsDiff.cls ⟨chiR (Rn n) * v, hmem n⟩ -
        G.gibbsDiff.Lcls ⟨chiR (Rn n) * v, hmem n⟩ - G.gibbsDiff.cls a) atTop (𝓝 0) := by
      have h := t0'.sub t1'
      rw [sub_zero] at h
      refine h.congr (fun n => ?_)
      rw [key n]
      exact (MemLp.toLp_sub (m0' n) (m1' n)).symm
    exact tendsto_sub_nhds_zero_iff.1 this
  · -- L(1 - L) b_n → L a
    have key : ∀ n, G.gibbsDiff.Lcls ⟨chiR (Rn n) * v, hmem n⟩ -
        G.gibbsDiff.Lcls ⟨Lg G.V (chiR (Rn n) * v), hLmem n⟩ - G.gibbsDiff.Lcls a =
        ((m1' n).sub (m2' n)).toLp _ := by
      intro n
      refine Lp.ext ?_
      filter_upwards [Lp.coeFn_sub (G.gibbsDiff.Lcls ⟨chiR (Rn n) * v, hmem n⟩ -
          G.gibbsDiff.Lcls ⟨Lg G.V (chiR (Rn n) * v), hLmem n⟩) (G.gibbsDiff.Lcls a),
        Lp.coeFn_sub (G.gibbsDiff.Lcls ⟨chiR (Rn n) * v, hmem n⟩)
          (G.gibbsDiff.Lcls ⟨Lg G.V (chiR (Rn n) * v), hLmem n⟩),
        G.gibbsDiff.coeFn_Lcls ⟨chiR (Rn n) * v, hmem n⟩,
        G.gibbsDiff.coeFn_Lcls ⟨Lg G.V (chiR (Rn n) * v), hLmem n⟩,
        G.gibbsDiff.coeFn_Lcls a, ((m1' n).sub (m2' n)).coeFn_toLp] with x e1 e2 e3 e4 e5 e6
      simp only [e1, e2, e3, e4, e5, Pi.sub_apply]
      refine Eq.trans ?_ e6.symm
      simp only [Pi.sub_apply]
      have h5 : G.gibbsDiff.L (chiR (Rn n) * v) x = Lg G.V (chiR (Rn n) * v) x := rfl
      have h6 : G.gibbsDiff.L (Lg G.V (chiR (Rn n) * v)) x = Lg G.V (Lg G.V (chiR (Rn n) * v)) x := rfl
      have h7 : G.gibbsDiff.L a.1 x = Lg G.V a.1 x := rfl
      have h8 := hLLvx x
      have h9 := hL x
      rw [h5, h6, h7]
      linarith
    have : Tendsto (fun n => G.gibbsDiff.Lcls ⟨chiR (Rn n) * v, hmem n⟩ -
        G.gibbsDiff.Lcls ⟨Lg G.V (chiR (Rn n) * v), hLmem n⟩ - G.gibbsDiff.Lcls a) atTop (𝓝 0) := by
      have h := t1'.sub t2'
      rw [sub_zero] at h
      refine h.congr (fun n => ?_)
      rw [key n]
      exact (MemLp.toLp_sub (m1' n) (m2' n)).symm
    exact tendsto_sub_nhds_zero_iff.1 this

/-- **A4: the converse of BGL Prop. 3.3.17 (p. 162), unconditional for bounded-jet Gibbs triples on `ℝ`.**
`f ∈ 𝒜 ∩ L²(μ)` with `Γ(f), Γ₂(f) ∈ L¹(μ)`, `V'' ≥ ρ` and bounded `V'`, `V''`, `V'''` ⇒ `[f] ∈ 𝒟(L)` and
`L[f] = [L f]`. -/
theorem gibbs_mem_domain_of_Γ₂ (hb : G.BddJet) {ρ : ℝ} (hρ : ∀ x, ρ ≤ deriv (deriv G.V) x) {f : ℝ → ℝ}
    (hf : f ∈ G.gibbsFull_unconditional.A) (hf2 : MemLp f 2 G.μ)
    (hG : Integrable (FullTriple.G G.gibbsFull_unconditional f f) G.μ)
    (hG2 : Integrable (G.gibbsFull_unconditional.toDiffusionTriple.Γ₂ f f) G.μ) :
    ∃ hF : hf2.toLp f ∈ G.gibbsFull_unconditional.toDiffusionTriple.generator.domain,
      ((G.gibbsFull_unconditional.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 G.μ) : ℝ → ℝ)
        =ᵐ[G.μ] G.gibbsFull_unconditional.L f :=
  FullTriple.mem_domain_of_Γ₂ (G.gibbsFull_CD_unconditional hρ) (G.gibbsFull_core2 hb) hf hf2 hG hG2

end GibbsData

end MarkovTriple.BGL.Instances.Gibbs
