import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllEnergy
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdZL

/-!
# `Core2` for `EllData d`: the three graph-norm cut-off estimates (R19, Stream A6)

With `F = χ_n` (a `CutFamily`), `v` smooth, `L v = v - a`, `Γ(v), Γ₂(v) - ρΓ(v) ∈ L¹`:
`χ_n v → v`, `L(χ_n v) → L v`, `LL(χ_n v) → LL v` in `L²(μ)`.  Dominated convergence, with Cauchy–Schwarz for `Γ` and for the
nonnegative form `Γ₂ - ρΓ`, and locality for the pointwise vanishing.
-/

open MeasureTheory Filter Topology Set
open MarkovTriple.BGL (pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ} {μ : Measure (Rd d)}

/-- dominated convergence for sequences of continuous functions with an `L¹` bound on the squares. -/
lemma ZL.of_dom [IsFiniteMeasure μ] {D : ℕ → Rd d → ℝ} (hc : ∀ n, Continuous (D n)) {Ψ : Rd d → ℝ}
    (hΨ : Integrable Ψ μ) (hb : ∀ n x, (D n x) ^ 2 ≤ Ψ x) (hz : ∀ x, ∀ᶠ n in atTop, D n x = 0) :
    ZL μ D := by
  have hm : ∀ n, MemLp (D n) 2 μ := fun n => by
    rw [memLp_two_iff_integrable_sq (hc n).aestronglyMeasurable]
    refine hΨ.mono' ((hc n).pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hb n x
  refine ⟨hm, tendsto_toLp_zero_rd hm ?_⟩
  have := tendsto_integral_of_dominated_convergence (μ := μ)
    (F := fun (n : ℕ) x => (D n x) ^ 2) (f := fun _ => (0 : ℝ)) Ψ
    (fun n => ((hc n).pow 2).aestronglyMeasurable) hΨ
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hb n x)
    (Eventually.of_forall fun x => by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hz x] with n hn
      rw [hn]; simp)
  simpa using this

namespace EllData
variable (E : EllData d)

/-- `Γ(A_n, k) → 0` in `L²` when `Γ(A_n) ≤ K`, `Γ(k) ≤ Ψ₀ ∈ L¹` and `Γ(A_n,k)(x)` is eventually `0`. -/
lemma zl_Γ [IsFiniteMeasure μ] {A : ℕ → Rd d → ℝ} {k : Rd d → ℝ} (hA : ∀ n, Sm (A n)) (hk : Sm k) {K : ℝ}
    (hAK : ∀ n x, E.Γ (A n) (A n) x ≤ K) {Ψ₀ : Rd d → ℝ} (hΨ : Integrable Ψ₀ μ)
    (hkΨ : ∀ x, E.Γ k k x ≤ Ψ₀ x) (hz : ∀ x, ∀ᶠ n in atTop, E.Γ (A n) k x = 0) :
    ZL μ (fun n x => E.Γ (A n) k x) := by
  refine ZL.of_dom (fun n => (E.sm_Γ (hA n) hk).continuous) (hΨ.const_mul K) (fun n x => ?_) hz
  have h1 := E.Γ_cs (A n) k x
  have h2 : E.Γ (A n) (A n) x * E.Γ k k x ≤ K * Ψ₀ x := by
    have a0 := E.Γ_nonneg (A n) x
    have k0 := E.Γ_nonneg k x
    have := hAK n x
    have := hkΨ x
    nlinarith
  exact h1.trans h2

/-- `Γ₂(χ_n, v) → 0` in `L²` (Cauchy–Schwarz for `Γ₂ - ρΓ`). -/
lemma zl_G2 [IsFiniteMeasure E.μ] {ρ : ℝ} (hρ : E.Curv ρ) {χ : ℕ → Rd d → ℝ} (hχ : E.CutFamily χ) {v : Rd d → ℝ}
    (hv : Sm v) (iΓ : Integrable (E.Γ v v) E.μ) (iG : Integrable (fun x => E.G2' ρ v v x) E.μ) :
    ZL E.μ (fun n x => E.G2 (χ n) v x) := by
  obtain ⟨K, hK⟩ := hχ.bound
  have hsχ := hχ.smooth
  have hG2cont : ∀ n, Continuous (fun x => E.G2 (χ n) v x) := fun n => (E.sm_G2 (hsχ n) hv).continuous
  have hΨ : Integrable (fun x => 2 * (K + |ρ| * K) * E.G2' ρ v v x + 2 * ρ ^ 2 * K * E.Γ v v x) E.μ :=
    (iG.const_mul _).add (iΓ.const_mul _)
  refine ZL.of_dom hG2cont hΨ (fun n x => ?_) (fun x => ?_)
  · have e : E.G2 (χ n) v x = E.G2' ρ (χ n) v x + ρ * E.Γ (χ n) v x := by unfold G2'; ring
    have c1 := E.G2'_cs hρ (hsχ n) hv x
    have c2 := E.Γ_cs (χ n) v x
    have a1 : E.G2' ρ (χ n) (χ n) x ≤ K + |ρ| * K := by
      unfold G2'
      have := (hK n x).2.2.2.2
      have h0 := E.Γ_nonneg (χ n) x
      have h1 := (hK n x).1
      nlinarith [neg_abs_le ρ, le_abs_self ρ, abs_nonneg ρ, mul_nonneg (abs_nonneg ρ) h0,
        mul_le_mul_of_nonneg_left h1 (abs_nonneg ρ)]
    have b1 := E.G2'_nonneg hρ hv x
    have g1' := E.Γ_nonneg v x
    have gK := (hK n x).1
    have hA : E.G2' ρ (χ n) v x ^ 2 ≤ (K + |ρ| * K) * E.G2' ρ v v x :=
      c1.trans (mul_le_mul_of_nonneg_right a1 b1)
    have hB : E.Γ (χ n) v x ^ 2 ≤ K * E.Γ v v x :=
      c2.trans (mul_le_mul_of_nonneg_right gK g1')
    rw [e]
    have hB' := mul_le_mul_of_nonneg_left hB (sq_nonneg ρ)
    nlinarith [sq_nonneg (E.G2' ρ (χ n) v x - ρ * E.Γ (χ n) v x), hA, hB']
  · filter_upwards [hχ.eventually_one x] with n hn
    exact (E.loc_one hn).2.2.2.2 v

/-- **the three graph-norm cut-off estimates**. -/
theorem cutoff_ZL_ell [IsFiniteMeasure μ] (hμ : μ = E.μ) {ρ : ℝ} (hρ : E.Curv ρ) {χ : ℕ → Rd d → ℝ}
    (hχ : E.CutFamily χ) {v a : Rd d → ℝ} (hv : Sm v) (ha : a ∈ A₀ d) (hv2 : MemLp v 2 μ)
    (hL : ∀ x, E.L v x = v x - a x) :
    ZL μ (fun n x => χ n x * v x - v x) ∧ ZL μ (fun n x => E.L (χ n * v) x - E.L v x) ∧
    ZL μ (fun n x => E.L (E.L (χ n * v)) x - E.L (E.L v) x) := by
  subst hμ
  obtain ⟨K, hK⟩ := hχ.bound
  have hK0 : 0 ≤ K := le_trans (E.Γ_nonneg (χ 0) 0) (hK 0 0).1
  have iΓ := E.integrable_Γ_resolvent hχ hv ha hv2 hL
  have iG := E.integrable_G2'_resolvent hρ hχ hv ha hv2 hL
  have iΓa : Integrable (E.Γ a a) E.μ :=
    (E.sm_Γ ha.1 ha.1).continuous.integrable_of_hasCompactSupport (E.hcs_Γ_left ha.2)
  have hsχ := hχ.smooth
  have haL : MemLp a 2 E.μ := ha.1.continuous.memLp_of_hasCompactSupport ha.2
  have hLvf : E.L v = fun y => v y + (-1 : ℝ) * a y := by funext y; rw [hL y]; ring
  have hLv : MemLp (E.L v) 2 E.μ := by
    have : E.L v = fun x => v x - a x := funext hL
    rw [this]; exact hv2.sub haL
  have hLa : E.L a ∈ A₀ d := E.L_mem ha
  have hLaL : MemLp (E.L a) 2 E.μ := hLa.1.continuous.memLp_of_hasCompactSupport hLa.2
  have hLLvx : ∀ x, E.L (E.L v) x = (v x - a x) - E.L a x := by
    intro x
    have := congrFun (E.L_lin hv ha.1 (-1)) x
    rw [hLvf, this, hL x]; ring
  have hLLv : MemLp (E.L (E.L v)) 2 E.μ := by
    have : E.L (E.L v) = fun x => (v x - a x) - E.L a x := funext hLLvx
    rw [this]; exact (hv2.sub haL).sub hLaL
  -- coefficient families
  have hloc : ∀ x, ∀ᶠ n in atTop, ∀ᶠ y in 𝓝 x, χ n y = 1 := hχ.eventually_one
  have g1 : Good (fun (n : ℕ) (x : Rd d) => χ n x - 1) := by
    refine ⟨fun n => (hsχ n).continuous.sub continuous_const, ⟨1, fun n x => ?_⟩, fun x => ?_⟩
    · have := hχ.mem n x
      rw [abs_le]; constructor <;> linarith [this.1, this.2]
    · filter_upwards [hloc x] with n hn
      rw [hn.self_of_nhds]; ring
  have gL : Good (fun (n : ℕ) (x : Rd d) => E.L (χ n) x) :=
    ⟨fun n => (E.sm_L (hsχ n)).continuous, ⟨K, fun n x => (hK n x).2.1⟩, fun x => by
      filter_upwards [hloc x] with n hn
      exact (E.loc_one hn).2.1⟩
  have gLL : Good (fun (n : ℕ) (x : Rd d) => E.L (E.L (χ n)) x) :=
    ⟨fun n => (E.sm_L (E.sm_L (hsχ n))).continuous, ⟨K, fun n x => (hK n x).2.2.1⟩, fun x => by
      filter_upwards [hloc x] with n hn
      exact (E.loc_one hn).2.2.1⟩
  -- Γ-terms
  have zΓv : ZL E.μ (fun n x => E.Γ (χ n) v x) :=
    E.zl_Γ hsχ hv (fun n x => (hK n x).1) iΓ (fun x => le_rfl) (fun x => by
      filter_upwards [hloc x] with n hn
      exact (E.loc_one hn).1 v)
  have hLvs : Sm (E.L v) := E.sm_L hv
  have hΓLv : ∀ x, E.Γ (E.L v) (E.L v) x ≤ 2 * E.Γ v v x + 2 * E.Γ a a x := by
    intro x
    rw [hLvf]
    exact E.Γ_sub_le hv ha.1 x
  have zΓLv : ZL E.μ (fun n x => E.Γ (χ n) (E.L v) x) :=
    E.zl_Γ hsχ hLvs (fun n x => (hK n x).1) ((iΓ.const_mul 2).add (iΓa.const_mul 2)) hΓLv
      (fun x => by
        filter_upwards [hloc x] with n hn
        exact (E.loc_one hn).1 (E.L v))
  have zLΓv : ZL E.μ (fun n x => E.Γ (E.L (χ n)) v x) :=
    E.zl_Γ (fun n => E.sm_L (hsχ n)) hv (fun n x => (hK n x).2.2.2.1) iΓ (fun x => le_rfl)
      (fun x => by
        filter_upwards [hloc x] with n hn
        exact (E.loc_one hn).2.2.2.1 v)
  -- Γ₂-term
  have zG2 : ZL E.μ (fun n x => E.G2 (χ n) v x) := E.zl_G2 hρ hχ hv iΓ iG
  refine ⟨?_, ?_, ?_⟩
  · exact (ZL.of_good g1 hv2).congr (fun n x => by ring)
  · refine (((ZL.of_good g1 hLv).add (ZL.of_good gL hv2)).add (zΓv.const_mul 2)).congr (fun n x => ?_)
    rw [E.L_cut (hsχ n) hv x]
    ring
  · have s1 := ZL.of_good g1 hLLv
    have s2 := ZL.of_good gL hLv
    have s4 := ZL.of_good gLL hv2
    refine (((((s1.add (s2.const_mul 2)).add (zΓLv.const_mul 4)).add s4).add (zLΓv.const_mul 4)).add
      (zG2.const_mul 4)).congr (fun n x => ?_)
    rw [E.LL_cut (hsχ n) hv x]
    ring

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
