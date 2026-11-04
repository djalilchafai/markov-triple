import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWitness

/-!
# `Core2EllMain` recovers the Gibbs `ℝ^d` theorem (R19, Stream A6; targets T4, T5)

For `G : GibbsRdData d` with `BddHess3`, the R18 cut-offs `χ_n = cut(n+1)` form a `CutFamily` for `G.toEll`
(`Γχ = |∇χ|²`, `Γ₂(χ) = ‖Hess χ‖² + Hess V(∇χ,∇χ)`, all bounded by the R18 estimates `cut_bounds`), so
`ell_core2`/`ell_mem_domain_of_Γ₂` apply: `gibbsRd_core2_via_ell`.  Non-vacuity with `ρ > 0`: `gaussData`, `cosData`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal
open MarkovTriple.BGL (FullTriple pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace GibbsRdData
variable (G : GibbsRdData d)

/-- **T4**: `BddHess3 ⇒ CoreCut` for `G.toEll`. -/
theorem BddHess3.coreCut {G : GibbsRdData d} (hb : G.BddHess3) : G.toEll.CoreCut := by
  refine ⟨fun n => chi n, ?_⟩
  have hev : ∀ x : Rd d, ∀ᶠ n : ℕ in atTop, ∀ᶠ y in 𝓝 x, chi n y = 1 := by
    intro x
    filter_upwards [eventually_qd_lt x] with n hn
    have hU := isOpen_inner (d := d) ((n : ℝ) + 1)
    filter_upwards [hU.mem_nhds hn] with y hy
    exact cut_eq_one (by positivity) (le_of_lt hy)
  have hbd : ∃ K : ℝ, ∀ (n : ℕ) (x : Rd d), G.toEll.Γ (chi n) (chi n) x ≤ K ∧ |G.toEll.L (chi n) x| ≤ K ∧
      |G.toEll.L (G.toEll.L (chi n)) x| ≤ K ∧ G.toEll.Γ (G.toEll.L (chi n)) (G.toEll.L (chi n)) x ≤ K ∧
      G.toEll.G2 (chi n) (chi n) x ≤ K := by
    by_cases hne : Nonempty (Fin d)
    · obtain ⟨i0⟩ := hne
      obtain ⟨K, hK⟩ := cut_bounds G hb
      obtain ⟨C2, hC2⟩ := hb.hess
      have hC20 : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0 i0 i0)
      have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK 0 0 i0 i0).2.1
      refine ⟨d * K ^ 2 + d ^ 2 * K ^ 2 * (1 + C2) + K + 1, fun n x => ?_⟩
      have hs : Sm (chi n : Rd d → ℝ) := sm_cut _
      have hsL : Sm (Lr G.V (chi n)) := sm_Lr G.smooth hs
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      have hdd : (0 : ℝ) ≤ d ^ 2 * K ^ 2 * (1 + C2) := by positivity
      have hdK : (0 : ℝ) ≤ d * K ^ 2 := by positivity
      have hΓ : ∀ f : Rd d → ℝ, (∀ i, |pderiv f i x| ≤ K) → G.toEll.Γ f f x ≤ d * K ^ 2 := by
        intro f hf
        rw [G.toEll_Γ f f]
        have := abs_sum_le' (f := fun i => pderiv f i x * pderiv f i x) (M := K * K) (fun i => by
          rw [abs_mul]; exact mul_le_mul (hf i) (hf i) (abs_nonneg _) hK0)
        have h2 := (le_abs_self _).trans this
        simp only [Gr]
        nlinarith
      have hL1 : G.toEll.L (chi n) x = Lr G.V (chi n) x := by rw [G.toEll_L hs]
      have hL2 : G.toEll.L (G.toEll.L (chi n)) x = Lr G.V (Lr G.V (chi n)) x := by
        rw [G.toEll_L hs, G.toEll_L hsL]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · have := hΓ (chi n) (fun i => (hK n x i i).2.1)
        nlinarith
      · rw [hL1]; have := (hK n x i0 i0).2.2.2.1; nlinarith
      · rw [hL2]; have := (hK n x i0 i0).2.2.2.2.2; nlinarith
      · have h := hΓ (Lr G.V (chi n)) (fun i => (hK n x i i).2.2.2.2.1)
        have e : G.toEll.L (chi n) = Lr G.V (chi n) := G.toEll_L hs
        rw [e]
        nlinarith
      · have e : G.toEll.G2 (chi n) (chi n) x = G.gibbsRdDiff.Γ₂ (chi n) (chi n) x := by
          have h := congrFun (G.toEll.Γ₂_eq_comb hs) x
          show _ = (G.toEll.diff).Γ₂ (chi n) (chi n) x
          rw [h]
          unfold EllData.G2
          rw [G.toEll.Γ_symm_apply (G.toEll.L (chi n)) (chi n) x]
        rw [e, G.gibbsRd_Γ₂_eq hs x]
        have t1 : ∑ i, ∑ j, pderiv (pderiv (chi n) i) j x ^ 2 ≤ d * (d * K ^ 2) := by
          have inner : ∀ i, ∑ j, pderiv (pderiv (chi n) i) j x ^ 2 ≤ d * K ^ 2 := by
            intro i
            have := abs_sum_le' (f := fun j => pderiv (pderiv (chi n) i) j x ^ 2) (M := K ^ 2) (fun j => by
              rw [abs_of_nonneg (sq_nonneg _)]
              have h1 := (hK n x i j).2.2.1
              nlinarith [abs_nonneg (pderiv (pderiv (chi n) i) j x),
                sq_abs (pderiv (pderiv (chi n) i) j x)])
            exact (le_abs_self _).trans this
          have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => inner i)
          simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
        have t2 : ∑ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv (chi n) i x * pderiv (chi n) j x ≤
            d * (d * (C2 * (K * K))) := by
          have inner : ∀ i, ∑ j, pderiv (pderiv G.V i) j x * pderiv (chi n) i x * pderiv (chi n) j x ≤
              d * (C2 * (K * K)) := by
            intro i
            have := abs_sum_le' (f := fun j => pderiv (pderiv G.V i) j x * pderiv (chi n) i x * pderiv (chi n) j x)
              (M := C2 * (K * K)) (fun j => by
                rw [abs_mul, abs_mul]
                have a1 := hC2 x i j
                have a2 := (hK n x i i).2.1
                have a3 := (hK n x j j).2.1
                calc |pderiv (pderiv G.V i) j x| * |pderiv (chi n) i x| * |pderiv (chi n) j x|
                    ≤ C2 * K * K := mul_le_mul (mul_le_mul a1 a2 (abs_nonneg _) hC20) a3 (abs_nonneg _)
                      (by positivity)
                  _ = C2 * (K * K) := by ring)
            exact (le_abs_self _).trans this
          have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => inner i)
          simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this
        nlinarith
    · refine ⟨0, fun n x => ?_⟩
      have he : IsEmpty (Fin d) := not_nonempty_iff.1 hne
      simp [EllData.Γ, EllData.L, EllData.G2]
  exact ⟨fun n => sm_cut _, fun n => hcs_cut (by positivity), fun n x => ⟨cut_nonneg _ x, cut_le_one _ x⟩,
    hev, hbd⟩

/-- **T4 (recovery)**: `Core2` for the Gibbs Full triple through the general `EllData` theorem, from `BddHess3` alone. -/
theorem gibbsRd_core2_via_ell (hb : G.BddHess3) : G.toEll.fullU.Core2 := by
  obtain ⟨ρ, hρ⟩ := BddHess3.hessGe hb
  exact G.toEll.ell_core2 (G.gibbsRd_curv hρ) hb.coreCut

end GibbsRdData

/-! ### T5: non-vacuity (`ρ > 0`, non-Gaussian) -/

theorem gaussData_coreCut (d : ℕ) : (gaussData d).toEll.CoreCut := (gaussData_bddHess3 d).coreCut

theorem cosData_coreCut (d : ℕ) : (cosData d).toEll.CoreCut := (cosData_bddHess3 d).coreCut

/-- `Core2` for the standard Gaussian through `ell_core2`, with `ρ = 1 > 0`. -/
theorem gaussData_ell_core2 (d : ℕ) : (gaussData d).toEll.fullU.Core2 :=
  (gaussData d).toEll.ell_core2 ((gaussData d).gibbsRd_curv hessGe_gauss) (gaussData_coreCut d)

/-- `Core2` for the non-Gaussian `V = |x|²/2 + cos(x₀)/2` through `ell_core2`, with `ρ = 1/2 > 0`. -/
theorem cosData_ell_core2 (d : ℕ) : (cosData d).toEll.fullU.Core2 :=
  (cosData d).toEll.ell_core2 ((cosData d).gibbsRd_curv (hessGe_cosV d)) (cosData_coreCut d)

end MarkovTriple.BGL.Instances.GibbsRd
