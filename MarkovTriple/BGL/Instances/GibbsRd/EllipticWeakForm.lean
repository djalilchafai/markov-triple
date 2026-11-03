import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticMollify
import MarkovTriple.BGL.Instances.GibbsRd.EllCalc

/-!
# The weak form on `H¹` and its extension to compactly supported `H¹` test functions (R16, elliptic half)

Statements WF (a), (b) of `STATEMENTS_R16_Elliptic.md` (continuation, batch 4); Evans §6.3.1 (the bilinear form `B[u,v]` and
the passage from `C_c^∞` to `H¹_0` test functions), Gilbarg–Trudinger §8.2.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)
open Elliptic

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- the (very) weak equation `L u = h` against `μ`, tested on `A₀` (form of `resolvent_weak`/`EllReg`, `Z⁻¹` removed) -/
def VeryWeakSol (u h : Rd d → ℝ) : Prop :=
  ∀ a ∈ A₀ d, ∫ x, u x * E.L a x * E.w x = ∫ x, h x * a x * E.w x

/-- the energy pairing `∫ w Σᵢⱼ aᵢⱼ gᵢ vⱼ` -/
noncomputable def Bf (g v : Fin d → Rd d → ℝ) : ℝ :=
  ∫ x, E.w x * ∑ i, ∑ j, E.a i j x * g i x * v j x

/-- **WF (a)**: for `u ∈ H¹_loc` the very weak equation is the usual weak form `B[u,a] = −∫ h a w` on `C_c^∞`. -/
theorem weakForm_of_veryWeak {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hW : E.VeryWeakSol u h)
    {a : Rd d → ℝ} (ha : a ∈ A₀ d) :
    E.Bf g (fun j x => pderiv a j x) = -∫ x, h x * a x * E.w x := by
  have hul : LocallyIntegrable u := hu.locallyIntegrable
  -- integrability of the pieces
  have hP : ∀ i, Sm (E.P a i) := fun i => E.sm_P ha.1 i
  have hPc : ∀ i, HasCompactSupport (E.P a i) := fun i => E.hcs_P ha.2 i
  have hdP : ∀ i, Continuous (fun x => pderiv (E.P a i) i x) := fun i => ((hP i).pderiv i).continuous
  have hdPc : ∀ i, HasCompactSupport (fun x => pderiv (E.P a i) i x) := fun i =>
    (hPc i).fderiv_apply ℝ (Pi.single i 1)
  have I1 : ∀ i, Integrable (fun x => u x * pderiv (E.P a i) i x) := fun i =>
    integrable_mul_cs hul (hdP i) (hdPc i)
  have I2 : ∀ i, Integrable (fun x => g i x * E.P a i x) := fun i =>
    integrable_mul_cs (hgL i).locallyIntegrable (hP i).continuous (hPc i)
  have e1 : ∀ x, u x * E.L a x * E.w x = ∑ i, u x * pderiv (E.P a i) i x := by
    intro x
    rw [E.L_eq, ← Finset.mul_sum]
    have := (E.w_pos x).ne'
    field_simp
  have s1 : ∫ x, u x * E.L a x * E.w x = ∑ i, ∫ x, u x * pderiv (E.P a i) i x := by
    simp_rw [e1]
    exact integral_finsetSum _ fun i _ => I1 i
  have s2 : ∀ i, ∫ x, u x * pderiv (E.P a i) i x = -∫ x, g i x * E.P a i x := fun i =>
    (hg i).2.2 (E.P a i) (hP i) (hPc i)
  have e2 : ∀ x, E.w x * ∑ i, ∑ j, E.a i j x * g i x * pderiv a j x = ∑ i, g i x * E.P a i x := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold P
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have s3 : E.Bf g (fun j x => pderiv a j x) = ∑ i, ∫ x, g i x * E.P a i x := by
    unfold Bf
    simp_rw [e2]
    exact integral_finsetSum _ fun i _ => I2 i
  rw [s3]
  have := hW a ha
  rw [s1] at this
  simp only [s2, Finset.sum_neg_distrib] at this
  linarith

/-- **WF (b)**: the weak form holds for compactly supported `H¹` test functions (Evans §6.3.1, via mollification). -/
theorem weakForm_extend {u h : Rd d → ℝ} {g : Fin d → Rd d → ℝ} (hu : LocL2 u)
    (hg : ∀ i, WeakDeriv u (g i) i) (hgL : ∀ i, LocL2 (g i)) (hh : LocL2 h) (hW : E.VeryWeakSol u h)
    {v : Rd d → ℝ} {vj : Fin d → Rd d → ℝ} (hv : MemLp v 2 volume) (hvc : HasCompactSupport v)
    (hvj : ∀ j, WeakDeriv v (vj j) j) (hvjL : ∀ j, MemLp (vj j) 2 volume) :
    E.Bf g vj = -∫ x, h x * v x * E.w x := by
  obtain ⟨ρ, hρ⟩ := exists_mollSeq d
  set T : Set (Rd d) := tsupport v with hT
  set S : Set (Rd d) := Metric.cthickening 1 T with hS
  have hSc : IsCompact S := hvc.cthickening
  have hcw : Continuous E.w := E.w_smooth.continuous
  have hvloc : LocallyIntegrable v := hv.locallyIntegrable (by norm_num)
  -- the approximants
  set an : ℕ → Rd d → ℝ := fun n => moll (ρ n) v with han
  have han_mem : ∀ n, an n ∈ A₀ d := fun n =>
    ⟨moll_contDiff (hρ.smooth n) (hρ.cs n) hvloc, moll_hasCompactSupport (hρ.cs n) hvc⟩
  have hpd : ∀ n j, (fun x => pderiv (an n) j x) = moll (ρ n) (vj j) := fun n j => by
    funext x; exact pderiv_moll (hρ.smooth n) (hρ.cs n) (hvj j) x
  have hvj0 : ∀ j, ∀ᵐ x, x ∉ T → vj j x = 0 := fun j => weakDeriv_zero_off (hvj j)
  have hv0 : ∀ y, y ∉ T → v y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hform : ∀ n, E.Bf g (fun j => moll (ρ n) (vj j)) = -∫ x, h x * an n x * E.w x := by
    intro n
    have := E.weakForm_of_veryWeak hu hg hgL hW (han_mem n)
    have e : (fun j x => pderiv (an n) j x) = fun j => moll (ρ n) (vj j) := by
      funext j; exact hpd n j
    rw [e] at this; exact this
  -- kernels cut to `S`
  set k : Fin d → Fin d → Rd d → ℝ := fun i j => S.indicator (fun x => (E.w x * E.a i j x) * g i x) with hk
  have hkm : ∀ i j, MemLp (k i j) 2 volume := fun i j =>
    LocL2.memLp_indicator (LocL2.mul_continuous (hgL i) (hcw.mul (E.a_smooth i j).continuous)) hSc
  set kh : Rd d → ℝ := S.indicator (fun x => E.w x * h x) with hkh
  have hkhm : MemLp kh 2 volume := LocL2.memLp_indicator (LocL2.mul_continuous hh hcw) hSc
  -- pointwise identities for the integrands
  have hBint : ∀ (w' : Fin d → Rd d → ℝ), (∀ j, ∀ x, x ∉ S → w' j x = 0) → ∀ x,
      E.w x * ∑ i, ∑ j, E.a i j x * g i x * w' j x = ∑ i, ∑ j, k i j x * w' j x := by
    intro w' hw' x
    by_cases hx : x ∈ S
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hk, Set.indicator_of_mem hx]; ring
    · simp [hk, Set.indicator_of_notMem hx, hw' _ x hx]
  have han0 : ∀ n j, ∀ x, x ∉ S → moll (ρ n) (vj j) x = 0 := fun n j x hx =>
    moll_eq_zero_off hρ n (hvj0 j) hx
  have hanv0 : ∀ n x, x ∉ S → an n x = 0 := fun n x hx => moll_eq_zero_off hρ n (Eventually.of_forall hv0) hx
  -- left side
  have hLHS : Tendsto (fun n => E.Bf g (fun j => moll (ρ n) (vj j))) atTop (𝓝 (E.Bf g vj)) := by
    have hmem : ∀ n j, MemLp (moll (ρ n) (vj j)) 2 volume := fun n j =>
      (moll_memLp_norm_le (hρ.smooth n) (hρ.cs n) (hρ.nonneg n) (hρ.integral n) (hvjL j)).1
    have hlim : ∀ i j, Tendsto (fun n => ∫ x, k i j x * moll (ρ n) (vj j) x) atTop (𝓝 (∫ x, k i j x * vj j x)) :=
      fun i j => tendsto_integral_mul (hkm i j) (hvjL j) (fun n => hmem n j) (moll_tendsto hρ (hvjL j))
    have hsum : Tendsto (fun n => ∑ i, ∑ j, ∫ x, k i j x * moll (ρ n) (vj j) x) atTop
        (𝓝 (∑ i, ∑ j, ∫ x, k i j x * vj j x)) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => hlim i j
    have e1 : ∀ n, E.Bf g (fun j => moll (ρ n) (vj j)) = ∑ i, ∑ j, ∫ x, k i j x * moll (ρ n) (vj j) x := by
      intro n
      unfold Bf
      simp_rw [hBint (fun j => moll (ρ n) (vj j)) (han0 n)]
      have hI : ∀ i, Integrable (fun x => ∑ j, k i j x * moll (ρ n) (vj j) x) := fun i =>
        integrable_finsetSum _ fun j _ => (hkm i j).integrable_mul (hmem n j)
      exact (integral_finsetSum (μ := volume) Finset.univ (f := fun i x => ∑ j, k i j x * moll (ρ n) (vj j) x)
        (fun i _ => hI i)).trans (Finset.sum_congr rfl fun i _ =>
          integral_finsetSum _ fun j _ => (hkm i j).integrable_mul (hmem n j))
    have e2 : E.Bf g vj = ∑ i, ∑ j, ∫ x, k i j x * vj j x := by
      unfold Bf
      have hae : ∀ᵐ x, ∀ j, x ∉ T → vj j x = 0 := by
        rw [ae_all_iff]; exact hvj0
      have hae' : (fun x => E.w x * ∑ i, ∑ j, E.a i j x * g i x * vj j x) =ᵐ[volume]
          fun x => ∑ i, ∑ j, k i j x * vj j x := by
        filter_upwards [hae] with x hx
        by_cases hxS : x ∈ S
        · rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          simp only [hk, Set.indicator_of_mem hxS]; ring
        · have hxT : x ∉ T := fun h' => hxS (Metric.self_subset_cthickening _ h')
          have hz : ∀ i j, E.a i j x * g i x * vj j x = 0 := fun i j => by rw [hx j hxT]; ring
          simp [hk, Set.indicator_of_notMem hxS, hz]
      rw [integral_congr_ae hae']
      have hI : ∀ i, Integrable (fun x => ∑ j, k i j x * vj j x) := fun i =>
        integrable_finsetSum _ fun j _ => (hkm i j).integrable_mul (hvjL j)
      exact (integral_finsetSum (μ := volume) Finset.univ (f := fun i x => ∑ j, k i j x * vj j x)
        (fun i _ => hI i)).trans (Finset.sum_congr rfl fun i _ =>
          integral_finsetSum _ fun j _ => (hkm i j).integrable_mul (hvjL j))
    rw [e2]
    simpa only [e1] using hsum
  -- right side
  have hRHS : Tendsto (fun n => -∫ x, h x * an n x * E.w x) atTop (𝓝 (-∫ x, h x * v x * E.w x)) := by
    have hmem : ∀ n, MemLp (an n) 2 volume := fun n =>
      (moll_memLp_norm_le (hρ.smooth n) (hρ.cs n) (hρ.nonneg n) (hρ.integral n) hv).1
    have hlim := tendsto_integral_mul hkhm hv hmem (moll_tendsto hρ hv)
    have e1 : ∀ n, ∫ x, h x * an n x * E.w x = ∫ x, kh x * an n x := by
      intro n
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ S
      · simp only [hkh, Set.indicator_of_mem hx]; ring
      · simp [hkh, Set.indicator_of_notMem hx, hanv0 n x hx]
    have e2 : ∫ x, h x * v x * E.w x = ∫ x, kh x * v x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ S
      · simp only [hkh, Set.indicator_of_mem hx]; ring
      · have hxT : x ∉ T := fun h' => hx (Metric.self_subset_cthickening _ h')
        simp [hkh, Set.indicator_of_notMem hx, hv0 x hxT]
    simp only [e1, e2]
    exact hlim.neg
  exact tendsto_nhds_unique hLHS (by simpa only [hform] using hRHS)

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
