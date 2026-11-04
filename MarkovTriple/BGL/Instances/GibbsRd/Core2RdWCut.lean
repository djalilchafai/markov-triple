import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdMain
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdWDefs

/-!
# `Core2` on `ℝ^d` with WEIGHTED commutators (R19, Stream A5, target C4)

R18 (`CoeffGood`, `cutoff_ZL`) needed the coefficients `Lχ_n`, `∂Lχ_n`, `LLχ_n`, `V_ij χ_i` bounded uniformly (hence `BddHess3`).
Here only the pure cut-off derivatives `∂^α χ_n` (`1 ≤ |α| ≤ 4`) are `Good`; every occurrence of `∇V`, `∇²V`, `∇³V` is absorbed into a
weighted jet of `v` that is in `L²(μ)`: with `g ∈ L²` and `∂ₖV g ∈ L²`, `∂ₖV ∂ⱼV g ∈ L²`, the sequences
`Lχ_n g`, `∂ₖ(Lχ_n) g`, `L(Lχ_n) g` tend to `0` in `L²(μ)` under `GrowHess3`
(`ZL_Lchi`, `ZL_dLchi`, `ZL_LLchi`), and `cutoff_ZL_w` is the weighted analogue of `cutoff_ZL`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- derivatives of the cut-off vanish inside the ball. -/
lemma dw_zero_of_open {R : ℝ} (hR : 0 < R) :
    ∀ (w : List (Fin d)), w ≠ [] → ∀ y ∈ {x : Rd d | qd x < R ^ 2}, dw w (cut R) y = 0
  | [], h, _, _ => absurd rfl h
  | [i], _, y, hy =>
    pderiv_eq_zero_of_open (isOpen_inner R) (c := 1) (fun z hz => cut_eq_one hR (le_of_lt hz)) hy i
  | i :: j :: w, _, y, hy =>
    pderiv_eq_zero_of_open (isOpen_inner R) (c := 0)
      (fun z hz => dw_zero_of_open hR (j :: w) (by simp) z hz) hy i

/-- the derivatives of order `1..4` of `χ_n` are `Good`. -/
lemma good_dw (w : List (Fin d)) (h1 : 1 ≤ w.length) (h4 : w.length ≤ 4) :
    Good (fun (n : ℕ) (x : Rd d) => dw w (chi n) x) := by
  obtain ⟨B, hB0, hB⟩ := cut_deriv_bound (d := d)
  refine ⟨fun n => (sm_dw w (sm_cut _)).continuous, ⟨B, fun n x => ?_⟩, fun x => ?_⟩
  · have hR : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h := hB ((n : ℝ) + 1) hR w h4 x
    have hl := l1_nonneg x
    have hw1 : 1 ≤ 1 + l1 x / ((n : ℝ) + 1) := by
      have : 0 ≤ l1 x / ((n : ℝ) + 1) := by positivity
      linarith
    have h2 : |dw w (cut ((n : ℝ) + 1)) x| ≤ (1 + l1 x / ((n : ℝ) + 1)) ^ 2 * |dw w (cut ((n : ℝ) + 1)) x| := by
      have : (1 : ℝ) ≤ (1 + l1 x / ((n : ℝ) + 1)) ^ 2 := one_le_pow₀ hw1
      nlinarith [abs_nonneg (dw w (cut ((n : ℝ) + 1)) x)]
    exact h2.trans (h.trans (div_le_self hB0 (one_le_pow₀ hR)))
  · filter_upwards [eventually_qd_lt x] with n hn
    exact dw_zero_of_open (by positivity) w (List.ne_nil_of_length_pos h1) x hn

section weighted
variable {μ : Measure (Rd d)}

/-- `Lχ_n · g → 0` when `g, ∂ₖV g ∈ L²`. -/
lemma ZL_Lchi {V g : Rd d → ℝ} (hg : MemLp g 2 μ) (hVg : ∀ k, MemLp (fun x => pderiv V k x * g x) 2 μ) :
    ZL μ (fun n x => Lr V (chi n) x * g x) := by
  have hs : ZL μ (fun n x => ∑ i, (dw [i, i] (chi n) x * g x - dw [i] (chi n) x * (pderiv V i x * g x))) :=
    ZL.finset_sum _ fun i _ => (ZL.of_good (good_dw [i, i] (by simp) (by simp)) hg).sub
      (ZL.of_good (good_dw [i] (by simp) (by simp)) (hVg i))
  refine hs.congr fun n x => ?_
  simp only [Lr, Finset.sum_mul, sub_mul, dw]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

variable {G : GibbsRdData d}

/-- `∂ₖ(Lχ_n) · g → 0` when `g, ∂ₘV g ∈ L²` (growth of `Hess V`). -/
lemma ZL_dLchi (hgr : G.GrowHess3) (k : Fin d) {g : Rd d → ℝ} (hg : MemLp g 2 μ)
    (hVg : ∀ m, MemLp (fun x => pderiv G.V m x * g x) 2 μ) :
    ZL μ (fun n x => pderiv (Lr G.V (chi n)) k x * g x) := by
  obtain ⟨C2, hC2⟩ := hgr.hess
  have m2 : ∀ j, MemLp (fun x => pderiv (pderiv G.V j) k x * g x) 2 μ := fun j =>
    memLp_mul_growth ((G.smooth.pderiv j).pderiv k).continuous.aestronglyMeasurable
      (fun x => hC2 x j k) hg hVg
  have hs : ZL μ (fun n x => ∑ j, (dw [k, j, j] (chi n) x * g x -
      (dw [j] (chi n) x * (pderiv (pderiv G.V j) k x * g x) +
        dw [k, j] (chi n) x * (pderiv G.V j x * g x)))) :=
    ZL.finset_sum _ fun j _ => (ZL.of_good (good_dw [k, j, j] (by simp) (by simp)) hg).sub
      ((ZL.of_good (good_dw [j] (by simp) (by simp)) (m2 j)).add
        (ZL.of_good (good_dw [k, j] (by simp) (by simp)) (hVg j)))
  refine hs.congr fun n x => ?_
  rw [pderiv_Lr' G.smooth (sm_cut _) k x, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [dw]
  ring

/-- `L(Lχ_n) · g → 0` when `g, ∂ⱼV g, ∂ⱼV(∂ₖV g) ∈ L²`. -/
lemma ZL_LLchi (hgr : G.GrowHess3) {g : Rd d → ℝ} (hg : MemLp g 2 μ)
    (hVg : ∀ m, MemLp (fun x => pderiv G.V m x * g x) 2 μ)
    (hVVg : ∀ j k, MemLp (fun x => pderiv G.V j x * (pderiv G.V k x * g x)) 2 μ) :
    ZL μ (fun n x => Lr G.V (Lr G.V (chi n)) x * g x) := by
  obtain ⟨C2, hC2⟩ := hgr.hess
  obtain ⟨C3, hC3⟩ := hgr.third
  have m2 : ∀ j k, MemLp (fun x => pderiv (pderiv G.V j) k x * g x) 2 μ := fun j k =>
    memLp_mul_growth ((G.smooth.pderiv j).pderiv k).continuous.aestronglyMeasurable
      (fun x => hC2 x j k) hg hVg
  have m3 : ∀ j k, MemLp (fun x => pderiv (pderiv (pderiv G.V j) k) k x * g x) 2 μ := fun j k =>
    memLp_mul_growth (((G.smooth.pderiv j).pderiv k).pderiv k).continuous.aestronglyMeasurable
      (fun x => hC3 x j k k) hg hVg
  have m5 : ∀ j k, MemLp (fun x => pderiv (pderiv G.V j) k x * (pderiv G.V k x * g x)) 2 μ := fun j k =>
    memLp_mul_growth ((G.smooth.pderiv j).pderiv k).continuous.aestronglyMeasurable
      (fun x => hC2 x j k) (hVg k) (hVVg · k)
  have gd : ∀ w : List (Fin d), 1 ≤ w.length → w.length ≤ 4 →
      Good (fun (n : ℕ) (x : Rd d) => dw w (chi n) x) := good_dw
  have hs : ZL μ (fun n x => ∑ k, ∑ j,
      (dw [k, k, j, j] (chi n) x * g x - dw [j] (chi n) x * (pderiv (pderiv (pderiv G.V j) k) k x * g x)
        - 2 * (dw [k, j] (chi n) x * (pderiv (pderiv G.V j) k x * g x))
        - dw [k, k, j] (chi n) x * (pderiv G.V j x * g x)
        - dw [k, j, j] (chi n) x * (pderiv G.V k x * g x)
        + dw [j] (chi n) x * (pderiv (pderiv G.V j) k x * (pderiv G.V k x * g x))
        + dw [k, j] (chi n) x * (pderiv G.V k x * (pderiv G.V j x * g x)))) := by
    refine ZL.finset_sum _ fun k _ => ZL.finset_sum _ fun j _ => ?_
    have p1 := ZL.of_good (gd [k, k, j, j] (by simp) (by simp)) hg
    have p2 := ZL.of_good (gd [j] (by simp) (by simp)) (m3 j k)
    have p3 := (ZL.of_good (gd [k, j] (by simp) (by simp)) (m2 j k)).const_mul 2
    have p4 := ZL.of_good (gd [k, k, j] (by simp) (by simp)) (hVg j)
    have p5 := ZL.of_good (gd [k, j, j] (by simp) (by simp)) (hVg k)
    have p6 := ZL.of_good (gd [j] (by simp) (by simp)) (m5 j k)
    have p7 := ZL.of_good (gd [k, j] (by simp) (by simp)) (hVVg k j)
    exact ((((((p1.sub p2).sub p3).sub p4).sub p5).add p6).add p7)
  refine hs.congr fun n x => ?_
  have hχ : Sm (chi n : Rd d → ℝ) := sm_cut _
  have hP : Sm (Lr G.V (chi n)) := sm_Lr G.smooth hχ
  have e1 : Lr G.V (Lr G.V (chi n)) x = ∑ k, (pderiv (pderiv (Lr G.V (chi n)) k) k x -
      pderiv G.V k x * pderiv (Lr G.V (chi n)) k x) := rfl
  rw [e1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [pderiv_pderiv_Lr G hχ k k x, pderiv_Lr' G.smooth hχ k x, sub_mul, Finset.mul_sum]
  simp only [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [dw]
  ring

end weighted

end MarkovTriple.BGL.Instances.GibbsRd

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- `χ_n − 1` is `Good`. -/
lemma good_chi_sub_one : Good (fun (n : ℕ) (x : Rd d) => chi n x - 1) := by
  refine ⟨fun n => ((sm_cut _).continuous.sub continuous_const), ⟨1, fun n x => ?_⟩, fun x => ?_⟩
  · have h0 := cut_nonneg (((n : ℕ) : ℝ) + 1) x
    have h1 := cut_le_one (((n : ℕ) : ℝ) + 1) x
    show |cut _ x - 1| ≤ 1
    rw [abs_le]; constructor <;> linarith
  · filter_upwards [eventually_qd_lt x] with n hn
    have : cut (((n : ℕ) : ℝ) + 1) x = 1 := cut_eq_one (by positivity) (le_of_lt hn)
    show cut _ x - 1 = 0
    rw [this]; ring

/-- **C4: the three graph-norm cut-off estimates with weighted commutators** (`GrowHess3` instead of `BddHess3`):
`χ_n v → v`, `L(χ_n v) → L v`, `L²(χ_n v) → L² v` in `L²(μ)`. -/
theorem cutoff_ZL_w {μ : Measure (Rd d)} {G : GibbsRdData d} (hgr : G.GrowHess3) {v : Rd d → ℝ} (hv : Sm v)
    (h0 : MemLp v 2 μ) (h1 : ∀ i, MemLp (pderiv v i) 2 μ) (h2 : ∀ i j, MemLp (pderiv (pderiv v i) j) 2 μ)
    (hLv : MemLp (Lr G.V v) 2 μ) (hLLv : MemLp (Lr G.V (Lr G.V v)) 2 μ)
    (hLv1 : ∀ i, MemLp (pderiv (Lr G.V v) i) 2 μ)
    (hW1 : ∀ k, MemLp (fun x => pderiv G.V k x * v x) 2 μ)
    (hW2 : ∀ k i, MemLp (fun x => pderiv G.V k x * pderiv v i x) 2 μ)
    (hW3 : ∀ j k, MemLp (fun x => pderiv G.V j x * (pderiv G.V k x * v x)) 2 μ)
    (hWL : ∀ k, MemLp (fun x => pderiv G.V k x * Lr G.V v x) 2 μ) :
    ZL μ (fun n x => chi n x * v x - v x) ∧
    ZL μ (fun n x => Lr G.V (chi n * v) x - Lr G.V v x) ∧
    ZL μ (fun n x => Lr G.V (Lr G.V (chi n * v)) x - Lr G.V (Lr G.V v) x) := by
  obtain ⟨C2, hC2⟩ := hgr.hess
  have hχ : ∀ n, Sm (chi n : Rd d → ℝ) := fun n => sm_cut _
  have gd : ∀ w : List (Fin d), 1 ≤ w.length → w.length ≤ 4 →
      Good (fun (n : ℕ) (x : Rd d) => dw w (chi n) x) := good_dw
  have g1 := good_chi_sub_one (d := d)
  refine ⟨?_, ?_, ?_⟩
  · exact (ZL.of_good g1 h0).congr (fun n x => by ring)
  · have hsum : ZL μ (fun n x => ∑ i, dw [i] (chi n) x * pderiv v i x) :=
      ZL.finset_sum _ (fun i _ => ZL.of_good (gd [i] (by simp) (by simp)) (h1 i))
    refine (((ZL.of_good g1 hLv).add (ZL_Lchi h0 hW1)).add (hsum.const_mul 2)).congr (fun n x => ?_)
    rw [Lr_chi_v hv (hχ n) x]
    simp only [Gr, dw]
    ring
  · have s1 : ZL μ (fun n x => (chi n x - 1) * Lr G.V (Lr G.V v) x) := ZL.of_good g1 hLLv
    have s2 : ZL μ (fun n x => Lr G.V (chi n) x * Lr G.V v x) := ZL_Lchi hLv hWL
    have s3 : ZL μ (fun n x => ∑ i, dw [i] (chi n) x * pderiv (Lr G.V v) i x) :=
      ZL.finset_sum _ (fun i _ => ZL.of_good (gd [i] (by simp) (by simp)) (hLv1 i))
    have s4 : ZL μ (fun n x => Lr G.V (Lr G.V (chi n)) x * v x) := ZL_LLchi hgr h0 hW1 hW3
    have s5 : ZL μ (fun n x => ∑ i, pderiv (Lr G.V (chi n)) i x * pderiv v i x) :=
      ZL.finset_sum _ (fun i _ => ZL_dLchi hgr i (h1 i) (fun m => hW2 m i))
    have s6 : ZL μ (fun n x => ∑ i, ∑ j, dw [j, i] (chi n) x * pderiv (pderiv v i) j x) :=
      ZL.finset_sum _ (fun i _ => ZL.finset_sum _ (fun j _ =>
        ZL.of_good (gd [j, i] (by simp) (by simp)) (h2 i j)))
    have s7 : ZL μ (fun n x => ∑ i, ∑ j,
        pderiv (pderiv G.V i) j x * pderiv (chi n) i x * pderiv v j x) :=
      ZL.finset_sum _ (fun i _ => ZL.finset_sum _ (fun j _ =>
        (ZL.of_good (gd [i] (by simp) (by simp))
          (memLp_mul_growth ((G.smooth.pderiv i).pderiv j).continuous.aestronglyMeasurable
            (fun x => hC2 x i j) (h1 j) (fun m => hW2 m j))).congr (fun n x => by simp only [dw]; ring)))
    refine ((((((s1.add (s2.const_mul 2)).add (s3.const_mul 4)).add s4).add (s5.const_mul 4)).add
      (s6.const_mul 4)).add (s7.const_mul 4)).congr (fun n x => ?_)
    rw [Lr_Lr_mul G.smooth hv (hχ n) x]
    simp only [Gr, dw]
    ring

end MarkovTriple.BGL.Instances.GibbsRd
