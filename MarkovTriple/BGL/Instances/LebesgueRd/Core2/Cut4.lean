import Mathlib
import MarkovTriple.BGL.Instances.LebesgueRd.Full.EsaCut

/-!
# Fourth-order cut-off estimate on `ℝ^d` (Round 25, stream F)

For smooth `v` whose jets `v, ∂v, ∂²v, ∂³v, Δv, ∂Δv, ΔΔv` lie in `L²`, the cut-offs `ζ_n v = cut n * v` satisfy
`ζ_n v → v`, `Δ(ζ_n v) → Δ v`, `ΔΔ(ζ_n v) → ΔΔ v` in `L²` (`cutoff4_graph_aux`).  The commutator terms are
`(Σ_j ∂_jζ_n ∂_j v)`, `Δζ_n · v`: products of a rescaled profile `c^k ψ(c x)` (`c = 1/(n+1)`, `k ≥ 1`) with `L²` jets.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.LebesgueRd

variable {d : ℕ}

/-! ### Linearity of `Lf` -/

lemma Lf_add' {f g : (Fin d → ℝ) → ℝ} (hf : Sm f) (hg : Sm g) (x : Fin d → ℝ) :
    Lf (f + g) x = Lf f x + Lf g x := by
  unfold Lf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dd_add hf hg i, dd_add (hf.dd i) (hg.dd i) i]
  rfl

lemma Lf_smul' (c : ℝ) {f : (Fin d → ℝ) → ℝ} (hf : Sm f) (x : Fin d → ℝ) :
    Lf (c • f) x = c * Lf f x := by
  unfold Lf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [dd_smul c hf i, dd_smul c (hf.dd i) i]
  rfl

/-! ### Rescaled profiles -/

/-- `Sc k ψ c = c^k ψ(c ·)`. -/
noncomputable def Sc (k : ℕ) (ψ : (Fin d → ℝ) → ℝ) (c : ℝ) : (Fin d → ℝ) → ℝ := fun x => c ^ k * ψ (c • x)

lemma Sc_smooth (k : ℕ) {ψ : (Fin d → ℝ) → ℝ} (hψ : Sm ψ) (c : ℝ) : Sm (Sc k ψ c) :=
  contDiff_const.mul (hψ.comp (contDiff_const_smul c))

lemma dd_Sc (k : ℕ) {ψ : (Fin d → ℝ) → ℝ} (hψ : Sm ψ) (c : ℝ) (i : Fin d) :
    dd i (Sc k ψ c) = Sc (k + 1) (dd i ψ) c := by
  funext x
  have h1 : Sm (fun y : Fin d → ℝ => ψ (c • y)) := hψ.comp (contDiff_const_smul c)
  have := dd_const_mul h1 (c ^ k) i x
  unfold Sc
  rw [this, congrFun (dd_scale_E hψ c i) x]
  ring

lemma Lf_Sc (k : ℕ) {ψ : (Fin d → ℝ) → ℝ} (hψ : Sm ψ) (c : ℝ) (x : Fin d → ℝ) :
    Lf (Sc k ψ c) x = Sc (k + 2) (Lf ψ) c x := by
  unfold Lf
  have : ∀ i, dd i (dd i (Sc k ψ c)) x = Sc (k + 2) (dd i (dd i ψ)) c x := by
    intro i
    rw [dd_Sc k hψ c i, dd_Sc (k + 1) (hψ.dd i) c i]
  simp only [this]
  unfold Sc
  rw [Finset.mul_sum]

lemma dd_cut_eq_Sc (n : ℕ) (j : Fin d) :
    dd j (cut n : (Fin d → ℝ) → ℝ) = Sc 1 (dd j (cut 0 : (Fin d → ℝ) → ℝ)) (((n : ℝ) + 1)⁻¹) := by
  funext x
  rw [dd_cut]
  unfold Sc
  ring

lemma Lf_cut_eq_Sc (n : ℕ) :
    Lf (cut n : (Fin d → ℝ) → ℝ) = Sc 2 (Lf (cut 0 : (Fin d → ℝ) → ℝ)) (((n : ℝ) + 1)⁻¹) := by
  funext x
  unfold Lf Sc
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => dd_dd_cut n i x

/-- bounds of rescaled profiles: `|m|, |∂ᵢ m|, |Δ m| ≤ K/(n+1)`. -/
structure SmallFam (m : ℕ → (Fin d → ℝ) → ℝ) (K : ℝ) : Prop where
  sm : ∀ n, Sm (m n)
  b0 : ∀ n x, |m n x| ≤ K * (1 / ((n : ℝ) + 1))
  b1 : ∀ n i x, |dd i (m n) x| ≤ K * (1 / ((n : ℝ) + 1))
  b2 : ∀ n x, |Lf (m n) x| ≤ K * (1 / ((n : ℝ) + 1))

lemma SmallFam.mono {m : ℕ → (Fin d → ℝ) → ℝ} {K K' : ℝ} (h : SmallFam m K) (hK : K ≤ K') : SmallFam m K' where
  sm := h.sm
  b0 n x := (h.b0 n x).trans (mul_le_mul_of_nonneg_right hK (by positivity))
  b1 n i x := (h.b1 n i x).trans (mul_le_mul_of_nonneg_right hK (by positivity))
  b2 n x := (h.b2 n x).trans (mul_le_mul_of_nonneg_right hK (by positivity))

lemma pow_le_self_of_le_one {c : ℝ} (h0 : 0 ≤ c) (h1 : c ≤ 1) {k : ℕ} (hk : 1 ≤ k) : c ^ k ≤ c := by
  calc c ^ k ≤ c ^ 1 := pow_le_pow_of_le_one h0 h1 hk
    _ = c := pow_one c

lemma abs_Sc_le {k : ℕ} (hk : 1 ≤ k) {ψ : (Fin d → ℝ) → ℝ} {B : ℝ} (hB : ∀ x, |ψ x| ≤ B) (n : ℕ)
    (x : Fin d → ℝ) : |Sc k ψ (((n : ℝ) + 1)⁻¹) x| ≤ B * (1 / ((n : ℝ) + 1)) := by
  unfold Sc
  have hc0 : (0 : ℝ) ≤ ((n : ℝ) + 1)⁻¹ := by positivity
  have hc1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
  rw [abs_mul, abs_of_nonneg (pow_nonneg hc0 k)]
  calc ((n : ℝ) + 1)⁻¹ ^ k * |ψ (((n : ℝ) + 1)⁻¹ • x)|
      ≤ ((n : ℝ) + 1)⁻¹ * B :=
        mul_le_mul (pow_le_self_of_le_one hc0 hc1 hk) (hB _) (abs_nonneg _) hc0
    _ = B * (1 / ((n : ℝ) + 1)) := by rw [one_div]; ring

lemma smallFam_Sc {k : ℕ} (hk : 1 ≤ k) {ψ : (Fin d → ℝ) → ℝ} (hψ : ψ ∈ A₀ d) :
    ∃ K : ℝ, 0 ≤ K ∧ SmallFam (fun n => Sc k ψ (((n : ℝ) + 1)⁻¹)) K := by
  obtain ⟨B0, hB0n, hB0⟩ := bound_of_A₀ hψ
  have h1 : ∀ i : Fin d, ∃ B, 0 ≤ B ∧ ∀ x, |dd i ψ x| ≤ B := fun i => bound_of_A₀ (dd_mem hψ i)
  choose B1 hB1n hB1 using h1
  obtain ⟨B2, hB2n, hB2⟩ := bound_of_A₀ (Lf_mem hψ)
  refine ⟨B0 + ∑ i, B1 i + B2, by have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hB1n j); linarith, ?_⟩
  have hs : ∀ i, B1 i ≤ ∑ j, B1 j := fun i =>
    Finset.single_le_sum (f := B1) (fun j _ => hB1n j) (Finset.mem_univ i)
  refine ⟨fun n => Sc_smooth k (smooth hψ) _, fun n x => ?_, fun n i x => ?_, fun n x => ?_⟩
  · exact (abs_Sc_le hk hB0 n x).trans (mul_le_mul_of_nonneg_right (by linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hB1n j)]) (by positivity))
  · rw [dd_Sc k (smooth hψ) _ i]
    exact (abs_Sc_le (by omega) (hB1 i) n x).trans (mul_le_mul_of_nonneg_right (by linarith [hs i, hB0n, hB2n]) (by positivity))
  · rw [Lf_Sc k (smooth hψ) _ x]
    exact (abs_Sc_le (by omega) hB2 n x).trans (mul_le_mul_of_nonneg_right (by linarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hB1n j)]) (by positivity))


/-! ### Products of a small family with an `L²` jet -/

lemma Sm_Lf {f : (Fin d → ℝ) → ℝ} (hf : Sm f) : Sm (Lf f) :=
  ContDiff.sum fun i _ => ((hf.dd i).dd i)

/-- the `L²` majorant of `Δ(m g)`. -/
noncomputable def Qf (g : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ‖Lf g x‖ + ‖g x‖ + 2 * ∑ i, ‖dd i g x‖

lemma memLp_Qf {g : (Fin d → ℝ) → ℝ} (h0 : MemLp g 2 volume) (h1 : ∀ i, MemLp (dd i g) 2 volume)
    (h2 : MemLp (Lf g) 2 volume) : MemLp (Qf g) 2 volume := by
  unfold Qf
  exact (h2.norm.add h0.norm).add ((memLp_finsetSum _ fun i _ => (h1 i).norm).const_mul 2)

lemma abs_Lf_mul_le {m : ℕ → (Fin d → ℝ) → ℝ} {K : ℝ} (hm : SmallFam m K) {g : (Fin d → ℝ) → ℝ}
    (hg : Sm g) (n : ℕ) (x : Fin d → ℝ) :
    |Lf (m n * g) x| ≤ K * (1 / ((n : ℝ) + 1)) * Qf g x := by
  set ε : ℝ := K * (1 / ((n : ℝ) + 1)) with hε
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hm.b0 n x)
  rw [Lf_mul (hm.sm n) hg x]
  have e1 : |m n x * Lf g x| ≤ ε * ‖Lf g x‖ := by
    rw [abs_mul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (hm.b0 n x) (abs_nonneg _)
  have e2 : |g x * Lf (m n) x| ≤ ε * ‖g x‖ := by
    rw [abs_mul, Real.norm_eq_abs, mul_comm]; exact mul_le_mul_of_nonneg_right (hm.b2 n x) (abs_nonneg _)
  have e3 : |Gf (m n) g x| ≤ ε * ∑ i, ‖dd i g x‖ := by
    unfold Gf
    calc |∑ i, dd i (m n) x * dd i g x| ≤ ∑ i, |dd i (m n) x * dd i g x| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ε * ‖dd i g x‖ := Finset.sum_le_sum fun i _ => by
          rw [abs_mul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_right (hm.b1 n i x) (abs_nonneg _)
      _ = _ := by rw [Finset.mul_sum]
  have e4 : |2 * Gf (m n) g x| ≤ 2 * (ε * ∑ i, ‖dd i g x‖) := by
    rw [abs_mul, abs_two]; linarith
  calc |m n x * Lf g x + g x * Lf (m n) x + 2 * Gf (m n) g x|
      ≤ |m n x * Lf g x + g x * Lf (m n) x| + |2 * Gf (m n) g x| := abs_add_le _ _
    _ ≤ |m n x * Lf g x| + |g x * Lf (m n) x| + |2 * Gf (m n) g x| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ε * Qf g x := by unfold Qf; nlinarith

/-! ### The fourth-order cut-off -/

lemma Lf_cut_mul_fun {v : (Fin d → ℝ) → ℝ} (hv : Sm v) (n : ℕ) :
    Lf (cut n * v) = (cut n * Lf v) + (Lf (cut n) * v) +
      (2 : ℝ) • (fun x => ∑ j, (dd j (cut n) * dd j v) x) := by
  funext x
  rw [Lf_mul (cut_smooth n) hv x]
  simp only [Gf, Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
  ring

lemma LL_cut {v : (Fin d → ℝ) → ℝ} (hv : Sm v) (n : ℕ) (x : Fin d → ℝ) :
    Lf (Lf (cut n * v)) x = Lf (cut n * Lf v) x + Lf (Lf (cut n) * v) x +
      2 * ∑ j, Lf (dd j (cut n) * dd j v) x := by
  rw [Lf_cut_mul_fun hv n]
  have hA : Sm (cut n * Lf v) := (cut_smooth n).mul (Sm_Lf hv)
  have hB : Sm (Lf (cut n) * v) := (Sm_Lf (cut_smooth n)).mul hv
  have hC : ∀ j, Sm (dd j (cut n) * dd j v) := fun j => ((cut_smooth n).dd j).mul (hv.dd j)
  have hC' : Sm (fun x => ∑ j, (dd j (cut n) * dd j v) x) := ContDiff.sum fun j _ => hC j
  have hAB : Sm (cut n * Lf v + Lf (cut n) * v) := hA.add hB
  have hC2 : Sm ((2 : ℝ) • (fun x => ∑ j, (dd j (cut n) * dd j v) x)) := hC'.const_smul (2 : ℝ)
  rw [Lf_add' hAB hC2, Lf_add' hA hB, Lf_smul' 2 hC',
    Lf_fsum (h := fun j => dd j (cut n) * dd j v) hC]

theorem cutoff4_graph_aux {v : (Fin d → ℝ) → ℝ} (hv : Sm v) (h0 : MemLp v 2 volume)
    (h1 : ∀ i, MemLp (dd i v) 2 volume) (h2 : MemLp (Lf v) 2 volume)
    (h11 : ∀ j i, MemLp (dd i (dd j v)) 2 volume) (h12 : ∀ j, MemLp (Lf (dd j v)) 2 volume)
    (h3 : ∀ i, MemLp (dd i (Lf v)) 2 volume) (h4 : MemLp (Lf (Lf v)) 2 volume) :
    Tendsto (fun n : ℕ => ∫ x, (Lf (Lf (cut n * v)) x - Lf (Lf v) x) ^ 2) atTop (𝓝 0) := by
  -- small families
  obtain ⟨K2, hK2n, hK2⟩ := smallFam_Sc (d := d) (k := 2) (by norm_num) (Lf_mem (cut_mem 0))
  have hm2 : SmallFam (fun n => Lf (cut n : (Fin d → ℝ) → ℝ)) K2 := by
    have : (fun n : ℕ => Lf (cut n : (Fin d → ℝ) → ℝ)) =
        fun n : ℕ => Sc 2 (Lf (cut 0 : (Fin d → ℝ) → ℝ)) (((n : ℝ) + 1)⁻¹) := funext Lf_cut_eq_Sc
    rw [this]; exact hK2
  have h1K : ∀ j : Fin d, ∃ K : ℝ, 0 ≤ K ∧
      SmallFam (fun n => dd j (cut n : (Fin d → ℝ) → ℝ)) K := fun j => by
    obtain ⟨K, hK, hS⟩ := smallFam_Sc (d := d) (k := 1) le_rfl (dd_mem (cut_mem 0) j)
    refine ⟨K, hK, ?_⟩
    have : (fun n : ℕ => dd j (cut n : (Fin d → ℝ) → ℝ)) =
        fun n : ℕ => Sc 1 (dd j (cut 0 : (Fin d → ℝ) → ℝ)) (((n : ℝ) + 1)⁻¹) :=
      funext (fun n => dd_cut_eq_Sc n j)
    rw [this]; exact hS
  choose K1 hK1n hK1 using h1K
  set K : ℝ := K2 + ∑ j, K1 j with hK
  have hKs : ∀ j, K1 j ≤ ∑ i, K1 i := fun j =>
    Finset.single_le_sum (f := K1) (fun i _ => hK1n i) (Finset.mem_univ j)
  have hKsum : 0 ≤ ∑ i, K1 i := Finset.sum_nonneg fun i _ => hK1n i
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  have hmK2 : SmallFam (fun n => Lf (cut n : (Fin d → ℝ) → ℝ)) K := hm2.mono (by linarith)
  have hmK1 : ∀ j, SmallFam (fun n => dd j (cut n : (Fin d → ℝ) → ℝ)) K := fun j =>
    (hK1 j).mono (by linarith [hKs j])
  -- the majorant
  set Q : (Fin d → ℝ) → ℝ := fun x => Qf v x + 2 * ∑ j, Qf (dd j v) x with hQ
  have hQL : MemLp Q 2 volume :=
    (memLp_Qf h0 h1 h2).add ((memLp_finsetSum _ fun j _ => memLp_Qf (h1 j) (h11 j) (h12 j)).const_mul 2)
  set H : ℕ → (Fin d → ℝ) → ℝ := fun n x =>
    Lf (Lf (cut n) * v) x + 2 * ∑ j, Lf (dd j (cut n) * dd j v) x with hH
  have hHb : ∀ n x, |H n x| ≤ K * (1 / ((n : ℝ) + 1)) * Q x := by
    intro n x
    have b1 := abs_Lf_mul_le hmK2 hv n x
    have b2 : ∀ j, |Lf (dd j (cut n) * dd j v) x| ≤ K * (1 / ((n : ℝ) + 1)) * Qf (dd j v) x :=
      fun j => abs_Lf_mul_le (hmK1 j) (hv.dd j) n x
    have b3 : |∑ j, Lf (dd j (cut n) * dd j v) x| ≤
        K * (1 / ((n : ℝ) + 1)) * ∑ j, Qf (dd j v) x := by
      calc _ ≤ ∑ j, |Lf (dd j (cut n) * dd j v) x| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, K * (1 / ((n : ℝ) + 1)) * Qf (dd j v) x := Finset.sum_le_sum fun j _ => b2 j
        _ = _ := by rw [Finset.mul_sum]
    calc |H n x| ≤ |Lf (Lf (cut n) * v) x| + |2 * ∑ j, Lf (dd j (cut n) * dd j v) x| := abs_add_le _ _
      _ ≤ K * (1 / ((n : ℝ) + 1)) * Qf v x + 2 * (K * (1 / ((n : ℝ) + 1)) * ∑ j, Qf (dd j v) x) := by
          rw [abs_mul, abs_two]; linarith
      _ = _ := by rw [hQ]; ring
  -- the cut-off of `Lf v`
  have hLs : Sm (Lf v) := Sm_Lf hv
  have hA := cutoff_graph_aux hLs h2 h3 h4
  have hmem : ∀ n : ℕ, Lf (cut n * Lf v) ∈ A₀ d := fun n =>
    Lf_mem (mem_A₀.2 ⟨(cut_smooth n).mul hLs, (cut_cs n).mul_right⟩)
  have hAL : ∀ n : ℕ, MemLp (fun x => Lf (cut n * Lf v) x - Lf (Lf v) x) 2 volume := fun n =>
    (memLp_of (hmem n) 2).sub h4
  have hr : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hQ2 : Integrable (fun x => (Q x) ^ 2) := hQL.integrable_sq
  have hbnd : Tendsto (fun n : ℕ => 2 * (∫ x, (Lf (cut n * Lf v) x - Lf (Lf v) x) ^ 2) +
      2 * ((K * (1 / ((n : ℝ) + 1))) ^ 2 * ∫ x, (Q x) ^ 2)) atTop (𝓝 0) := by
    have h5 : Tendsto (fun n : ℕ => (K * (1 / ((n : ℝ) + 1))) ^ 2 * ∫ x, (Q x) ^ 2) atTop (𝓝 0) := by
      have := ((hr.const_mul K).pow 2).mul_const (∫ x, (Q x) ^ 2)
      simpa using this
    have := (hA.const_mul 2).add (h5.const_mul 2)
    simpa using this
  refine squeeze_zero (fun n => integral_nonneg fun x => sq_nonneg _) (fun n => ?_) hbnd
  have hint : Integrable (fun x => 2 * (Lf (cut n * Lf v) x - Lf (Lf v) x) ^ 2 +
      2 * ((K * (1 / ((n : ℝ) + 1))) ^ 2 * (Q x) ^ 2)) :=
    ((hAL n).integrable_sq.const_mul 2).add (hQ2.const_mul _ |>.const_mul 2)
  calc ∫ x, (Lf (Lf (cut n * v)) x - Lf (Lf v) x) ^ 2
      ≤ ∫ x, (2 * (Lf (cut n * Lf v) x - Lf (Lf v) x) ^ 2 +
        2 * ((K * (1 / ((n : ℝ) + 1))) ^ 2 * (Q x) ^ 2)) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hint
          (Filter.Eventually.of_forall fun x => ?_)
        beta_reduce
        have e : Lf (Lf (cut n * v)) x - Lf (Lf v) x =
            (Lf (cut n * Lf v) x - Lf (Lf v) x) + H n x := by
          rw [LL_cut hv n x]; simp only [hH]; ring
        have hb : (H n x) ^ 2 ≤ (K * (1 / ((n : ℝ) + 1))) ^ 2 * (Q x) ^ 2 := by
          rw [← mul_pow, ← sq_abs (H n x)]
          exact pow_le_pow_left₀ (abs_nonneg _) (hHb n x) 2
        rw [e]
        nlinarith [sq_nonneg ((Lf (cut n * Lf v) x - Lf (Lf v) x) - H n x)]
    _ = 2 * (∫ x, (Lf (cut n * Lf v) x - Lf (Lf v) x) ^ 2) +
        2 * ((K * (1 / ((n : ℝ) + 1))) ^ 2 * ∫ x, (Q x) ^ 2) := by
        rw [integral_add ((hAL n).integrable_sq.const_mul 2) (hQ2.const_mul _ |>.const_mul 2),
          integral_const_mul, integral_const_mul, integral_const_mul]

end MarkovTriple.BGL.LebesgueRd
