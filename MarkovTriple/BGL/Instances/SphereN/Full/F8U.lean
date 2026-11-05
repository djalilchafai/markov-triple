import Mathlib
import MarkovTriple.BGL.Instances.SphereN.Full.Expand

/-!
# F8 for the round sphere (Round 32, stream Y, steps 3b-4)

For `t > 0` and every `u ∈ L²(σ)`: `P_t u = Σ_k e^{-λ_k t} a_k` (`exists_expansion`, `sphere_semigroup_harm`), the polynomial
series `Σ_k e^{-λ_k t} h_k(y)` is `C^∞` on `ℝ^n` (`contDiff_top_Fs`: `‖h_k‖_{L²} ≤ ‖u‖` and the Gaussian factor beats every
exponential), and its restriction to the sphere is the `L²` limit.  Hence `sphereF8` and the unconditional `sphereFullU`.
-/

open MeasureTheory MvPolynomial Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.SphereN

variable {n : ℕ}

lemma summable_gauss (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) {c : ℝ} (hc : 0 ≤ c) :
    Summable fun k : ℕ => c ^ k * Real.exp (-((k : ℝ) * (k + n - 2)) * t) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hT : Tendsto (fun k : ℕ => (c + 1) * Real.exp (-(t * k))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k : ℕ => Real.exp (-(t * k))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp
        (Tendsto.const_mul_atTop ht tendsto_natCast_atTop_atTop))
    simpa using h1.const_mul (c + 1)
  have hev : ∀ᶠ k : ℕ in atTop, (c + 1) * Real.exp (-(t * k)) ≤ 1 / 2 :=
    hT.eventually (ge_mem_nhds (by norm_num))
  refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => (1 / 2 : ℝ) ^ k) summable_geometric_two ?_
  filter_upwards [hev] with k hk
  have h0 : 0 ≤ c ^ k * Real.exp (-((k : ℝ) * (k + n - 2)) * t) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have h1 : c ^ k ≤ (c + 1) ^ k := pow_le_pow_left₀ hc (by linarith) k
  have h2 : Real.exp (-((k : ℝ) * (k + n - 2)) * t) ≤ Real.exp (-(t * k)) ^ k := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hk0 hk0, mul_nonneg (mul_nonneg hk0 hk0) ht.le,
      mul_nonneg (mul_nonneg hk0 (sub_nonneg.2 hn')) ht.le]
  calc c ^ k * Real.exp (-((k : ℝ) * (k + n - 2)) * t) ≤ (c + 1) ^ k * Real.exp (-(t * k)) ^ k :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = ((c + 1) * Real.exp (-(t * k))) ^ k := by rw [mul_pow]
    _ ≤ (1 / 2) ^ k := pow_le_pow_left₀ (by positivity) hk k

/-- bound of the restrictions of a harmonic homogeneous polynomial in the sup norm of `C(S, ℝ)`. -/
lemma norm_restrA_le (hn : 2 ≤ n) {k : ℕ} {p : Pn n} (hp : IsHarm k p) :
    ‖restrA p‖ ≤ Real.sqrt n ^ k * Real.sqrt (Nn n p) := by
  refine (ContinuousMap.norm_le _ (by positivity)).2 fun x => ?_
  rw [restrA_apply, Real.norm_eq_abs]
  have := harm_sup_abs hn hp (cv (x : Ee n))
  rw [nrm_cv_sph, one_mul] at this
  exact this

theorem sphereF8_pos (hn : 2 ≤ n) {t : ℝ≥0} (ht : 0 < t) (u : Lp ℝ 2 (σ n)) :
    (sphereDiffusion n hn).semigroup t u ∈ smoothCls n := by
  have hn1 : 1 ≤ n := Nat.one_le_of_lt hn
  have hprob := σ_isProbabilityMeasure hn1
  obtain ⟨a, haV, han, hsum⟩ := exists_expansion hn u
  have hex : ∀ k, ∃ h : Pn n, IsHarm k h ∧ Φ0 h = a k := fun k => by
    obtain ⟨h, hh, e⟩ := haV k
    exact ⟨h, hh, e⟩
  choose h hhar hΦ using hex
  set lam : ℕ → ℝ := fun k => Real.exp (-((k : ℝ) * (k + n - 2)) * (t : ℝ)) with hlam
  set H : ℕ → Pn n := fun k => lam k • h k with hH
  have hHharm : ∀ k, IsHarm k (H k) := fun k => (Hk n k).smul_mem (lam k) (hhar k)
  have hΦH : ∀ k, Φ0 (H k) = lam k • a k := fun k => by rw [hH]; simp [hΦ]
  have hNH : ∀ k, Real.sqrt (Nn n (H k)) ≤ lam k * ‖u‖ := fun k => by
    rw [← norm_Φ0_sq hn1, Real.sqrt_sq (norm_nonneg _), hΦH, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (han k) (Real.exp_pos _).le
  have hcls : HCls H := by
    refine ⟨hHharm, fun c hc => ?_⟩
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((summable_gauss hn (by exact_mod_cast ht) hc).mul_right ‖u‖)
    calc c ^ k * Real.sqrt (Nn n (H k)) ≤ c ^ k * (lam k * ‖u‖) :=
          mul_le_mul_of_nonneg_left (hNH k) (by positivity)
      _ = c ^ k * lam k * ‖u‖ := by ring
  -- the sum is smooth
  have hsm := contDiff_top_Fs hn hcls
  have hg := A₀S_of_contDiff hsm
  refine ⟨_, hg, ?_⟩
  -- `P_t u` is the `L²` limit of the terms
  have h1 : HasSum (fun k => (sphereDiffusion n hn).semigroup t (a k))
      ((sphereDiffusion n hn).semigroup t u) := hsum.mapL _
  have h2 : ∀ k, (sphereDiffusion n hn).semigroup t (a k) = Φ0 (H k) := fun k => by
    rw [hΦH, ← hΦ k, Φ0_eq_cls hn, sphere_semigroup_harm hn (hhar k)]
  simp only [h2] at h1
  -- uniform convergence on the sphere
  have hnorm : Summable fun k => ‖restrA (H k)‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_restrA_le hn (hHharm k)) (hcls.2 _ (Real.sqrt_nonneg _))
  have hS : HasSum (fun k => restrA (H k)) (∑' k, restrA (H k)) := hnorm.of_norm.hasSum
  have h3 := hS.mapL (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ)
  have h4 : (ContinuousMap.toLp (E := ℝ) 2 (σ n) ℝ) (∑' k, restrA (H k))
      = (sphereDiffusion n hn).semigroup t u := by
    refine h3.unique ?_
    simpa [Φ0_apply] using h1
  rw [← h4]
  filter_upwards [ContinuousMap.coeFn_toLp (E := ℝ) (p := 2) (μ := σ n) (𝕜 := ℝ) (∑' k, restrA (H k))]
    with x hx
  rw [hx, ← ContinuousMap.tsum_apply hnorm.of_norm]
  simp only [restrA_apply, Fs, restr, ev]

theorem sphereF8 (hn : 2 ≤ n) : SphereF8 n hn := by
  intro t f
  rcases eq_zero_or_pos t with h0 | hpos
  · subst h0
    exact sphereF8_zero hn f
  · exact sphereF8_pos hn hpos _

noncomputable def sphereFullU (hn : 2 ≤ n) : FullTriple (Sph n) := sphereFull hn (sphereF8 hn)

theorem sphereFullU_CD (hn : 2 ≤ n) : (sphereFullU hn).CD ((n : ℝ) - 2) ((n : ℝ≥0∞) - 1) :=
  sphereFull_CD hn (sphereF8 hn)

theorem sphereFullU_core2 (hn : 2 ≤ n) : (sphereFullU hn).Core2 :=
  sphereFull_core2 hn (sphereF8 hn)

end MarkovTriple.BGL.SphereN
