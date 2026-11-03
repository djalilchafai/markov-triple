import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.Core2RdDefs
import MarkovTriple.BGL.Instances.GibbsRd.Convex
import MarkovTriple.BGL.Instances.GibbsRd.Bochner

/-!
# Uniform bounds for the radial cut-offs under `BddHess3` (R18, Stream A3, targets B0 `grad_growth`, B2)

Statements: `STATEMENTS_R18_Core2Rd.md`.  With `χ_n = cut (n+1)`: `χ_n, ∂χ_n, ∂²χ_n, Lχ_n, ∂(Lχ_n), L(Lχ_n)` are bounded
uniformly in `n` (`∇V` grows at most linearly) and vanish on `{|x|² < (n+1)²}` (`cut_bounds`, `cut_vanish`).
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- `s x = ∑ |xⱼ|` -/
noncomputable def l1 (x : Rd d) : ℝ := ∑ j, |x j|

lemma l1_nonneg (x : Rd d) : 0 ≤ l1 x := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma continuous_l1 : Continuous (l1 : Rd d → ℝ) := by
  unfold l1; fun_prop

lemma l1_smul (R : ℝ) (hR : 0 ≤ R) (x : Rd d) : l1 (R • x) = R * l1 x := by
  unfold l1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [abs_mul, abs_of_nonneg hR]

/-! ### (a) linear growth of `∇V` -/

theorem GibbsRdData.BddHess3.grad_growth {G : GibbsRdData d} (hb : G.BddHess3) :
    ∃ C : ℝ, ∀ (x : Rd d) (i : Fin d), |pderiv G.V i x| ≤ C * (1 + ∑ j, |x j|) := by
  obtain ⟨C2, hC2⟩ := hb.hess
  refine ⟨(∑ i, |pderiv G.V i 0|) + max C2 0, fun x i => ?_⟩
  set g := pderiv G.V i with hg
  have hgs : Sm g := G.smooth.pderiv i
  have hmv : ‖g ((1:ℝ) • x) - g ((0:ℝ) • x)‖ ≤ (max C2 0 * l1 x) * ‖(1 : ℝ) - 0‖ := by
    refine Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s : ℝ => g (s • x)) (f' := fun t => ∑ j, x j * pderiv g j (t • x))
      (s := Set.Icc (0 : ℝ) 1) (C := max C2 0 * l1 x)
      (fun t _ => (hasDerivAt_ray hgs x t).hasDerivWithinAt) (fun t _ => ?_)
      (convex_Icc 0 1) (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    rw [Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    unfold l1
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hC2 (t • x) i j).trans (le_max_left _ _)) (abs_nonneg _)
  simp only [one_smul, zero_smul, norm_one, Real.norm_eq_abs, sub_zero, mul_one] at hmv
  have h0 : |g 0| ≤ ∑ i, |pderiv G.V i 0| :=
    Finset.single_le_sum (f := fun i => |pderiv G.V i 0|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h1 : |g x| ≤ |g 0| + |g x - g 0| := by
    have := abs_add_le (g 0) (g x - g 0)
    simpa using this
  have hl : 0 ≤ l1 x := l1_nonneg x
  have hm : 0 ≤ max C2 0 := le_max_right _ _
  have hS : 0 ≤ ∑ i, |pderiv G.V i 0| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  show |g x| ≤ (∑ i, |pderiv G.V i 0| + max C2 0) * (1 + l1 x)
  nlinarith [mul_nonneg hS hl, mul_nonneg hm hl]


/-! ### (b) scaling -/

/-- `sc R m g (x) = R^{-m} g(R⁻¹ x)` -/
noncomputable def sc (R : ℝ) (m : ℕ) (g : Rd d → ℝ) : Rd d → ℝ := fun x => (R⁻¹) ^ m * g (R⁻¹ • x)

lemma sm_sc (R : ℝ) (m : ℕ) {g : Rd d → ℝ} (hg : Sm g) : Sm (sc R m g) :=
  contDiff_const.mul (hg.comp (contDiff_id.const_smul R⁻¹ :
    ContDiff ℝ (⊤ : ℕ∞) fun y : Rd d => R⁻¹ • y))

lemma pderiv_sc (R : ℝ) (m : ℕ) {g : Rd d → ℝ} (hg : Sm g) (i : Fin d) :
    pderiv (sc R m g) i = sc R (m + 1) (pderiv g i) := by
  funext x
  have h1 : HasFDerivAt (fun y : Rd d => R⁻¹ • y) (R⁻¹ • ContinuousLinearMap.id ℝ (Rd d)) x :=
    (hasDerivAt_id' (𝕜 := ℝ) (1 : ℝ) |> fun _ => (hasFDerivAt_id x).const_smul R⁻¹)
  have h2 := ((hg.hasFDerivAt' (R⁻¹ • x)).comp x h1).const_mul ((R⁻¹) ^ m)
  have e := h2.fderiv
  change fderiv ℝ (fun x => R⁻¹ ^ m * g (R⁻¹ • x)) x = _ at e
  unfold pderiv sc
  rw [e]
  simp [pow_succ]
  ring

/-- iterated partial derivative along a word -/
noncomputable def dw : List (Fin d) → (Rd d → ℝ) → (Rd d → ℝ)
  | [], f => f
  | i :: w, f => pderiv (dw w f) i

lemma sm_dw (w : List (Fin d)) {g : Rd d → ℝ} (hg : Sm g) : Sm (dw w g) := by
  induction w with
  | nil => exact hg
  | cons i w ih => exact ih.pderiv i

lemma dw_sc (R : ℝ) (w : List (Fin d)) (m : ℕ) {g : Rd d → ℝ} (hg : Sm g) :
    dw w (sc R m g) = sc R (m + w.length) (dw w g) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    show pderiv (dw w (sc R m g)) i = _
    rw [ih, pderiv_sc R _ (sm_dw w hg) i]
    show _ = sc R (m + (w.length + 1)) _
    rw [← add_assoc]; rfl

lemma cut_eq_sc {R : ℝ} (hR : 0 < R) : (cut R : Rd d → ℝ) = sc R 0 (cut 1) := by
  funext x
  simp only [sc, cut, pow_zero, one_mul, one_pow, div_one]
  congr 2
  unfold qd
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- weighted bound for the derivatives of the unit cut-off -/
lemma cut_one_bound (w : List (Fin d)) : ∃ B : ℝ, ∀ y : Rd d, (1 + l1 y) ^ 2 * |dw w (cut 1) y| ≤ B := by
  have hc : Sm (dw w (cut 1 : Rd d → ℝ)) := sm_dw w (sm_cut 1)
  have hs : HasCompactSupport (dw w (cut 1 : Rd d → ℝ)) := by
    induction w with
    | nil => exact hcs_cut one_pos
    | cons i w ih =>
      exact (ih (sm_dw w (sm_cut 1))).fderiv_apply ℝ (Pi.single i 1)
  have hf : Continuous (fun y : Rd d => (1 + l1 y) ^ 2 * dw w (cut 1) y) :=
    ((continuous_const.add continuous_l1).pow 2).mul hc.continuous
  have hfs : HasCompactSupport (fun y : Rd d => (1 + l1 y) ^ 2 * dw w (cut 1) y) := hs.mul_left
  obtain ⟨B, hB⟩ := hf.bounded_above_of_compact_support hfs
  refine ⟨B, fun y => ?_⟩
  have := hB y
  rwa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (1 + l1 y) ^ 2)] at this

/-- uniform weighted bound for all derivatives of `cut R` of order `≤ 4`. -/
lemma cut_deriv_bound : ∃ B : ℝ, 0 ≤ B ∧ ∀ (R : ℝ), 1 ≤ R → ∀ (w : List (Fin d)), w.length ≤ 4 →
    ∀ x : Rd d, (1 + l1 x / R) ^ 2 * |dw w (cut R) x| ≤ B / R ^ w.length := by
  choose B hB using fun w : List (Fin d) => cut_one_bound w
  obtain ⟨M, hM⟩ := ((List.finite_length_le (Fin d) 4).image B).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun R hR w hw x => ?_⟩
  have hR0 : 0 < R := by linarith
  have hMw : B w ≤ M := hM ⟨w, hw, rfl⟩
  rw [cut_eq_sc hR0, dw_sc R w 0 (sm_cut 1)]
  simp only [sc, zero_add]
  have hy := hB w (R⁻¹ • x)
  have e : l1 (R⁻¹ • x) = l1 x / R := by
    rw [l1_smul _ (inv_nonneg.2 hR0.le)]; field_simp
  rw [e] at hy
  have e2 : max M 0 / R ^ w.length = max M 0 * R⁻¹ ^ w.length := by
    rw [inv_pow, div_eq_mul_inv]
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < R⁻¹ ^ w.length), e2]
  calc (1 + l1 x / R) ^ 2 * (R⁻¹ ^ w.length * |dw w (cut 1) (R⁻¹ • x)|)
      = R⁻¹ ^ w.length * ((1 + l1 x / R) ^ 2 * |dw w (cut 1) (R⁻¹ • x)|) := by ring
    _ ≤ R⁻¹ ^ w.length * max M 0 := by
        apply mul_le_mul_of_nonneg_left (hy.trans (hMw.trans (le_max_left _ _))) (by positivity)
    _ = max M 0 * R⁻¹ ^ w.length := by ring


/-! ### (c) vanishing inside, uniform bounds outside -/

lemma pderiv_eq_zero_of_open {f : Rd d → ℝ} {U : Set (Rd d)} (hU : IsOpen U) {c : ℝ}
    (h : ∀ y ∈ U, f y = c) {x : Rd d} (hx : x ∈ U) (i : Fin d) : pderiv f i x = 0 := by
  have hev : f =ᶠ[𝓝 x] fun _ => c := Filter.mem_of_superset (hU.mem_nhds hx) fun y hy => h y hy
  unfold pderiv
  rw [hev.fderiv_eq]
  simp

lemma isOpen_inner (R : ℝ) : IsOpen {x : Rd d | qd x < R ^ 2} :=
  isOpen_lt sm_qd.continuous continuous_const

/-- **B2 (vanishing)**: all the cut-off quantities vanish on `{|x|² < (n+1)²}`. -/
theorem cut_vanish (G : GibbsRdData d) (n : ℕ) {x : Rd d} (hx : qd x < ((n : ℝ) + 1) ^ 2) (i j : Fin d) :
    pderiv (cut ((n : ℝ) + 1)) i x = 0 ∧ pderiv (pderiv (cut ((n : ℝ) + 1)) i) j x = 0 ∧
    Lr G.V (cut ((n : ℝ) + 1)) x = 0 ∧ pderiv (Lr G.V (cut ((n : ℝ) + 1))) i x = 0 ∧
    Lr G.V (Lr G.V (cut ((n : ℝ) + 1))) x = 0 := by
  set R : ℝ := (n : ℝ) + 1 with hR
  have hR0 : 0 < R := by positivity
  have hU := isOpen_inner (d := d) R
  have h0 : ∀ y ∈ {x : Rd d | qd x < R ^ 2}, cut R y = 1 := fun y hy => cut_eq_one hR0 (le_of_lt hy)
  have h1 : ∀ y ∈ {x : Rd d | qd x < R ^ 2}, ∀ i, pderiv (cut R) i y = 0 := fun y hy i =>
    pderiv_eq_zero_of_open hU h0 hy i
  have h2 : ∀ y ∈ {x : Rd d | qd x < R ^ 2}, ∀ i j, pderiv (pderiv (cut R) i) j y = 0 := fun y hy i j =>
    pderiv_eq_zero_of_open hU (h1 · · i) hy j
  have hP : ∀ y ∈ {x : Rd d | qd x < R ^ 2}, Lr G.V (cut R) y = 0 := fun y hy => by
    simp [Lr, h1 y hy, h2 y hy]
  have hP1 : ∀ y ∈ {x : Rd d | qd x < R ^ 2}, ∀ i, pderiv (Lr G.V (cut R)) i y = 0 := fun y hy i =>
    pderiv_eq_zero_of_open hU hP hy i
  have hP2 : ∀ y ∈ {x : Rd d | qd x < R ^ 2}, ∀ i j, pderiv (pderiv (Lr G.V (cut R)) i) j y = 0 :=
    fun y hy i j => pderiv_eq_zero_of_open hU (hP1 · · i) hy j
  have hx' : x ∈ {x : Rd d | qd x < R ^ 2} := hx
  refine ⟨h1 x hx' i, h2 x hx' i j, hP x hx', hP1 x hx' i, ?_⟩
  simp [Lr, hP1 x hx', hP2 x hx']

/-- second derivative of `L f` -/
lemma pderiv_pderiv_Lr (G : GibbsRdData d) {f : Rd d → ℝ} (hf : Sm f) (k i : Fin d) (x : Rd d) :
    pderiv (pderiv (Lr G.V f) k) i x = ∑ j, (pderiv (pderiv (pderiv (pderiv f j) j) k) i x -
      ((pderiv (pderiv (pderiv G.V j) k) i x * pderiv f j x +
          pderiv (pderiv G.V j) k x * pderiv (pderiv f j) i x) +
        (pderiv (pderiv G.V j) i x * pderiv (pderiv f j) k x +
          pderiv G.V j x * pderiv (pderiv (pderiv f j) k) i x))) := by
  have hfun : pderiv (Lr G.V f) k = fun y => ∑ j, (pderiv (pderiv (pderiv f j) j) k y -
      (pderiv (pderiv G.V j) k y * pderiv f j y + pderiv G.V j y * pderiv (pderiv f j) k y)) :=
    funext fun y => G.pderiv_Lr hf k y
  have hV := G.smooth
  have s1 : ∀ j, Sm (pderiv (pderiv (pderiv f j) j) k) := fun j => ((hf.pderiv j).pderiv j).pderiv k
  have s2 : ∀ j, Sm (fun y => pderiv (pderiv G.V j) k y * pderiv f j y) := fun j =>
    ((hV.pderiv j).pderiv k).mul (hf.pderiv j)
  have s3 : ∀ j, Sm (fun y => pderiv G.V j y * pderiv (pderiv f j) k y) := fun j =>
    (hV.pderiv j).mul ((hf.pderiv j).pderiv k)
  rw [hfun, pderiv_sum _ (fun j => (s1 j).sub (((s2 j).add (s3 j)))) i x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pderiv_sub' (s1 j) ((s2 j).add (s3 j)) i x, pderiv_add' (s2 j) (s3 j) i x,
    pderiv_mul' ((hV.pderiv j).pderiv k) (hf.pderiv j) i x,
    pderiv_mul' (hV.pderiv j) ((hf.pderiv j).pderiv k) i x]

lemma abs_sum_le' {f : Fin d → ℝ} {M : ℝ} (h : ∀ j, |f j| ≤ M) : |∑ j, f j| ≤ d * M := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have := Finset.sum_le_card_nsmul Finset.univ (fun j => |f j|) M (fun j _ => h j)
  simpa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using this

lemma abs_mul_le' {a b α β : ℝ} (ha : |a| ≤ α) (hb : |b| ≤ β) : |a * b| ≤ α * β := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

lemma F1_aux {R a D B C1 w1 : ℝ} {m : ℕ} (hR : 1 ≤ R) (hm : 1 ≤ m) (hw : 1 ≤ w1) (hC : 0 ≤ C1)
    (hD0 : 0 ≤ D) (ha : a ≤ C1 * R * w1) (hD : w1 ^ 2 * D ≤ B / R ^ m) :
    a * D ≤ C1 * B := by
  have hRm : R ≤ R ^ m := le_self_pow₀ hR (by omega)
  have hRm0 : 0 < R ^ m := by positivity
  have h1 : w1 * D ≤ w1 ^ 2 * D := by
    have := mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ w1) hD0) (sub_nonneg.2 hw)
    nlinarith
  have h2 : R ^ m * (w1 * D) ≤ B := by
    have := (le_div_iff₀ hRm0).1 (h1.trans hD)
    linarith
  calc a * D ≤ C1 * R * w1 * D := mul_le_mul_of_nonneg_right ha hD0
    _ = C1 * (R * (w1 * D)) := by ring
    _ ≤ C1 * (R ^ m * (w1 * D)) := by
        apply mul_le_mul_of_nonneg_left _ hC
        exact mul_le_mul_of_nonneg_right hRm (by positivity)
    _ ≤ C1 * B := mul_le_mul_of_nonneg_left h2 hC

lemma F2_aux {R a b D B C1 w1 : ℝ} {m : ℕ} (hR : 1 ≤ R) (hm : 2 ≤ m) (hw : 1 ≤ w1) (hC : 0 ≤ C1)
    (hD0 : 0 ≤ D) (ha : a ≤ C1 * R * w1) (hb : b ≤ C1 * R * w1) (hb0 : 0 ≤ b)
    (hD : w1 ^ 2 * D ≤ B / R ^ m) : a * b * D ≤ C1 ^ 2 * B := by
  have hRm : R ^ 2 ≤ R ^ m := pow_le_pow_right₀ hR hm
  have hRm0 : 0 < R ^ m := by positivity
  have h2 : R ^ m * (w1 ^ 2 * D) ≤ B := by
    have := (le_div_iff₀ hRm0).1 hD
    linarith
  have hab : a * b ≤ (C1 * R * w1) * (C1 * R * w1) := mul_le_mul ha hb hb0 (by positivity)
  calc a * b * D ≤ (C1 * R * w1) * (C1 * R * w1) * D := mul_le_mul_of_nonneg_right hab hD0
    _ = C1 ^ 2 * (R ^ 2 * (w1 ^ 2 * D)) := by ring
    _ ≤ C1 ^ 2 * (R ^ m * (w1 ^ 2 * D)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hRm (by positivity)
    _ ≤ C1 ^ 2 * B := mul_le_mul_of_nonneg_left h2 (by positivity)


lemma T_ge {C1 C2 C3 B : ℝ} (h1 : 0 ≤ C1) (h2 : 0 ≤ C2) (h3 : 0 ≤ C3) (hB : 0 ≤ B) :
    B ≤ (1 + C1 + C2 + C3 + C1 * C2 + C1 ^ 2) * B ∧ C1 * B ≤ (1 + C1 + C2 + C3 + C1 * C2 + C1 ^ 2) * B ∧
    C2 * B ≤ (1 + C1 + C2 + C3 + C1 * C2 + C1 ^ 2) * B ∧ C3 * B ≤ (1 + C1 + C2 + C3 + C1 * C2 + C1 ^ 2) * B ∧
    C2 * (C1 * B) ≤ (1 + C1 + C2 + C3 + C1 * C2 + C1 ^ 2) * B ∧
    C1 ^ 2 * B ≤ (1 + C1 + C2 + C3 + C1 * C2 + C1 ^ 2) * B := by
  have p1 := mul_nonneg h1 hB
  have p2 := mul_nonneg h2 hB
  have p3 := mul_nonneg h3 hB
  have p4 := mul_nonneg (mul_nonneg h1 h2) hB
  have p5 := mul_nonneg (sq_nonneg C1) hB
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

lemma core2rd_final_arith (d T : ℝ) (hd : d ≤ d ^ 2) (hT0 : 0 ≤ T) :
    d * (2 * T) ≤ T * (1 + 8 * d ^ 2) ∧ d * (3 * T) ≤ T * (1 + 8 * d ^ 2) ∧
    d * (d * (5 * T) + d * (3 * T)) ≤ T * (1 + 8 * d ^ 2) ∧
    T ≤ T * (1 + 8 * d ^ 2) := by
  have h1 := mul_le_mul_of_nonneg_right hd hT0
  have h2 := mul_nonneg hT0 (sq_nonneg d)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- **B2 (bounds), real-scale form**: for `R ≥ 1`. -/
theorem cut_bounds_real (G : GibbsRdData d) (hb : G.BddHess3) :
    ∃ K : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ (x : Rd d) (i j : Fin d),
      |cut R x| ≤ 1 ∧ |pderiv (cut R) i x| ≤ K ∧ |pderiv (pderiv (cut R) i) j x| ≤ K ∧
      |Lr G.V (cut R) x| ≤ K ∧ |pderiv (Lr G.V (cut R)) i x| ≤ K ∧ |Lr G.V (Lr G.V (cut R)) x| ≤ K := by
  obtain ⟨C1', hC1'⟩ := hb.grad_growth
  obtain ⟨C2', hC2'⟩ := hb.hess
  obtain ⟨C3', hC3'⟩ := hb.third
  obtain ⟨B, hB0, hB⟩ := cut_deriv_bound (d := d)
  set C1 : ℝ := max C1' 0 with hC1
  set C2 : ℝ := max C2' 0 with hC2
  set C3 : ℝ := max C3' 0 with hC3
  have hC10 : 0 ≤ C1 := le_max_right _ _
  have hC20 : 0 ≤ C2 := le_max_right _ _
  have hC30 : 0 ≤ C3 := le_max_right _ _
  set T : ℝ := (1 + C1 + C2 + C3 + C1 * C2 + C1 ^ 2) * B with hT
  have hT0 : 0 ≤ T := by positivity
  obtain ⟨tB, tC1, tC2, tC3, tC21, tC11⟩ := T_ge hC10 hC20 hC30 hB0
  rw [← hT] at tB tC1 tC2 tC3 tC21 tC11
  clear_value T
  clear hT
  have hd : (d : ℝ) ≤ (d : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with h | h
    · simp [h]
    · have : (1 : ℝ) ≤ d := by exact_mod_cast h
      nlinarith
  refine ⟨T * (1 + 8 * (d : ℝ) ^ 2), fun R hR x i j => ?_⟩
  have hR0 : 0 < R := by linarith
  have hl := l1_nonneg x
  have hw1 : 1 ≤ 1 + l1 x / R := by
    have : 0 ≤ l1 x / R := by positivity
    linarith
  have hgrow : ∀ i, |pderiv G.V i x| ≤ C1 * R * (1 + l1 x / R) := by
    intro i
    have h1 := hC1' x i
    have e : C1 * R * (1 + l1 x / R) = C1 * (R + l1 x) := by field_simp
    have h2 : C1' * (1 + ∑ j, |x j|) ≤ C1 * (1 + l1 x) := by
      unfold l1
      exact mul_le_mul (le_max_left _ _) le_rfl (by positivity) hC10
    have h3 : C1 * (1 + l1 x) ≤ C1 * (R + l1 x) := mul_le_mul_of_nonneg_left (by linarith) hC10
    linarith
  have hDw : ∀ w : List (Fin d), w.length ≤ 4 →
      (1 + l1 x / R) ^ 2 * |dw w (cut R) x| ≤ B / R ^ w.length := fun w hw => hB R hR w hw x
  have A0 : ∀ w : List (Fin d), w.length ≤ 4 → |dw w (cut R) x| ≤ B := by
    intro w hw
    have h1 := hDw w hw
    have h2 : |dw w (cut R) x| ≤ (1 + l1 x / R) ^ 2 * |dw w (cut R) x| := by
      have : (1 : ℝ) ≤ (1 + l1 x / R) ^ 2 := one_le_pow₀ hw1
      nlinarith [abs_nonneg (dw w (cut R) x)]
    exact h2.trans (h1.trans (div_le_self hB0 (one_le_pow₀ hR)))
  have A1 : ∀ w : List (Fin d), 1 ≤ w.length → w.length ≤ 4 → ∀ k,
      |pderiv G.V k x * dw w (cut R) x| ≤ C1 * B := by
    intro w hw1' hw4 k
    rw [abs_mul]
    exact F1_aux hR hw1' hw1 hC10 (abs_nonneg _) (hgrow k) (hDw w hw4)
  have A2 : ∀ w : List (Fin d), 2 ≤ w.length → w.length ≤ 4 → ∀ k l,
      |pderiv G.V k x * pderiv G.V l x * dw w (cut R) x| ≤ C1 ^ 2 * B := by
    intro w hw2 hw4 k l
    rw [abs_mul, abs_mul]
    exact F2_aux hR hw2 hw1 hC10 (abs_nonneg _) (hgrow k) (hgrow l) (abs_nonneg _) (hDw w hw4)
  have hV2 : ∀ a b, |pderiv (pderiv G.V a) b x| ≤ C2 := fun a b => (hC2' x a b).trans (le_max_left _ _)
  have hV3 : ∀ a b c, |pderiv (pderiv (pderiv G.V a) b) c x| ≤ C3 := fun a b c =>
    (hC3' x a b c).trans (le_max_left _ _)
  have n1 : 0 ≤ C1 * B := by positivity
  have n2 : 0 ≤ C2 * B := by positivity
  have n3 : 0 ≤ C3 * B := by positivity
  have n4 : 0 ≤ C1 * C2 * B := by positivity
  have n5 : 0 ≤ C1 ^ 2 * B := by positivity
  -- atoms, all bounded by `T`
  have a0 : ∀ w : List (Fin d), w.length ≤ 4 → |dw w (cut R) x| ≤ T := fun w hw =>
    (A0 w hw).trans tB
  have a1 : ∀ w : List (Fin d), 1 ≤ w.length → w.length ≤ 4 → ∀ k,
      |pderiv G.V k x * dw w (cut R) x| ≤ T := fun w h1 h4 k =>
    (A1 w h1 h4 k).trans tC1
  have a2 : ∀ w : List (Fin d), 2 ≤ w.length → w.length ≤ 4 → ∀ k l,
      |pderiv G.V k x * pderiv G.V l x * dw w (cut R) x| ≤ T := fun w h1 h4 k l =>
    (A2 w h1 h4 k l).trans tC11
  have b2 : ∀ (a b : Fin d) (w : List (Fin d)), w.length ≤ 4 →
      |pderiv (pderiv G.V a) b x * dw w (cut R) x| ≤ T := fun a b w hw =>
    (abs_mul_le' (hV2 a b) (A0 w hw)).trans tC2
  have b3 : ∀ (a b c : Fin d) (w : List (Fin d)), w.length ≤ 4 →
      |pderiv (pderiv (pderiv G.V a) b) c x * dw w (cut R) x| ≤ T := fun a b c w hw =>
    (abs_mul_le' (hV3 a b c) (A0 w hw)).trans tC3
  have b21 : ∀ (a b k : Fin d) (w : List (Fin d)), 1 ≤ w.length → w.length ≤ 4 →
      |pderiv G.V k x * (pderiv (pderiv G.V a) b x * dw w (cut R) x)| ≤ T := by
    intro a b k w h1 h4
    have e : pderiv G.V k x * (pderiv (pderiv G.V a) b x * dw w (cut R) x) =
        pderiv (pderiv G.V a) b x * (pderiv G.V k x * dw w (cut R) x) := by ring
    rw [e]
    exact (abs_mul_le' (hV2 a b) (A1 w h1 h4 k)).trans tC21
  -- first-order data
  have hχ0 : |cut R x| ≤ 1 := by
    rw [abs_of_nonneg (cut_nonneg R x)]; exact cut_le_one R x
  have hχ1 : |pderiv (cut R) i x| ≤ T := a0 [i] (by simp)
  have hχ2 : |pderiv (pderiv (cut R) i) j x| ≤ T := a0 [j, i] (by simp)
  have hχs := sm_cut (d := d) R
  -- `P = L χ`
  have hP : |Lr G.V (cut R) x| ≤ d * (2 * T) := by
    unfold Lr
    refine abs_sum_le' fun k => ?_
    have h1 : |pderiv (pderiv (cut R) k) k x| ≤ T := a0 [k, k] (by simp)
    have h2 : |pderiv G.V k x * pderiv (cut R) k x| ≤ T := a1 [k] (by simp) (by simp) k
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  -- `∂ₖ P`
  have hPk : ∀ k, |pderiv (Lr G.V (cut R)) k x| ≤ d * (3 * T) := by
    intro k
    rw [G.pderiv_Lr hχs k x]
    refine abs_sum_le' fun l => ?_
    have h1 : |pderiv (pderiv (pderiv (cut R) l) l) k x| ≤ T := a0 [k, l, l] (by simp)
    have h2 : |pderiv (pderiv G.V l) k x * pderiv (cut R) l x| ≤ T := b2 l k [l] (by simp)
    have h3 : |pderiv G.V l x * pderiv (pderiv (cut R) l) k x| ≤ T := a1 [k, l] (by simp) (by simp) l
    rw [abs_le] at h1 h2 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  -- `∂ₖ∂ₖ P`
  have hPkk : ∀ k, |pderiv (pderiv (Lr G.V (cut R)) k) k x| ≤ d * (5 * T) := by
    intro k
    rw [pderiv_pderiv_Lr G hχs k k x]
    refine abs_sum_le' fun l => ?_
    have h1 : |pderiv (pderiv (pderiv (pderiv (cut R) l) l) k) k x| ≤ T := a0 [k, k, l, l] (by simp)
    have h2 : |pderiv (pderiv (pderiv G.V l) k) k x * pderiv (cut R) l x| ≤ T := b3 l k k [l] (by simp)
    have h3 : |pderiv (pderiv G.V l) k x * pderiv (pderiv (cut R) l) k x| ≤ T := b2 l k [k, l] (by simp)
    have h4 : |pderiv G.V l x * pderiv (pderiv (pderiv (cut R) l) k) k x| ≤ T :=
      a1 [k, k, l] (by simp) (by simp) l
    rw [abs_le] at h1 h2 h3 h4 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  -- `V_k ∂ₖ P`
  have hVPk : ∀ k, |pderiv G.V k x * pderiv (Lr G.V (cut R)) k x| ≤ d * (3 * T) := by
    intro k
    rw [G.pderiv_Lr hχs k x, Finset.mul_sum]
    refine abs_sum_le' fun l => ?_
    have h1 : |pderiv G.V k x * pderiv (pderiv (pderiv (cut R) l) l) k x| ≤ T :=
      a1 [k, l, l] (by simp) (by simp) k
    have h2 : |pderiv G.V k x * (pderiv (pderiv G.V l) k x * pderiv (cut R) l x)| ≤ T :=
      b21 l k k [l] (by simp) (by simp)
    have h3 : |pderiv G.V k x * pderiv G.V l x * pderiv (pderiv (cut R) l) k x| ≤ T :=
      a2 [k, l] (by simp) (by simp) k l
    have e : pderiv G.V k x * (pderiv (pderiv (pderiv (cut R) l) l) k x -
        (pderiv (pderiv G.V l) k x * pderiv (cut R) l x +
          pderiv G.V l x * pderiv (pderiv (cut R) l) k x)) =
        pderiv G.V k x * pderiv (pderiv (pderiv (cut R) l) l) k x -
        (pderiv G.V k x * (pderiv (pderiv G.V l) k x * pderiv (cut R) l x) +
          pderiv G.V k x * pderiv G.V l x * pderiv (pderiv (cut R) l) k x) := by ring
    rw [e]
    rw [abs_le] at h1 h2 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]
  have hLP : |Lr G.V (Lr G.V (cut R)) x| ≤ d * (d * (5 * T) + d * (3 * T)) := by
    unfold Lr
    have := abs_sum_le' (f := fun k => pderiv (pderiv (Lr G.V (cut R)) k) k x -
      pderiv G.V k x * pderiv (Lr G.V (cut R)) k x) (M := d * (5 * T) + d * (3 * T)) (fun k => by
        have h1 := hPkk k
        have h2 := hVPk k
        rw [abs_le] at h1 h2 ⊢
        constructor <;> linarith [h1.1, h1.2, h2.1, h2.2])
    exact this
  obtain ⟨f1, f2, f4, f5⟩ := core2rd_final_arith (d : ℝ) T hd hT0
  refine ⟨hχ0, hχ1.trans f5, hχ2.trans f5, hP.trans f1, (hPk i).trans f2, hLP.trans f4⟩

/-- **B2 (bounds)**: uniform in `n`. -/
theorem cut_bounds (G : GibbsRdData d) (hb : G.BddHess3) :
    ∃ K : ℝ, ∀ (n : ℕ) (x : Rd d) (i j : Fin d),
      |cut ((n : ℝ) + 1) x| ≤ 1 ∧ |pderiv (cut ((n : ℝ) + 1)) i x| ≤ K ∧
      |pderiv (pderiv (cut ((n : ℝ) + 1)) i) j x| ≤ K ∧ |Lr G.V (cut ((n : ℝ) + 1)) x| ≤ K ∧
      |pderiv (Lr G.V (cut ((n : ℝ) + 1))) i x| ≤ K ∧
      |Lr G.V (Lr G.V (cut ((n : ℝ) + 1))) x| ≤ K := by
  obtain ⟨K, hK⟩ := cut_bounds_real G hb
  exact ⟨K, fun n x i j => hK _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) x i j⟩

end MarkovTriple.BGL.Instances.GibbsRd
