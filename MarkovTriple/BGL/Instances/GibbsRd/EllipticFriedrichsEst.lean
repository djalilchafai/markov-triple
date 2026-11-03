import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsComm

/-!
# The Friedrichs commutator estimate, uniform in the mollification parameter (R16, Friedrichs step)

Statement C2 of `STATEMENTS_R16_Friedrichs.md`: the commutator `ρ ⋆ Pop b φ − Pop b (ρ ⋆ φ)` is bounded in `L²` by
`C ‖∇φ‖₂` with `C` depending only on `b` on `closedBall 0 (R₀+1)`, on `R₀` and on `C₁ ≥ ∫ |∂ᵢρ(z)| ‖z‖ dz`, i.e. uniformly
along the scaled mollifier sequence (Friedrichs 1944, Lemma 1; the same mechanism as Gilbarg–Trudinger Lemma 7.? and
Evans §6.3 (difference-quotient version)).  Only the LOCAL Lipschitz constant of `b` on a compact ball enters.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- the properties of one mollifier used by the commutator estimate -/
structure FrKer (ρ : (Fin d → ℝ) → ℝ) (C₁ : ℝ) : Prop where
  sm : Sm ρ
  cs : HasCompactSupport ρ
  nonneg : ∀ x, 0 ≤ ρ x
  integral : ∫ x, ρ x = 1
  support : ∀ x, ρ x ≠ 0 → ‖x‖ < 1
  grad : ∀ i, ∫ z, |pderiv ρ i z| * ‖z‖ ≤ C₁

lemma IsFrMollSeq.ker {ρ : ℕ → (Fin d → ℝ) → ℝ} (h : IsFrMollSeq ρ) :
    ∃ C₁ : ℝ, 0 ≤ C₁ ∧ ∀ n, FrKer (ρ n) C₁ := by
  obtain ⟨C₁, hC₁, hg⟩ := h.grad
  refine ⟨C₁, hC₁, fun n => ⟨h.moll.smooth n, h.moll.cs n, h.moll.nonneg n, h.moll.integral n, fun x hx => ?_,
    fun i => hg n i⟩⟩
  have := h.moll.support n x hx
  refine this.trans_le ?_
  rw [div_le_one (by positivity)]; linarith [Nat.cast_nonneg (α := ℝ) n]

section
variable {b : Fin d → Fin d → (Fin d → ℝ) → ℝ} {ρ φ : (Fin d → ℝ) → ℝ} {C₁ : ℝ}

/-- local Lipschitz constant of the coefficients on a ball -/
lemma exists_lip (hb : ∀ i j, Sm (b i j)) (R₁ : ℝ) :
    ∃ Lb : ℝ, 0 ≤ Lb ∧ ∀ i j, ∀ x ∈ Metric.closedBall (0 : Fin d → ℝ) R₁, ‖fderiv ℝ (b i j) x‖ ≤ Lb := by
  have h : ∀ i j, ∃ C : ℝ, ∀ x ∈ Metric.closedBall (0 : Fin d → ℝ) R₁, ‖fderiv ℝ (b i j) x‖ ≤ C := fun i j =>
    (isCompact_closedBall (0 : Fin d → ℝ) R₁).exists_bound_of_continuousOn
      ((hb i j).continuous_fderiv (by simp)).continuousOn
  choose C hC using h
  refine ⟨∑ i, ∑ j, max (C i j) 0, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => le_max_right _ _,
    fun i j x hx => ?_⟩
  refine (hC i j x hx).trans ((le_max_left (C i j) 0).trans ?_)
  calc max (C i j) 0 ≤ ∑ j', max (C i j') 0 :=
        Finset.single_le_sum (f := fun j' => max (C i j') 0) (fun _ _ => le_max_right _ _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', max (C i' j') 0 :=
        Finset.single_le_sum (f := fun i' => ∑ j', max (C i' j') 0)
          (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ i)

lemma lip_of_bound {f : (Fin d → ℝ) → ℝ} (hf : Sm f) {R₁ L : ℝ}
    (hL : ∀ x ∈ Metric.closedBall (0 : Fin d → ℝ) R₁, ‖fderiv ℝ f x‖ ≤ L) {x y : Fin d → ℝ}
    (hx : ‖x‖ ≤ R₁) (hy : ‖y‖ ≤ R₁) : |f y - f x| ≤ L * ‖y - x‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := f) (s := Metric.closedBall 0 R₁)
    (fun z _ => hf.differentiableAt z) hL (convex_closedBall 0 R₁) (by simpa using hx) (by simpa using hy)
  simpa using this

lemma abs_pderiv_le {f : (Fin d → ℝ) → ℝ} {R₁ L : ℝ}
    (hL : ∀ x ∈ Metric.closedBall (0 : Fin d → ℝ) R₁, ‖fderiv ℝ f x‖ ≤ L) {x : Fin d → ℝ} (hx : ‖x‖ ≤ R₁)
    (i : Fin d) : |pderiv f i x| ≤ L := by
  unfold pderiv
  have h1 := (fderiv ℝ f x).le_opNorm (Pi.single i (1 : ℝ))
  have h2 : ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ ≤ 1 := norm_single_le i
  have h3 := hL x (by simpa using hx)
  rw [← Real.norm_eq_abs]
  calc ‖(fderiv ℝ f x) (Pi.single i 1)‖ ≤ ‖fderiv ℝ f x‖ * ‖(Pi.single i (1 : ℝ) : Fin d → ℝ)‖ := h1
    _ ≤ ‖fderiv ℝ f x‖ * 1 := by gcongr
    _ ≤ L := by linarith

/-- the derivative of a kernel supported in the unit ball is supported in the closed unit ball -/
lemma pderiv_ker_support (hk : FrKer ρ C₁) (i : Fin d) (z : Fin d → ℝ) (hz : pderiv ρ i z ≠ 0) : ‖z‖ ≤ 1 := by
  have h1 : fderiv ℝ ρ z ≠ 0 := fun h0 => hz (by simp [pderiv, h0])
  have h2 : z ∈ tsupport ρ := support_fderiv_subset ℝ h1
  have h3 : tsupport ρ ⊆ Metric.closedBall 0 1 := by
    refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
    simpa using (hk.support y hy).le
  simpa using h3 h2


/-- one `(i,j)` term of the commutator formula is bounded by a positive kernel applied to `|∂ⱼφ|` -/
theorem term_bound (hb : ∀ i j, Sm (b i j)) (hk : FrKer ρ C₁) (hφ : Sm φ) {R₀ Lb : ℝ} (hLb0 : 0 ≤ Lb)
    (hLb : ∀ i j, ∀ x ∈ Metric.closedBall (0 : Fin d → ℝ) (R₀ + 1), ‖fderiv ℝ (b i j) x‖ ≤ Lb)
    (hg0 : ∀ j y, R₀ < ‖y‖ → pderiv φ j y = 0) (i j : Fin d) (x : Fin d → ℝ) :
    |(∫ y, pderiv ρ i (x - y) * (b i j y * pderiv φ j y))
        - pderiv (b i j) i x * moll ρ (pderiv φ j) x
        - b i j x * ∫ y, pderiv ρ i (x - y) * pderiv φ j y|
      ≤ Lb * ∫ y, ((|pderiv ρ i (x - y)| * ‖x - y‖) + ρ (x - y)) * |pderiv φ j y| := by
  have hgS : Sm (pderiv φ j) := hφ.pderiv j
  have hgcs : HasCompactSupport (pderiv φ j) :=
    hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R₀) fun y hy => hg0 j y (by simpa using hy)
  have hDc : Continuous (pderiv ρ i) := (hk.sm.pderiv i).continuous
  have hbc : Continuous (b i j) := (hb i j).continuous
  have hgc : Continuous (pderiv φ j) := hgS.continuous
  have hgabs : HasCompactSupport (fun y => |pderiv φ j y|) :=
    hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R₀) fun y hy => by
      simp [hg0 j y (by simpa using hy)]
  have I1 := integrable_ker hDc (hbc.mul hgc) hgcs.mul_left x
  have I2 := integrable_ker hDc hgc hgcs x
  have Ik : Integrable (fun y => ((|pderiv ρ i (x - y)| * ‖x - y‖)) * |pderiv φ j y|) := by
    have hkc : Continuous (fun z => |pderiv ρ i z| * ‖z‖) := hDc.abs.mul continuous_norm
    exact integrable_ker hkc hgc.abs hgabs x
  have Iρ : Integrable (fun y => ρ (x - y) * |pderiv φ j y|) := integrable_ker hk.sm.continuous hgc.abs hgabs x
  -- combine the first and third terms
  have eq1 : (∫ y, pderiv ρ i (x - y) * (b i j y * pderiv φ j y)) - b i j x * ∫ y, pderiv ρ i (x - y) * pderiv φ j y
      = ∫ y, pderiv ρ i (x - y) * ((b i j y - b i j x) * pderiv φ j y) := by
    have I1' : Integrable (fun y => pderiv ρ i (x - y) * (b i j y * pderiv φ j y)) := I1
    rw [← integral_const_mul, ← integral_sub I1' (I2.const_mul (b i j x))]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  -- first bound
  have h1 : |∫ y, pderiv ρ i (x - y) * ((b i j y - b i j x) * pderiv φ j y)| ≤
      Lb * ∫ y, ((|pderiv ρ i (x - y)| * ‖x - y‖)) * |pderiv φ j y| := by
    rw [← integral_const_mul]
    have := norm_integral_le_of_norm_le (μ := (volume : Measure (Fin d → ℝ)))
      (f := fun y => pderiv ρ i (x - y) * ((b i j y - b i j x) * pderiv φ j y))
      (g := fun y => Lb * ((|pderiv ρ i (x - y)| * ‖x - y‖) * |pderiv φ j y|)) (Ik.const_mul _)
      (Eventually.of_forall fun y => ?_)
    · simpa using this
    · by_cases h0 : pderiv ρ i (x - y) = 0 ∨ pderiv φ j y = 0
      · rcases h0 with h0 | h0 <;> simp [h0]
      · push Not at h0
        have hxy := pderiv_ker_support hk i (x - y) h0.1
        have hy : ‖y‖ ≤ R₀ := by
          by_contra hlt; exact h0.2 (hg0 j y (not_le.1 hlt))
        have hx : ‖x‖ ≤ R₀ + 1 := by
          calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
            _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
            _ ≤ 1 + R₀ := add_le_add hxy hy
            _ = R₀ + 1 := by ring
        have hlip := lip_of_bound (hb i j) (hLb i j) hx (hy.trans (by linarith))
        rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
        rw [norm_sub_rev y x] at hlip
        calc |pderiv ρ i (x - y)| * (|b i j y - b i j x| * |pderiv φ j y|)
            ≤ |pderiv ρ i (x - y)| * ((Lb * ‖x - y‖) * |pderiv φ j y|) := by gcongr
          _ = Lb * (|pderiv ρ i (x - y)| * ‖x - y‖ * |pderiv φ j y|) := by ring
  -- second bound
  have h2 : |pderiv (b i j) i x * moll ρ (pderiv φ j) x| ≤ Lb * ∫ y, ρ (x - y) * |pderiv φ j y| := by
    have hnn : 0 ≤ ∫ y, ρ (x - y) * |pderiv φ j y| :=
      integral_nonneg fun y => mul_nonneg (hk.nonneg _) (abs_nonneg _)
    by_cases hx : ‖x‖ ≤ R₀ + 1
    · have hder := abs_pderiv_le (hLb i j) hx i
      rw [abs_mul]
      have : |moll ρ (pderiv φ j) x| ≤ ∫ y, ρ (x - y) * |pderiv φ j y| := by
        rw [moll_eq, ← Real.norm_eq_abs]
        refine norm_integral_le_of_norm_le Iρ (Eventually.of_forall fun y => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hk.nonneg _)]
      exact mul_le_mul hder this (abs_nonneg _) hLb0
    · have : moll ρ (pderiv φ j) x = 0 := by
        rw [moll_eq]
        refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
        by_cases h0 : ρ (x - y) = 0
        · simp [h0]
        · have h1 := hk.support _ h0
          have : pderiv φ j y = 0 := by
            apply hg0 j y
            by_contra hy
            push Not at hy
            apply hx
            calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
              _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
              _ ≤ R₀ + 1 := by linarith
          simp [this]
      rw [this]; simpa using mul_nonneg hLb0 hnn
  rw [sub_right_comm, eq1]
  calc _ ≤ |∫ y, pderiv ρ i (x - y) * ((b i j y - b i j x) * pderiv φ j y)| +
        |pderiv (b i j) i x * moll ρ (pderiv φ j) x| := abs_sub _ _
    _ ≤ (Lb * ∫ y, ((|pderiv ρ i (x - y)| * ‖x - y‖)) * |pderiv φ j y|) +
        Lb * ∫ y, ρ (x - y) * |pderiv φ j y| := add_le_add h1 h2
    _ = Lb * ∫ y, ((|pderiv ρ i (x - y)| * ‖x - y‖) + ρ (x - y)) * |pderiv φ j y| := by
        rw [← mul_add, ← integral_add Ik Iρ]
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun y => by ring)


/-- the commutator `ρ ⋆ Pop b φ − Pop b (ρ ⋆ φ)` -/
noncomputable def Tcomm (b : Fin d → Fin d → (Fin d → ℝ) → ℝ) (ρ φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  moll ρ (Pop b φ) x - Pop b (moll ρ φ) x

lemma sm_Tcomm (hb : ∀ i j, Sm (b i j)) (hρ : Sm ρ) (hρc : HasCompactSupport ρ) (hφ : Sm φ) : Sm (Tcomm b ρ φ) := by
  have h1 : Sm (Pop b φ) := sm_Pop hb hφ
  have h2 : Sm (moll ρ φ) := moll_contDiff hρ hρc hφ.continuous.locallyIntegrable
  exact (moll_contDiff hρ hρc h1.continuous.locallyIntegrable).sub (sm_Pop hb h2)

/-- **C2** (Friedrichs commutator estimate, uniform in `ρ`): see `STATEMENTS_R16_Friedrichs.md`. -/
theorem comm_bound (hb : ∀ i j, Sm (b i j)) (R₀ C₁ : ℝ) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ρ φ : (Fin d → ℝ) → ℝ, FrKer ρ C₁ → Sm φ → tsupport φ ⊆ Metric.closedBall 0 R₀ →
      Integrable (fun x => Tcomm b ρ φ x ^ 2) ∧
      ∫ x, Tcomm b ρ φ x ^ 2 ≤ C * ∫ x, ∑ j, pderiv φ j x ^ 2 := by
  obtain ⟨Lb, hLb0, hLb⟩ := exists_lip hb (R₀ + 1)
  set cbar : ℝ := Lb * d * (C₁ + 1) with hcbar
  have hcbar0 : 0 ≤ cbar := by positivity
  refine ⟨cbar ^ 2 * d, by positivity, fun ρ φ hk hφ hts => ?_⟩
  have hφc : HasCompactSupport φ :=
    IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin d → ℝ) R₀) (isClosed_tsupport φ) hts
  have hg0 : ∀ j y, R₀ < ‖y‖ → pderiv φ j y = 0 := fun j y hy => by
    by_contra hne
    have h1 : fderiv ℝ φ y ≠ 0 := fun h0 => hne (by simp [pderiv, h0])
    have := hts (support_fderiv_subset ℝ h1)
    simp at this; linarith
  have hgS : ∀ j, Sm (pderiv φ j) := fun j => hφ.pderiv j
  have hgcs : ∀ j, HasCompactSupport (pderiv φ j) := fun j =>
    hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R₀) fun y hy => hg0 j y (by simpa using hy)
  set G : (Fin d → ℝ) → ℝ := fun y => ∑ j, |pderiv φ j y| with hG
  have hGc : Continuous G := continuous_finsetSum _ fun j _ => (hgS j).continuous.abs
  have hGcs : HasCompactSupport G := hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R₀) fun y hy =>
    Finset.sum_eq_zero fun j _ => by simp [hg0 j y (by simpa using hy)]
  -- the kernel
  set kk : Fin d → (Fin d → ℝ) → ℝ := fun i z => |pderiv ρ i z| * ‖z‖ with hkk
  set κ : (Fin d → ℝ) → ℝ := fun z => Lb * ∑ i, (kk i z + ρ z) with hκ
  have hkkc : ∀ i, Continuous (kk i) := fun i => ((hk.sm.pderiv i).continuous).abs.mul continuous_norm
  have hkkcs : ∀ i, HasCompactSupport (kk i) := fun i =>
    hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) 1) fun z hz => by
      have : pderiv ρ i z = 0 := by
        by_contra hne; exact hz (by simpa using pderiv_ker_support hk i z hne)
      simp [hkk, this]
  have hκc : Continuous κ := continuous_const.mul (continuous_finsetSum _ fun i _ => (hkkc i).add hk.sm.continuous)
  have hκcs : HasCompactSupport κ := hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) 1) fun z hz => by
    have h1 : ∀ i, kk i z = 0 := fun i => by
      have := (hkkcs i); by_contra hne
      exact hz (by
        have hD : pderiv ρ i z ≠ 0 := fun h0 => hne (by simp [hkk, h0])
        simpa using pderiv_ker_support hk i z hD)
    have h2 : ρ z = 0 := by
      by_contra hne; exact hz (by simpa using (hk.support z hne).le)
    simp [hκ, h1, h2]
  have hκ0 : ∀ z, 0 ≤ κ z := fun z => mul_nonneg hLb0 (Finset.sum_nonneg fun i _ =>
    add_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _)) (hk.nonneg z))
  have hκi : Integrable κ := hκc.integrable_of_hasCompactSupport hκcs
  have hκint : ∫ z, κ z ≤ cbar := by
    have hi : ∀ i, Integrable (fun z => kk i z + ρ z) := fun i =>
      ((hkkc i).integrable_of_hasCompactSupport (hkkcs i)).add
        (hk.sm.continuous.integrable_of_hasCompactSupport hk.cs)
    have : ∫ z, κ z = Lb * ∑ i, ((∫ z, kk i z) + 1) := by
      simp only [hκ]
      rw [integral_const_mul, integral_finsetSum _ fun i _ => hi i]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_add ((hkkc i).integrable_of_hasCompactSupport (hkkcs i))
        (hk.sm.continuous.integrable_of_hasCompactSupport hk.cs), hk.integral]
    rw [this, hcbar]
    have : ∑ i : Fin d, ((∫ z, kk i z) + 1) ≤ ∑ i : Fin d, (C₁ + 1) :=
      Finset.sum_le_sum fun i _ => by have := hk.grad i; simp only [hkk]; linarith
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc Lb * ∑ i : Fin d, ((∫ z, kk i z) + 1) ≤ Lb * (d * (C₁ + 1)) := mul_le_mul_of_nonneg_left (by simpa using this) hLb0
      _ = Lb * d * (C₁ + 1) := by ring
  have hκint0 : 0 ≤ ∫ z, κ z := integral_nonneg hκ0
  -- pointwise bound for the commutator
  have hT : ∀ x, |Tcomm b ρ φ x| ≤ ∫ t, κ t * G (x - t) := by
    intro x
    have e0 : Tcomm b ρ φ x = _ := comm_formula hb hk.sm hk.cs hφ hφc x
    have hint : ∀ i j, Integrable (fun y => ((|pderiv ρ i (x - y)| * ‖x - y‖) + ρ (x - y)) * |pderiv φ j y|) := fun i j =>
      integrable_ker ((hkkc i).add hk.sm.continuous) (hgS j).continuous.abs
        (hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R₀) fun y hy => by
          simp [hg0 j y (by simpa using hy)]) x
    calc |Tcomm b ρ φ x| ≤ ∑ i, ∑ j, Lb * ∫ y, ((|pderiv ρ i (x - y)| * ‖x - y‖) + ρ (x - y)) * |pderiv φ j y| := by
          rw [e0]
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
          exact term_bound hb hk hφ hLb0 hLb hg0 i j x
      _ = ∫ y, κ (x - y) * G y := by
          have : ∀ y, κ (x - y) * G y =
              ∑ i, ∑ j, Lb * (((|pderiv ρ i (x - y)| * ‖x - y‖) + ρ (x - y)) * |pderiv φ j y|) := by
            intro y
            simp only [hκ, hG, hkk]
            rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
          simp_rw [this]
          rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => (hint i j).const_mul _]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_finsetSum _ fun j _ => (hint i j).const_mul _]
          exact Finset.sum_congr rfl fun j _ => (integral_const_mul _ _).symm
      _ = ∫ t, κ t * G (x - t) := by
          have := integral_sub_left_eq_self (μ := (volume : Measure (Fin d → ℝ))) (fun y => κ y * G (x - y)) x
          simp only [sub_sub_cancel] at this
          exact this
  obtain ⟨hI, hIeq⟩ := integral_conv_sq hκi hGc hGcs
  have hTc : Continuous (Tcomm b ρ φ) := (sm_Tcomm hb hk.sm hk.cs hφ).continuous
  have hdom : ∀ x, Tcomm b ρ φ x ^ 2 ≤ (∫ z, κ z) * ∫ t, κ t * G (x - t) ^ 2 := fun x =>
    calc Tcomm b ρ φ x ^ 2 ≤ (∫ t, κ t * G (x - t)) ^ 2 := sq_le_sq' (abs_le.1 (hT x)).1 (abs_le.1 (hT x)).2
      _ ≤ _ := conv_sq_le hκ0 hκi hGc hGcs x
  have hint : Integrable (fun x => Tcomm b ρ φ x ^ 2) := by
    refine (hI.const_mul (∫ z, κ z)).mono' (hTc.pow 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hdom x
  refine ⟨hint, ?_⟩
  -- the `L²` norm of `G`
  have hgsq : Continuous (fun x => ∑ j, pderiv φ j x ^ 2) := continuous_finsetSum _ fun j _ => (hgS j).continuous.pow 2
  have hgsqcs : HasCompactSupport (fun x => ∑ j, pderiv φ j x ^ 2) :=
    hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R₀) fun y hy =>
      Finset.sum_eq_zero fun j _ => by simp [hg0 j y (by simpa using hy)]
  have hGsq : Continuous (fun y => G y ^ 2) := hGc.pow 2
  have hGsqcs : HasCompactSupport (fun y => G y ^ 2) := hGcs.comp_left (g := fun z : ℝ => z ^ 2) (by simp)
  have hGle : ∫ y, G y ^ 2 ≤ d * ∫ x, ∑ j, pderiv φ j x ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono (hGsq.integrable_of_hasCompactSupport hGsqcs)
      ((hgsq.integrable_of_hasCompactSupport hgsqcs).const_mul _) fun y => ?_
    simp only [hG]
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := fun j => |pderiv φ j y|)
    simpa [sq_abs] using this
  calc ∫ x, Tcomm b ρ φ x ^ 2 ≤ ∫ x, (∫ z, κ z) * ∫ t, κ t * G (x - t) ^ 2 :=
        integral_mono hint (hI.const_mul _) hdom
    _ = (∫ z, κ z) * ((∫ z, κ z) * ∫ y, G y ^ 2) := by rw [integral_const_mul, hIeq]
    _ ≤ cbar * (cbar * (d * ∫ x, ∑ j, pderiv φ j x ^ 2)) := by
        have h0 : 0 ≤ ∫ y, G y ^ 2 := integral_nonneg fun y => sq_nonneg _
        have : (∫ z, κ z) * ∫ y, G y ^ 2 ≤ cbar * (d * ∫ x, ∑ j, pderiv φ j x ^ 2) :=
          mul_le_mul hκint hGle h0 hcbar0
        exact mul_le_mul hκint this (mul_nonneg hκint0 h0) hcbar0
    _ = cbar ^ 2 * d * ∫ x, ∑ j, pderiv φ j x ^ 2 := by ring

end

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
