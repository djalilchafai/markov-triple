import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllipticFriedrichsEnergy

/-!
# `L²_loc ⇒ H¹_loc` for very weak solutions of divergence-form equations (R16, Friedrichs step)

Statements M1, M2 of `STATEMENTS_R16_Friedrichs.md`.  Textbook route (Friedrichs 1944; Gilbarg–Trudinger §7.2 and the proof
of Thm 8.8; Evans §6.3.1 Step 1): mollify `u_ε = ρ_ε ⋆ u`, uniform `H¹` bound for `ζ u_ε` from the equation for `u_ε` with the
Friedrichs commutator error (`EllipticFriedrichsEst`, `EllipticFriedrichsEnergy`), then weak sequential compactness in `L²`
and the localisation `weakDeriv_of_local` of `EllipticLocal.lean`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MarkovTriple.BGL.Instances.GibbsRd.Elliptic

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

/-- `N2 (c g) ≤ Z · N2 g` for a bounded measurable multiplier `c` -/
lemma N2_mul_le {c g : (Fin d → ℝ) → ℝ} {Z : ℝ} (hg : MemLp g 2 volume) (hc : ∀ x, ‖c x‖ ≤ Z)
    (hcm : AEStronglyMeasurable c volume) : N2 (fun x => c x * g x) ≤ Z * N2 g := by
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans (hc 0)
  have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (f := fun x => c x * g x) (g := g) (c := Z) (μ := volume)
    (hcm.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hc x) (norm_nonneg _)) 2
  unfold N2
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hg.eLpNorm_ne_top) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hZ0] at this

/-- **weak compactness criterion**: smooth `L²` approximants with `L²`-bounded `i`-th derivative give a weak derivative in
`L²` (the compactness half of Evans §5.8.2 Thm 3 (ii)). -/
theorem weakDeriv_of_approx {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 volume) (i : Fin d) {fn : ℕ → (Fin d → ℝ) → ℝ}
    (hfnS : ∀ n, Sm (fn n)) (hfnL : ∀ n, MemLp (fn n) 2 volume)
    (hconv : Tendsto (fun n => N2 (fun x => fn n x - f x)) atTop (𝓝 0)) {C : ℝ}
    (hb : ∀ n, MemLp (pderiv (fn n) i) 2 volume ∧ N2 (pderiv (fn n) i) ≤ C) :
    ∃ g : (Fin d → ℝ) → ℝ, MemLp g 2 volume ∧ WeakDeriv f g i := by
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  let G : ℕ → Lp ℝ 2 (volume : Measure (Fin d → ℝ)) := fun n => (hb n).1.toLp (pderiv (fn n) i)
  have hG : ∀ n, ‖G n‖ ≤ C := fun n => by
    simp only [G, Lp.norm_toLp]
    exact (hb n).2
  obtain ⟨g, φs, hφs, hweak⟩ := weak_subseq G C hG
  refine ⟨(g : (Fin d → ℝ) → ℝ), Lp.memLp g, (hf.locallyIntegrable (by norm_num)),
    (Lp.memLp g).locallyIntegrable (by norm_num), fun φ hφ hs => ?_⟩
  have hφS : Sm φ := hφ
  have hφm : MemLp φ 2 volume := hφS.continuous.memLp_of_hasCompactSupport hs
  have hdφm : MemLp (pderiv φ i) 2 volume :=
    (hφS.pderiv i).continuous.memLp_of_hasCompactSupport (hs.fderiv_apply ℝ (Pi.single i 1))
  have h1 : Tendsto (fun n => ∫ x, pderiv (fn (φs n)) i x * φ x) atTop (𝓝 (∫ x, (g : (Fin d → ℝ) → ℝ) x * φ x)) := by
    have := hweak (hφm.toLp φ)
    have e1 : ∀ n, inner ℝ (G (φs n)) (hφm.toLp φ) = ∫ x, pderiv (fn (φs n)) i x * φ x := fun n =>
      inner_toLp (hb (φs n)).1 hφm
    have e2 : inner ℝ g (hφm.toLp φ) = ∫ x, (g : (Fin d → ℝ) → ℝ) x * φ x := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hφm.coeFn_toLp] with x hx
      simp [hx, mul_comm]
    simpa [e1, e2] using this
  have h2 : Tendsto (fun n => ∫ x, pderiv φ i x * fn n x) atTop (𝓝 (∫ x, pderiv φ i x * f x)) :=
    tendsto_integral_mul hdφm hf hfnL hconv
  have h2' := h2.comp hφs.tendsto_atTop
  have h3 : ∀ n, ∫ x, pderiv φ i x * fn (φs n) x = -∫ x, pderiv (fn (φs n)) i x * φ x := fun n => by
    have := ibp_smooth (hfnS (φs n)) hφS hs i
    rw [← this]
    exact integral_congr_ae (Eventually.of_forall fun x => by ring)
  have h4 := tendsto_nhds_unique (by simpa only [Function.comp_def, h3] using h2') h1.neg
  show ∫ x, f x * pderiv φ i x = _
  have e : ∫ x, f x * pderiv φ i x = ∫ x, pderiv φ i x * f x :=
    integral_congr_ae (Eventually.of_forall fun x => by ring)
  rw [e]
  linarith


section
variable {b : Fin d → Fin d → (Fin d → ℝ) → ℝ} {u F : (Fin d → ℝ) → ℝ}

/-- **M1 (local form)**: for each cut-off `cut R`, `cut R · u` has a weak derivative `∂ᵢ` in `L²_loc`. -/
theorem cutoff_h1 (hb : ∀ i j, Sm (b i j)) (hsym : ∀ i j x, b i j x = b j i x)
    (hell : ∀ K : Set (Fin d → ℝ), IsCompact K → ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ K, ∀ ξ : Fin d → ℝ,
      lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, b i j x * ξ i * ξ j)
    (hu : LocL2 u) (hF : LocL2 F)
    (veq : ∀ a : (Fin d → ℝ) → ℝ, Sm a → HasCompactSupport a → ∫ x, u x * Pop b a x = ∫ x, F x * a x)
    {R : ℝ} (hR : 0 < R) (i : Fin d) :
    ∃ g : (Fin d → ℝ) → ℝ, LocL2 g ∧ WeakDeriv (fun x => cut R x * u x) g i := by
  set R₀ : ℝ := 2 * R with hR₀def
  have hR₀ : ∀ y : Fin d → ℝ, R₀ < ‖y‖ → cut R y = 0 := by
    intro y hy
    apply cut_eq_zero hR
    have h1 : ‖y‖ ≤ Real.sqrt (qd y) := by
      rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
      intro j
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => y j ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j))
    have h2 : R₀ < Real.sqrt (qd y) := lt_of_lt_of_le hy h1
    have h3 : R₀ ^ 2 < qd y := (Real.lt_sqrt (by positivity)).1 h2
    nlinarith
  set S : Set (Fin d → ℝ) := Metric.closedBall 0 (R₀ + 2) with hSdef
  have hS : IsCompact S := isCompact_closedBall _ _
  set ut := S.indicator u with hutdef
  set Ft := S.indicator F with hFtdef
  have hut : MemLp ut 2 volume := hu.memLp_indicator hS
  have hFt : MemLp Ft 2 volume := hF.memLp_indicator hS
  have hmemS : ∀ x : Fin d → ℝ, ‖x‖ ≤ R₀ + 1 → x ∈ S := fun x hx => by
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]; linarith
  have veq' : ∀ a : (Fin d → ℝ) → ℝ, Sm a → (∀ y, R₀ + 1 < ‖y‖ → a y = 0) →
      ∫ x, ut x * Pop b a x = ∫ x, Ft x * a x := by
    intro a ha ha0
    have hcs : HasCompactSupport a :=
      hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) (R₀ + 1)) fun y hy => ha0 y (by simpa using hy)
    have e1 : ∫ x, ut x * Pop b a x = ∫ x, u x * Pop b a x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : ‖x‖ ≤ R₀ + 1
      · simp [hutdef, Set.indicator_of_mem (hmemS x hx)]
      · simp [Pop_zero_off ha0 x (not_le.1 hx)]
    have e2 : ∫ x, Ft x * a x = ∫ x, F x * a x := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : ‖x‖ ≤ R₀ + 1
      · simp [hFtdef, Set.indicator_of_mem (hmemS x hx)]
      · simp [ha0 x (not_le.1 hx)]
    rw [e1, e2]
    exact veq a ha hcs
  obtain ⟨lam, hlam, hell'⟩ := hell (Metric.closedBall 0 R₀) (isCompact_closedBall _ _)
  obtain ⟨ρ, hρ⟩ := exists_frMollSeq d
  obtain ⟨C₁, hC₁, hker⟩ := hρ.ker
  obtain ⟨C, hC0, hCbd⟩ := energy_est hb hsym hlam hell' hC₁ (sm_cut R) hR₀
  have hv : ∀ n, Sm (moll (ρ n) ut) := fun n =>
    moll_contDiff (hρ.moll.smooth n) (hρ.moll.cs n) (hut.locallyIntegrable (by norm_num))
  set fn : ℕ → (Fin d → ℝ) → ℝ := fun n x => cut R x * moll (ρ n) ut x with hfn
  have hfnS : ∀ n, Sm (fn n) := fun n => (sm_cut R).mul (hv n)
  have hfn0 : ∀ n y, R₀ < ‖y‖ → fn n y = 0 := fun n y hy => by simp [hfn, hR₀ y hy]
  have hfnL : ∀ n, MemLp (fn n) 2 volume := fun n =>
    (hfnS n).continuous.memLp_of_hasCompactSupport (hcs_of_tsupport (isCompact_closedBall (0 : Fin d → ℝ) R₀)
      fun y hy => hfn0 n y (by simpa using hy))
  -- uniform bound on the `i`-th derivative
  have hb' : ∀ n, MemLp (pderiv (fn n) i) 2 volume ∧
      N2 (pderiv (fn n) i) ≤ Real.sqrt (C * ((∫ x, ut x ^ 2) + ∫ x, Ft x ^ 2)) := by
    intro n
    have hd0 : ∀ y, R₀ < ‖y‖ → pderiv (fn n) i y = 0 := fun y hy => pderiv_zero_off (hfn0 n) i y hy
    have hmem : MemLp (pderiv (fn n) i) 2 volume :=
      ((hfnS n).pderiv i).continuous.memLp_of_hasCompactSupport (hcs_of_tsupport
        (isCompact_closedBall (0 : Fin d → ℝ) R₀) fun y hy => hd0 y (by simpa using hy))
    refine ⟨hmem, ?_⟩
    have hbd := hCbd (ρ n) ut Ft (hker n) (hρ.even n) hut hFt veq'
    have i1 : Integrable (fun x => pderiv (fn n) i x ^ 2) :=
      int_of_zero_off (R := R₀) (((hfnS n).pderiv i).continuous.pow 2) fun y hy => by simp [hd0 y hy]
    have i2 : Integrable (fun x => ∑ j, pderiv (fn n) j x ^ 2) :=
      int_of_zero_off (R := R₀) (continuous_finsetSum _ fun j _ => ((hfnS n).pderiv j).continuous.pow 2)
        fun y hy => Finset.sum_eq_zero fun j _ => by simp [pderiv_zero_off (hfn0 n) j y hy]
    have h1 : ∫ x, pderiv (fn n) i x ^ 2 ≤ ∫ x, ∑ j, pderiv (fn n) j x ^ 2 :=
      integral_mono i1 i2 fun x => Finset.single_le_sum (f := fun j => pderiv (fn n) j x ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : N2 (pderiv (fn n) i) ^ 2 ≤ C * ((∫ x, ut x ^ 2) + ∫ x, Ft x ^ 2) := by
      rw [N2_sq hmem]
      simpa [sq] using h1.trans hbd
    exact (le_abs_self _).trans (Real.abs_le_sqrt h2)
  -- convergence
  set f : (Fin d → ℝ) → ℝ := fun x => cut R x * ut x with hf
  have hfL : MemLp f 2 volume := by
    refine hut.of_le_mul (c := 1) ((sm_cut R).continuous.aestronglyMeasurable.mul hut.aestronglyMeasurable)
      (Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_of_nonneg (cut_nonneg R x)]
    exact mul_le_mul_of_nonneg_right (by simpa using cut_le_one R x) (norm_nonneg _)
  have hmoll : ∀ n, MemLp (fun x => moll (ρ n) ut x - ut x) 2 volume := fun n =>
    (moll_memLp_norm_le (hρ.moll.smooth n) (hρ.moll.cs n) (hρ.moll.nonneg n) (hρ.moll.integral n) hut).1.sub hut
  have hconv : Tendsto (fun n => N2 (fun x => fn n x - f x)) atTop (𝓝 0) := by
    have h0 := moll_tendsto hρ.moll hut
    refine squeeze_zero (fun n => N2_nonneg _) (fun n => ?_) (by simpa using h0.const_mul 1)
    have := N2_mul_le (c := cut R) (Z := 1) (hmoll n)
      (fun x => by rw [Real.norm_of_nonneg (cut_nonneg R x)]; exact cut_le_one R x)
      (sm_cut R).continuous.aestronglyMeasurable
    have e : (fun x => fn n x - f x) = fun x => cut R x * (moll (ρ n) ut x - ut x) := by
      funext x; simp only [hfn, hf]; ring
    rw [e]; simpa using this
  obtain ⟨g, hgL, hwd⟩ := weakDeriv_of_approx hfL i hfnS hfnL hconv hb'
  refine ⟨g, fun K hK => hgL.restrict K, ?_⟩
  refine hwd.congr_ae (Eventually.of_forall fun x => ?_) (Filter.EventuallyEq.refl _ _)
  show cut R x * ut x = cut R x * u x
  by_cases hx : ‖x‖ ≤ R₀
  · simp [hutdef, Set.indicator_of_mem (hmemS x (by linarith))]
  · simp [hR₀ x (not_le.1 hx)]

/-- **M1**: very weak solutions of `Pop b u = F` with `u, F ∈ L²_loc` lie in `H¹_loc`
(Friedrichs 1944; see the file header). -/
theorem sobolev_one_of_veryWeak (hb : ∀ i j, Sm (b i j)) (hsym : ∀ i j x, b i j x = b j i x)
    (hell : ∀ K : Set (Fin d → ℝ), IsCompact K → ∃ lam : ℝ, 0 < lam ∧ ∀ x ∈ K, ∀ ξ : Fin d → ℝ,
      lam * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, b i j x * ξ i * ξ j)
    (hu : LocL2 u) (hF : LocL2 F)
    (veq : ∀ a : (Fin d → ℝ) → ℝ, Sm a → HasCompactSupport a → ∫ x, u x * Pop b a x = ∫ x, F x * a x) :
    Sobolev 1 u := by
  refine ⟨hu, fun i => ?_⟩
  obtain ⟨g, hg, hw⟩ := weakDeriv_of_local hu i
    (fun N => cutoff_h1 hb hsym hell hu hF veq (R := (N : ℝ) + 1) (by positivity) i)
  exact ⟨g, hw, hg⟩

end

end MarkovTriple.BGL.Instances.GibbsRd.Elliptic
