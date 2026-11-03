import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.EllCalc

/-!
# Caccioppoli (energy) identity and inequality with a smooth cut-off — smooth solutions (R16, elliptic half)

Evans PDE §6.3.1 Thm 1, Step 1 (`∫ ζ²|Du|² ≤ C ∫ (f² + u²)`), Gilbarg–Trudinger (8.28)–(8.30), for the operator
`L = w⁻¹ div(w a ∇ ·)` of `EllData d` and `Γ(f,g) = Σ aᵢⱼ ∂ᵢf ∂ⱼg`.

**Scope (honest)**: here `u` is `C^∞` (not merely `H¹_loc`).  The version for weak `H¹_loc` solutions needs the density of
`C_c^∞` in `H¹_c` (mollifiers), which is NOT in Mathlib and not proved in this development.

* `caccioppoli_identity`: `∫ w Γ(ζu,ζu) = − ∫ w ζ² u Lu + ∫ w u² Γ(ζ,ζ)`;
* `caccioppoli`: `∫ w ζ² Γ(u,u) ≤ − 2 ∫ w ζ² u Lu + 4 ∫ w u² Γ(ζ,ζ)`.
-/

open MeasureTheory Filter Topology

namespace MarkovTriple.BGL.Instances.GibbsRd

open MarkovTriple.BGL (pderiv)

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- derivation property of `Γ` in the left slot -/
lemma Γ_mul_left {f g k : Rd d → ℝ} (hf : Sm f) (hg : Sm g) (x : Rd d) :
    E.Γ (f * g) k x = f x * E.Γ g k x + g x * E.Γ f k x := by
  unfold Γ
  have h : ∀ j, pderiv (f * g) j x = pderiv f j x * g x + f x * pderiv g j x := fun j => pderiv_mul hf hg j x
  simp only [h, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- pointwise expansion of `Γ(ζu, ζu)` -/
lemma Γ_prod_self {ζ u : Rd d → ℝ} (hζ : Sm ζ) (hu : Sm u) (x : Rd d) :
    E.Γ (ζ * u) (ζ * u) x = ζ x ^ 2 * E.Γ u u x + 2 * ζ x * u x * E.Γ ζ u x + u x ^ 2 * E.Γ ζ ζ x := by
  rw [E.Γ_mul_left hζ hu, E.Γ_symm ζ (ζ * u), E.Γ_symm u (ζ * u), E.Γ_mul_left hζ hu x,
    E.Γ_mul_left hζ hu x, E.Γ_symm u ζ]
  ring

/-- pointwise expansion of `Γ(ζ²u, u)` -/
lemma Γ_sq_mul {ζ u : Rd d → ℝ} (hζ : Sm ζ) (hu : Sm u) (x : Rd d) :
    E.Γ ((ζ * ζ) * u) u x = ζ x ^ 2 * E.Γ u u x + 2 * ζ x * u x * E.Γ ζ u x := by
  have hzz : Sm (ζ * ζ) := hζ.mul hζ
  rw [E.Γ_mul_left (f := ζ * ζ) (g := u) hzz hu x, E.Γ_mul_left (f := ζ) (g := ζ) (k := u) hζ hζ x]
  simp only [Pi.mul_apply]
  ring

/-- **Caccioppoli identity** (smooth `u`, `ζ ∈ C_c^∞`):
`∫ w Γ(ζu,ζu) = − ∫ w ζ² u Lu + ∫ w u² Γ(ζ,ζ)`. -/
theorem caccioppoli_identity {ζ u : Rd d → ℝ} (hζ : Sm ζ) (hc : HasCompactSupport ζ) (hu : Sm u) :
    ∫ x, E.w x * E.Γ (ζ * u) (ζ * u) x =
      - (∫ x, E.w x * (ζ x ^ 2 * u x) * E.L u x) + ∫ x, E.w x * (u x ^ 2 * E.Γ ζ ζ x) := by
  obtain ⟨g, hgdef⟩ : ∃ g : Rd d → ℝ, g = (ζ * ζ) * u := ⟨_, rfl⟩
  have hg : Sm g := by rw [hgdef]; exact (hζ.mul hζ).mul hu
  have hgc : HasCompactSupport g := by
    rw [hgdef]; exact (hc.mul_right).mul_right
  have h0 := E.ibp_master (f := u) (g := g) hu hg (Or.inl hgc)
  have cw : Continuous E.w := E.w_smooth.continuous
  have cL : Continuous (E.L u) := (E.sm_L hu).continuous
  have I1 : Integrable (fun x => E.w x * g x * E.L u x + E.w x * E.Γ g u x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((cw.mul hg.continuous).mul cL).add (cw.mul (E.sm_Γ hg hu).continuous)
    · exact HasCompactSupport.add (hcs_of_factor hgc fun x hx => by simp [hx])
        (hcs_of_factor (E.hcs_Γ_left (g := u) hgc) fun x hx => by simp [hx])
  have I2 : Integrable (fun x => E.w x * (ζ x ^ 2 * u x) * E.L u x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (cw.mul ((hζ.continuous.pow 2).mul hu.continuous)).mul cL
    · exact hcs_of_factor hc fun x hx => by simp [hx]
  have I3 : Integrable (fun x => E.w x * (u x ^ 2 * E.Γ ζ ζ x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact cw.mul ((hu.continuous.pow 2).mul (E.sm_Γ hζ hζ).continuous)
    · exact hcs_of_factor (E.hcs_Γ_left (g := ζ) hc) fun x hx => by simp [hx]
  have e : ∀ x, E.w x * E.Γ (ζ * u) (ζ * u) x =
      (E.w x * g x * E.L u x + E.w x * E.Γ g u x)
        - E.w x * (ζ x ^ 2 * u x) * E.L u x + E.w x * (u x ^ 2 * E.Γ ζ ζ x) := by
    intro x
    rw [E.Γ_prod_self hζ hu, hgdef, E.Γ_sq_mul hζ hu]
    simp only [Pi.mul_apply]
    ring
  simp_rw [e]
  have k1 : ∫ x, ((E.w x * g x * E.L u x + E.w x * E.Γ g u x) - E.w x * (ζ x ^ 2 * u x) * E.L u x) =
      (∫ x, (E.w x * g x * E.L u x + E.w x * E.Γ g u x)) - ∫ x, E.w x * (ζ x ^ 2 * u x) * E.L u x :=
    integral_sub I1 I2
  have k2 : ∫ x, (((E.w x * g x * E.L u x + E.w x * E.Γ g u x) - E.w x * (ζ x ^ 2 * u x) * E.L u x)
      + E.w x * (u x ^ 2 * E.Γ ζ ζ x)) =
      (∫ x, ((E.w x * g x * E.L u x + E.w x * E.Γ g u x) - E.w x * (ζ x ^ 2 * u x) * E.L u x))
        + ∫ x, E.w x * (u x ^ 2 * E.Γ ζ ζ x) :=
    integral_add (I1.sub I2) I3
  rw [k2, k1, h0]
  ring

/-- positivity of the quadratic form of `a` -/
lemma quad_nonneg (v : Fin d → ℝ) (x : Rd d) : 0 ≤ ∑ i, ∑ j, E.a i j x * v i * v j := by
  by_cases h : v = 0
  · simp [h]
  · exact (E.a_pos x v h).le

/-- pointwise Young-type bound `ζ² Γ(u,u) ≤ 2 Γ(ζu,ζu) + 2 u² Γ(ζ,ζ)` (the quadratic form at `ζ∇u + 2u∇ζ`). -/
lemma Γ_young {ζ u : Rd d → ℝ} (hζ : Sm ζ) (hu : Sm u) (x : Rd d) :
    ζ x ^ 2 * E.Γ u u x ≤ 2 * E.Γ (ζ * u) (ζ * u) x + 2 * (u x ^ 2 * E.Γ ζ ζ x) := by
  have hq := E.quad_nonneg (fun i => ζ x * pderiv u i x + 2 * u x * pderiv ζ i x) x
  have hexp : ∑ i, ∑ j, E.a i j x * (ζ x * pderiv u i x + 2 * u x * pderiv ζ i x) *
      (ζ x * pderiv u j x + 2 * u x * pderiv ζ j x) =
      ζ x ^ 2 * E.Γ u u x + 2 * ζ x * u x * E.Γ u ζ x + 2 * ζ x * u x * E.Γ ζ u x
        + 4 * u x ^ 2 * E.Γ ζ ζ x := by
    unfold Γ
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hexp, show E.Γ u ζ x = E.Γ ζ u x from congrFun (E.Γ_symm u ζ) x] at hq
  rw [E.Γ_prod_self hζ hu]
  nlinarith [hq]

/-- **Caccioppoli inequality with a smooth cut-off** (smooth `u`; Evans §6.3.1 Step 1):
`∫ w ζ² Γ(u,u) ≤ − 2 ∫ w ζ² u Lu + 4 ∫ w u² Γ(ζ,ζ)`. -/
theorem caccioppoli {ζ u : Rd d → ℝ} (hζ : Sm ζ) (hc : HasCompactSupport ζ) (hu : Sm u) :
    ∫ x, E.w x * (ζ x ^ 2 * E.Γ u u x) ≤
      - 2 * (∫ x, E.w x * (ζ x ^ 2 * u x) * E.L u x) + 4 * ∫ x, E.w x * (u x ^ 2 * E.Γ ζ ζ x) := by
  have cw : Continuous E.w := E.w_smooth.continuous
  have hζu : Sm (ζ * u) := hζ.mul hu
  have hcu : HasCompactSupport (ζ * u) := hc.mul_right
  have J1 : Integrable (fun x => E.w x * (ζ x ^ 2 * E.Γ u u x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact cw.mul ((hζ.continuous.pow 2).mul (E.sm_Γ hu hu).continuous)
    · exact hcs_of_factor hc fun x hx => by simp [hx]
  have J2 : Integrable (fun x => E.w x * E.Γ (ζ * u) (ζ * u) x) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact cw.mul (E.sm_Γ hζu hζu).continuous
    · exact hcs_of_factor (E.hcs_Γ_left (g := ζ * u) hcu) fun x hx => by simp [hx]
  have J3 : Integrable (fun x => E.w x * (u x ^ 2 * E.Γ ζ ζ x)) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact cw.mul ((hu.continuous.pow 2).mul (E.sm_Γ hζ hζ).continuous)
    · exact hcs_of_factor (E.hcs_Γ_left (g := ζ) hc) fun x hx => by simp [hx]
  have hmono : ∫ x, E.w x * (ζ x ^ 2 * E.Γ u u x) ≤
      ∫ x, (2 * (E.w x * E.Γ (ζ * u) (ζ * u) x) + 2 * (E.w x * (u x ^ 2 * E.Γ ζ ζ x))) := by
    refine integral_mono J1 ((J2.const_mul 2).add (J3.const_mul 2)) fun x => ?_
    have := E.Γ_young hζ hu x
    have hw := (E.w_pos x).le
    nlinarith [mul_le_mul_of_nonneg_left this hw]
  have k : ∫ x, (2 * (E.w x * E.Γ (ζ * u) (ζ * u) x) + 2 * (E.w x * (u x ^ 2 * E.Γ ζ ζ x))) =
      2 * (∫ x, E.w x * E.Γ (ζ * u) (ζ * u) x) + 2 * ∫ x, E.w x * (u x ^ 2 * E.Γ ζ ζ x) := by
    rw [integral_add (J2.const_mul 2) (J3.const_mul 2), integral_const_mul, integral_const_mul]
  rw [k, E.caccioppoli_identity hζ hc hu] at hmono
  linarith

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
