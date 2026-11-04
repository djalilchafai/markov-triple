import Mathlib
import MarkovTriple.BGL.Instances.GibbsRd.DirectEllCut
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllEnergy
import MarkovTriple.BGL.Instances.GibbsRd.Core2EllMain
import MarkovTriple.BGL.Theory.Extension.ClosedIdent
import MarkovTriple.BGL.Theory.Extension.Gamma2Ident

/-!
# Direct converse of BGL Prop. 3.3.17 for `EllData d`: the cut-off identity and `L f ∈ L²` (R20, Stream D2)

Statements: `STATEMENTS_R20_DirectEll.md` (D2, D5).

## DIFFERENCE FROM BGL

*BGL* (Prop. 3.3.17, p. 161-162) proves the converse (`f ∈ 𝒜 ∩ L²`, `Γ(f), Γ₂(f) ∈ L¹` ⇒ `f ∈ 𝒟(L)`) by extending a linear form
to all of `L²` through the density of `(L² + Id)𝒜₀`, i.e. `Core2` (ERRATA R15-1); R17-R19 proved `Core2` only under growth
hypotheses (`CoreCut`, `GrowHess3`, ...).  *Here* we do NOT use `Core2` or `CoreCut`.  We prove
`L f ∈ L²(μ)` directly by the cut-off (Caccioppoli) technique of BGL Prop. 3.2.1 (p. 142), applied to `Γ₂` instead of `Γ`: for a
completeness cut-off `χ` (`Γ(χ) ≤ 1`, no other bound) and `φ = χ²`,

`∫ χ²(Lf)² = ∫ χ²Γ₂(f) + ∫ χ Γ(χ, Γ f) − 2 ∫ χ Lf Γ(χ, f)`   (`cutoff_identity`; Bochner `Γ₂ = ½LΓ − Γ(·,L·)` and two integrations by parts).

The middle term is `2 Hess f(∇χ,∇f)`; it is controlled by `|∇χ|` only, through the Hessian Cauchy–Schwarz
`HessCS ρ : |Γ(χ, Γf)|² ≤ 4Γ(χ)Γ(f)(Γ₂(f) − ρΓ(f))` (proved in `Riemannian/DirectRiemHess.lean` from Bochner's formula and
`Curv ρ`; here it is an explicit hypothesis of the abstract estimate).  Then Fatou gives `Lf ∈ L²`, and the converse is obtained from
the EXISTING ESA statement `FullTriple.mem_domain_of_ESA` (BGL Prop. 3.3.6 (i), via F10): `f ∈ 𝒜 ∩ L²`, `Lf ∈ L²` ⇒ `[f] ∈ 𝒟(L)`, `L[f] = [Lf]`.
Hypotheses differing from BGL / from R19: only `Curv ρ` (any sign) and completeness; no `Core2`, no `CoreCut`.
`f ∈ L²` and `ρ > 0` are NOT used for `Lf ∈ L²`.

* `HessCS`, `cutoff_identity`, `cutoff_bound`, `memLp_L_of_hessCS`, `ell_mem_domain_of_hessCS`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
open MarkovTriple.BGL (FullTriple DiffusionTriple pderiv)

namespace MarkovTriple.BGL.Instances.GibbsRd

variable {d : ℕ}

namespace EllData
variable (E : EllData d)

/-- **Hessian Cauchy–Schwarz** (pointwise): `|Γ(u, Γ f)|² ≤ 4 Γ(u) Γ(f) (Γ₂(f) − ρΓ(f))`.  In a Riemannian chart
`Γ(u,Γf) = 2 Hess f(∇u,∇f)` and `Γ₂(f) − ρΓ(f) ≥ ‖Hess f‖²` (`RiemData.riem_hessCS`, `EllData.hessCS_of_curv`). -/
def HessCS (ρ : ℝ) : Prop :=
  ∀ f u : Rd d → ℝ, Sm f → Sm u → ∀ x,
    (E.Γ u (E.Γ f f) x) ^ 2 ≤ 4 * E.Γ u u x * E.Γ f f x * E.G2' ρ f f x

private lemma int_cs {μ : Measure (Rd d)} [IsFiniteMeasure μ] (h : Rd d → ℝ) (hc : Continuous h)
    (hs : HasCompactSupport h) : Integrable h μ := hc.integrable_of_hasCompactSupport hs

/-- **The cut-off identity**: for `c ∈ C_c^∞` and `f ∈ C^∞`,
`∫ c²(Lf)² = ∫ c² Γ₂(f) + ∫ c Γ(c, Γ f) − 2 ∫ c Lf Γ(c, f)` (all integrals of compactly supported continuous functions). -/
theorem cutoff_identity {c f : Rd d → ℝ} (hc : Sm c) (hcc : HasCompactSupport c) (hf : Sm f) :
    ∫ x, (c x * c x) * (E.L f x) ^ 2 ∂E.μ =
      ∫ x, (c x * c x) * E.G2 f f x ∂E.μ + ∫ x, c x * E.Γ c (E.Γ f f) x ∂E.μ
        - 2 * ∫ x, c x * E.L f x * E.Γ c f x ∂E.μ := by
  have hLf : Sm (E.L f) := E.sm_L hf
  have hΓff : Sm (E.Γ f f) := E.sm_Γ hf hf
  have hcc2 : HasCompactSupport (c * c) := hcc.mul_right
  -- the two integrations by parts
  have h1 := E.ibp_sm hΓff (hc.mul hc) (Or.inl hcc2)
  have h2 := E.ibp_sm hf ((hc.mul hc).mul hLf) (Or.inl hcc2.mul_right)
  -- pointwise Leibniz
  have l1 : ∀ k x, E.Γ (c * c) k x = 2 * (c x * E.Γ c k x) := by
    intro k x
    rw [E.Γ_leib hc hc k x]; ring
  have l2 : ∀ x, E.Γ ((c * c) * E.L f) f x =
      (c x * c x) * E.Γ (E.L f) f x + E.L f x * (2 * (c x * E.Γ c f x)) := by
    intro x
    have := E.Γ_leib (f := c * c) (g := E.L f) (hc.mul hc) hLf f x
    rw [this, l1 f x]
    simp only [Pi.mul_apply]
  -- integrability of the pieces
  have iA1 : Integrable (fun x => (c x * c x) * E.L (E.Γ f f) x) E.μ :=
    int_cs _ ((hc.mul hc).mul (E.sm_L hΓff)).continuous hcc2.mul_right
  have iA2 : Integrable (fun x => c x * E.Γ c (E.Γ f f) x) E.μ :=
    int_cs _ (hc.mul (E.sm_Γ hc hΓff)).continuous hcc.mul_right
  have iA3 : Integrable (fun x => (c x * c x) * E.Γ (E.L f) f x) E.μ :=
    int_cs _ ((hc.mul hc).mul (E.sm_Γ hLf hf)).continuous hcc2.mul_right
  have iA4 : Integrable (fun x => (c x * c x) * (E.L f x) ^ 2) E.μ :=
    int_cs _ ((hc.mul hc).mul (hLf.pow 2)).continuous hcc2.mul_right
  have iA5 : Integrable (fun x => c x * E.L f x * E.Γ c f x) E.μ :=
    int_cs _ ((hc.mul hLf).mul (E.sm_Γ hc hf)).continuous hcc.mul_right.mul_right
  have iA6 : Integrable (fun x => (c x * c x) * E.G2 f f x) E.μ :=
    int_cs _ ((hc.mul hc).mul (E.sm_G2 hf hf)).continuous hcc2.mul_right
  -- first IBP: ∫ c² LΓf = -2 ∫ c Γ(c,Γf)
  have e1 : ∫ x, (c x * c x) * E.L (E.Γ f f) x ∂E.μ = -(2 * ∫ x, c x * E.Γ c (E.Γ f f) x ∂E.μ) := by
    have : ∫ x, (c * c) x * E.L (E.Γ f f) x ∂E.μ = -∫ x, E.Γ (c * c) (E.Γ f f) x ∂E.μ := h1
    simp only [Pi.mul_apply, l1] at this
    rw [this, integral_const_mul]
  -- second IBP: ∫ c²(Lf)² = -∫ c²Γ(Lf,f) - 2∫ c Lf Γ(c,f)
  have e2 : ∫ x, (c x * c x) * (E.L f x) ^ 2 ∂E.μ =
      -(∫ x, (c x * c x) * E.Γ (E.L f) f x ∂E.μ + 2 * ∫ x, c x * E.L f x * E.Γ c f x ∂E.μ) := by
    have : ∫ x, ((c * c) * E.L f) x * E.L f x ∂E.μ = -∫ x, E.Γ ((c * c) * E.L f) f x ∂E.μ := h2
    simp only [l2] at this
    have e3 : ∫ x, ((c * c) * E.L f) x * E.L f x ∂E.μ = ∫ x, (c x * c x) * (E.L f x) ^ 2 ∂E.μ :=
      integral_congr_ae (Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
    have e4 : ∫ x, ((c x * c x) * E.Γ (E.L f) f x + E.L f x * (2 * (c x * E.Γ c f x))) ∂E.μ =
        ∫ x, (c x * c x) * E.Γ (E.L f) f x ∂E.μ + 2 * ∫ x, c x * E.L f x * E.Γ c f x ∂E.μ := by
      rw [integral_add iA3 ((iA5.const_mul 2).congr (Eventually.of_forall fun x => by ring)),
        ← integral_const_mul]
      congr 1
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    rw [← e3, this, e4]
  -- the Bochner combination
  have e5 : ∫ x, (c x * c x) * E.G2 f f x ∂E.μ =
      1 / 2 * ∫ x, (c x * c x) * E.L (E.Γ f f) x ∂E.μ - ∫ x, (c x * c x) * E.Γ (E.L f) f x ∂E.μ := by
    have pw : ∀ x, (c x * c x) * E.G2 f f x =
        1 / 2 * ((c x * c x) * E.L (E.Γ f f) x) - (c x * c x) * E.Γ (E.L f) f x := by
      intro x
      unfold G2
      rw [E.Γ_symm_apply f (E.L f) x]
      ring
    simp only [pw]
    rw [integral_sub (iA1.const_mul _) iA3, integral_const_mul]
  linarith

/-- the integrand bound for the cross term: `|c Γ(c,Γf)| ≤ Γ(f) + (Γ₂(f) − ρΓ(f))` -/
lemma cross_bound {ρ : ℝ} (hρ : E.Curv ρ) (hH : E.HessCS ρ) {c f : Rd d → ℝ} (hc : Sm c) (hf : Sm f)
    (h01 : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (hg : ∀ x, E.Γ c c x ≤ 1) (x : Rd d) :
    |c x * E.Γ c (E.Γ f f) x| ≤ E.Γ f f x + E.G2' ρ f f x := by
  have h := hH f c hf hc x
  have hN := E.Γ_nonneg f x
  have hG := E.G2'_nonneg hρ hf x
  have hk0 := E.Γ_nonneg c x
  have hk1 := hg x
  set a := E.Γ c (E.Γ f f) x
  set N := E.Γ f f x
  set G := E.G2' ρ f f x
  have hsq : a ^ 2 ≤ (N + G) ^ 2 := by
    refine h.trans ?_
    have : 4 * E.Γ c c x * N * G ≤ 4 * 1 * N * G := by
      have := mul_nonneg hN hG
      nlinarith
    nlinarith [sq_nonneg (N - G)]
  have hb := abs_le_of_sq_le_sq' hsq (by positivity)
  have : |a| ≤ N + G := abs_le.2 hb
  rw [abs_mul, abs_of_nonneg (h01 x).1]
  exact (mul_le_of_le_one_left (abs_nonneg _) (h01 x).2).trans this

/-- **Uniform bound**: for a completeness cut-off `c` (`0 ≤ c ≤ 1`, `Γ(c) ≤ 1`, no other bound),
`∫ c² (Lf)² ≤ 2 (∫|Γ₂(f)| + ∫(Γ(f) + Γ₂(f) − ρΓ(f)) + 2∫Γ(f))`. -/
theorem cutoff_bound {ρ : ℝ} (hρ : E.Curv ρ) (hH : E.HessCS ρ) {c f : Rd d → ℝ} (hc : Sm c)
    (hcc : HasCompactSupport c) (h01 : ∀ x, 0 ≤ c x ∧ c x ≤ 1) (hg : ∀ x, E.Γ c c x ≤ 1) (hf : Sm f)
    (hG : Integrable (E.Γ f f) E.μ) (hG2 : Integrable (E.G2 f f) E.μ) :
    ∫ x, (c x * c x) * (E.L f x) ^ 2 ∂E.μ ≤
      2 * (∫ x, |E.G2 f f x| ∂E.μ + ∫ x, (E.Γ f f x + E.G2' ρ f f x) ∂E.μ + 2 * ∫ x, E.Γ f f x ∂E.μ) := by
  have hLf : Sm (E.L f) := E.sm_L hf
  have hΓff : Sm (E.Γ f f) := E.sm_Γ hf hf
  have hcc2 : HasCompactSupport (c * c) := hcc.mul_right
  have hid := E.cutoff_identity hc hcc hf
  have iA4 : Integrable (fun x => (c x * c x) * (E.L f x) ^ 2) E.μ :=
    int_cs _ ((hc.mul hc).mul (hLf.pow 2)).continuous hcc2.mul_right
  have iA2 : Integrable (fun x => c x * E.Γ c (E.Γ f f) x) E.μ :=
    int_cs _ (hc.mul (E.sm_Γ hc hΓff)).continuous hcc.mul_right
  have iA5 : Integrable (fun x => c x * E.L f x * E.Γ c f x) E.μ :=
    int_cs _ ((hc.mul hLf).mul (E.sm_Γ hc hf)).continuous hcc.mul_right.mul_right
  have iA6 : Integrable (fun x => (c x * c x) * E.G2 f f x) E.μ :=
    int_cs _ ((hc.mul hc).mul (E.sm_G2 hf hf)).continuous hcc2.mul_right
  have iG2' : Integrable (fun x => E.G2' ρ f f x) E.μ := hG2.sub (hG.const_mul ρ)
  have iS : Integrable (fun x => E.Γ f f x + E.G2' ρ f f x) E.μ := hG.add iG2'
  have iR : Integrable (fun x => 1 / 2 * ((c x * c x) * (E.L f x) ^ 2) + 2 * E.Γ f f x) E.μ :=
    (iA4.const_mul _).add (hG.const_mul 2)
  -- J1
  have b1 : ∫ x, (c x * c x) * E.G2 f f x ∂E.μ ≤ ∫ x, |E.G2 f f x| ∂E.μ := by
    refine integral_mono iA6 hG2.abs fun x => ?_
    have p0 : 0 ≤ c x * c x := mul_self_nonneg _
    have p1 : c x * c x ≤ 1 := by nlinarith [h01 x]
    calc (c x * c x) * E.G2 f f x ≤ |(c x * c x) * E.G2 f f x| := le_abs_self _
      _ = (c x * c x) * |E.G2 f f x| := by rw [abs_mul, abs_of_nonneg p0]
      _ ≤ |E.G2 f f x| := mul_le_of_le_one_left (abs_nonneg _) p1
  -- J2
  have b2 : ∫ x, c x * E.Γ c (E.Γ f f) x ∂E.μ ≤ ∫ x, (E.Γ f f x + E.G2' ρ f f x) ∂E.μ :=
    integral_mono iA2 iS fun x => (le_abs_self _).trans (E.cross_bound hρ hH hc hf h01 hg x)
  -- J3
  have b3 : -(2 * ∫ x, c x * E.L f x * E.Γ c f x ∂E.μ) ≤
      1 / 2 * ∫ x, (c x * c x) * (E.L f x) ^ 2 ∂E.μ + 2 * ∫ x, E.Γ f f x ∂E.μ := by
    rw [← integral_const_mul, ← integral_neg, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (iA4.const_mul _) (hG.const_mul 2)]
    refine integral_mono (iA5.const_mul 2).neg iR fun x => ?_
    have hcs := E.Γ_cs c f x
    have hΓcc := hg x
    have hN := E.Γ_nonneg f x
    have hk0 := E.Γ_nonneg c x
    have hq : E.Γ c f x ^ 2 ≤ E.Γ f f x := by
      refine hcs.trans ?_
      nlinarith
    set a := c x * E.L f x
    set b := E.Γ c f x
    have : -(2 * (a * b)) ≤ 1 / 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a + 2 * b)]
    have e : (c x * c x) * (E.L f x) ^ 2 = a ^ 2 := by simp only [a]; ring
    show -(2 * (c x * E.L f x * E.Γ c f x)) ≤ 1 / 2 * ((c x * c x) * (E.L f x) ^ 2) + 2 * E.Γ f f x
    rw [e]
    nlinarith
  linarith

/-- **D2**: `L f ∈ L²(μ)` for smooth `f` with `Γ(f), Γ₂(f) ∈ L¹(μ)`, from `Curv ρ` and the Hessian Cauchy–Schwarz,
with the completeness cut-offs only (no `CoreCut`, no `Core2`). -/
theorem memLp_L_of_hessCS {ρ : ℝ} (hρ : E.Curv ρ) (hH : E.HessCS ρ) {f : Rd d → ℝ} (hf : Sm f)
    (hG : Integrable (E.Γ f f) E.μ) (hG2 : Integrable (E.G2 f f) E.μ) : MemLp (E.L f) 2 E.μ := by
  obtain ⟨χ, hχ⟩ := E.exists_gradCut
  have hLf : Sm (E.L f) := E.sm_L hf
  set B : ℝ := 2 * (∫ x, |E.G2 f f x| ∂E.μ + ∫ x, (E.Γ f f x + E.G2' ρ f f x) ∂E.μ +
    2 * ∫ x, E.Γ f f x ∂E.μ) with hB
  have hint : Integrable (fun x => (E.L f x) ^ 2) E.μ := by
    refine integrable_of_cut_ae (φ := fun n x => χ n x * χ n x) (B := B) (hLf.pow 2).continuous
      (fun x => sq_nonneg _) (fun n => (hχ.smooth n).continuous.mul (hχ.smooth n).continuous)
      (fun n x => mul_self_nonneg _) (fun n => (hχ.cs n).mul_right) ?_ ?_
    · filter_upwards [hχ.tendsto] with x hx
      simpa using hx.mul hx
    · intro n
      exact E.cutoff_bound hρ hH (hχ.smooth n) (hχ.cs n) (hχ.mem n) (hχ.grad n) hf hG hG2
  exact (memLp_two_iff_integrable_sq hLf.continuous.aestronglyMeasurable).2 hint

/-- **D5 (abstract form)**: the converse of BGL Prop. 3.3.17 for `EllData d`, from `Curv ρ` and `HessCS ρ`, WITHOUT
`Core2`/`CoreCut` (via `memLp_L_of_hessCS` and `FullTriple.mem_domain_of_ESA`). -/
theorem ell_mem_domain_of_hessCS {ρ : ℝ} (hρ : E.Curv ρ) (hH : E.HessCS ρ) {f : Rd d → ℝ}
    (hf : f ∈ E.fullU.A) (hf2 : MemLp f 2 E.μ)
    (hG : Integrable (FullTriple.G E.fullU f f) E.μ)
    (hG2 : Integrable (E.fullU.toDiffusionTriple.Γ₂ f f) E.μ) :
    ∃ hF : hf2.toLp f ∈ E.fullU.toDiffusionTriple.generator.domain,
      ((E.fullU.toDiffusionTriple.generator ⟨hf2.toLp f, hF⟩ : Lp ℝ 2 E.μ) : Rd d → ℝ) =ᵐ[E.μ]
        E.fullU.L f := by
  have hfS : Sm f := hf
  have hG' : Integrable (E.Γ f f) E.μ := by
    have e : FullTriple.G E.fullU f f = E.Γ f f := E.ΓA_eq hfS hfS
    rwa [e] at hG
  have hG2' : Integrable (E.G2 f f) E.μ := by
    have e : E.fullU.toDiffusionTriple.Γ₂ f f = E.G2 f f := by
      have h := E.Γ₂_eq_comb hfS
      funext x
      have h1 : E.fullU.toDiffusionTriple.Γ₂ f f x = (E.L (E.Γ f f) x - E.Γ f (E.L f) x - E.Γ (E.L f) f x) / 2 :=
        congrFun h x
      rw [h1]
      unfold G2
      rw [E.Γ_symm_apply f (E.L f) x]
    rwa [e] at hG2
  have hLf2 : MemLp (E.fullU.L f) 2 E.μ := E.memLp_L_of_hessCS hρ hH hfS hG' hG2'
  obtain ⟨hF, _⟩ := FullTriple.mem_domain_of_ESA (T := E.fullU) hf hf2 hLf2
  exact ⟨hF, FullTriple.generator_ae_L hf hf2 hF⟩

end EllData

end MarkovTriple.BGL.Instances.GibbsRd
