import Mathlib
import MarkovTriple.BGL.Instances.Riemannian.R27.LChange

/-!
# General atlases (`d ≥ 1`), glued `Γ`, `L`, `Γ₂`, and chart independence derived from the transition laws

A `Chart M d` is a parametrisation `pt : ℝ^d ⊇ U → M` (injective on the open set `U`) with its co-metric `g` and Riemannian
density `w` (BGL Sect. 1.11.3, Appendix C.3).  An `Atlas` is a family of charts covering `M` together with the transition
maps `τ_ab` on the (open) overlaps, of class `C²`, satisfying the pushforward laws
`g_b ∘ τ = J g_a Jᵀ`, `w_a = (w_b ∘ τ) |det J|`.

The glued `Γ`, `L` evaluate the chartwise formulas in a chart chosen at each point; chart independence
(`glueΓ_indep`, `glueL_indep`, `glueΓ₂_indep`) is deduced from the transition laws alone, via `Gch_chart_change` and `Lch_chart_change`.
No global operator is used.  No topology on `M` is needed.
-/

open MarkovTriple.BGL (pderiv)
open Filter Topology

namespace MarkovTriple.BGL.Instances.Riemannian.R27

/-- a chart: a parametrisation of a piece of `M` by an open set of `ℝ^d`, with co-metric `g` and density `w` -/
structure Chart (M : Type) (d : ℕ) where
  U : Set (Ev d)
  isOpen : IsOpen U
  pt : Ev d → M
  injOn : Set.InjOn pt U
  g : Fin d → Fin d → Ev d → ℝ
  w : Ev d → ℝ
  g_smooth : ∀ i j, ContDiffOn ℝ (⊤ : ℕ∞) (g i j) U
  w_smooth : ContDiffOn ℝ (⊤ : ℕ∞) w U
  w_pos : ∀ x ∈ U, 0 < w x

/-- the overlap domain of two charts (in the coordinates of `a`) -/
def Chart.overlap {M : Type} {d : ℕ} (a b : Chart M d) : Set (Ev d) :=
  {x | x ∈ a.U ∧ ∃ y ∈ b.U, b.pt y = a.pt x}

/-- an atlas with transition maps satisfying the pushforward laws -/
structure Atlas (M : Type) (d : ℕ) where
  ι : Type
  chart : ι → Chart M d
  cover : ∀ p : M, ∃ i, ∃ x ∈ (chart i).U, (chart i).pt x = p
  τ : ι → ι → Ev d → Ev d
  overlap_open : ∀ a b, IsOpen ((chart a).overlap (chart b))
  τ_mem : ∀ a b, ∀ x ∈ (chart a).overlap (chart b),
    τ a b x ∈ (chart b).U ∧ (chart b).pt (τ a b x) = (chart a).pt x
  τ_smooth : ∀ a b, ContDiffOn ℝ 2 (τ a b) ((chart a).overlap (chart b))
  τ_g : ∀ a b, ∀ x ∈ (chart a).overlap (chart b), ∀ i j,
    (chart b).g i j (τ a b x) = ∑ k, ∑ l, jac (τ a b) x i k * (chart a).g k l x * jac (τ a b) x j l
  τ_w : ∀ a b, ∀ x ∈ (chart a).overlap (chart b),
    (chart a).w x = (chart b).w (τ a b x) * |(jac (τ a b) x).det|

variable {M : Type} {d : ℕ}

/-- functions of class `C^k` in every chart -/
def Atlas.Smooth (A : Atlas M d) (k : ℕ) (f : M → ℝ) : Prop :=
  ∀ i, ContDiffOn ℝ k (f ∘ (A.chart i).pt) (A.chart i).U

section congr

variable {g : Fin d → Fin d → Ev d → ℝ} {w : Ev d → ℝ} {F G : Ev d → ℝ} {x : Ev d}

lemma Gch_congr_eventually {H K : Ev d → ℝ} (hF : F =ᶠ[𝓝 x] G) (hH : H =ᶠ[𝓝 x] K) :
    Gch g F H x = Gch g G K x := by
  unfold Gch
  simp only [pderiv_congr_eventually hF, pderiv_congr_eventually hH]

lemma Lch_congr_eventually (hF : F =ᶠ[𝓝 x] G) : Lch g w F x = Lch g w G x := by
  unfold Lch
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  refine pderiv_congr_eventually ?_ i
  filter_upwards [hF.eventually_nhds] with y hy
  simp only [pderiv_congr_eventually hy]

end congr

namespace Atlas
variable (A : Atlas M d)

/-- the chart index chosen at `p` -/
noncomputable def idx (p : M) : A.ι := (A.cover p).choose
/-- the coordinate chosen at `p` -/
noncomputable def pos (p : M) : Ev d := (A.cover p).choose_spec.choose
lemma pos_mem (p : M) : A.pos p ∈ (A.chart (A.idx p)).U := (A.cover p).choose_spec.choose_spec.1
lemma pt_pos (p : M) : (A.chart (A.idx p)).pt (A.pos p) = p := (A.cover p).choose_spec.choose_spec.2

/-- glued carré du champ -/
noncomputable def glueΓ (f h : M → ℝ) (p : M) : ℝ :=
  Gch (A.chart (A.idx p)).g (f ∘ (A.chart (A.idx p)).pt) (h ∘ (A.chart (A.idx p)).pt) (A.pos p)

/-- glued Laplace-Beltrami operator -/
noncomputable def glueL (f : M → ℝ) (p : M) : ℝ :=
  Lch (A.chart (A.idx p)).g (A.chart (A.idx p)).w (f ∘ (A.chart (A.idx p)).pt) (A.pos p)

/-- glued iterated carré du champ `Γ₂(f) = ½ L Γ(f,f) - Γ(f, Lf)` -/
noncomputable def glueΓ₂ (f : M → ℝ) (p : M) : ℝ :=
  (1 / 2) * A.glueL (A.glueΓ f f) p - A.glueΓ f (A.glueL f) p

/-- two points of two charts with the same image are related by the transition map -/
lemma τ_eq (a b : A.ι) {x y : Ev d} (hx : x ∈ (A.chart a).U) (hy : y ∈ (A.chart b).U)
    (h : (A.chart a).pt x = (A.chart b).pt y) : x ∈ (A.chart a).overlap (A.chart b) ∧ A.τ a b x = y := by
  have hov : x ∈ (A.chart a).overlap (A.chart b) := ⟨hx, y, hy, h.symm⟩
  refine ⟨hov, ?_⟩
  obtain ⟨h1, h2⟩ := A.τ_mem a b x hov
  exact (A.chart b).injOn h1 hy (h2.trans h)

/-- regularity data of a transition at a point of the overlap -/
lemma τ_contDiffAt (a b : A.ι) {x : Ev d} (hx : x ∈ (A.chart a).overlap (A.chart b)) :
    ContDiffAt ℝ 2 (A.τ a b) x :=
  (A.τ_smooth a b).contDiffAt ((A.overlap_open a b).mem_nhds hx)

lemma smooth_contDiffAt {k : ℕ} {f : M → ℝ} (hf : A.Smooth k f) (i : A.ι) {x : Ev d}
    (hx : x ∈ (A.chart i).U) : ContDiffAt ℝ k (f ∘ (A.chart i).pt) x :=
  (hf i).contDiffAt ((A.chart i).isOpen.mem_nhds hx)

lemma g_contDiffAt (i : A.ι) {x : Ev d} (hx : x ∈ (A.chart i).U) (a b : Fin d) :
    ContDiffAt ℝ 1 ((A.chart i).g a b) x :=
  (((A.chart i).g_smooth a b).contDiffAt ((A.chart i).isOpen.mem_nhds hx)).of_le (by exact_mod_cast le_top)

lemma w_contDiffAt (i : A.ι) {x : Ev d} (hx : x ∈ (A.chart i).U) :
    ContDiffAt ℝ 1 (A.chart i).w x :=
  (((A.chart i).w_smooth).contDiffAt ((A.chart i).isOpen.mem_nhds hx)).of_le (by exact_mod_cast le_top)

/-- on the overlap, `f ∘ pt_a = (f ∘ pt_b) ∘ τ` -/
lemma comp_eventually (a b : A.ι) (f : M → ℝ) {x : Ev d} (hx : x ∈ (A.chart a).overlap (A.chart b)) :
    (f ∘ (A.chart a).pt) =ᶠ[𝓝 x] ((f ∘ (A.chart b).pt) ∘ A.τ a b) := by
  filter_upwards [(A.overlap_open a b).mem_nhds hx] with z hz
  simp only [Function.comp_apply]
  rw [(A.τ_mem a b z hz).2]

/-- **Chart independence of `Γ`, derived from the transition laws**. -/
theorem glueΓ_indep {f h : M → ℝ} (hf : A.Smooth 2 f) (hh : A.Smooth 2 h) (i : A.ι) {x : Ev d}
    (hx : x ∈ (A.chart i).U) :
    A.glueΓ f h ((A.chart i).pt x) =
      Gch (A.chart i).g (f ∘ (A.chart i).pt) (h ∘ (A.chart i).pt) x := by
  set p := (A.chart i).pt x with hp
  obtain ⟨hov, hτx⟩ := A.τ_eq (A.idx p) i (A.pos_mem p) hx ((A.pt_pos p).trans hp)
  set a := A.idx p
  set x0 := A.pos p
  unfold glueΓ
  have hτ := A.τ_contDiffAt a i hov
  have hlaw : ∀ i' j', (A.chart i).g i' j' (A.τ a i x0) =
      ∑ k, ∑ l, jac (A.τ a i) x0 i' k * (A.chart a).g k l x0 * jac (A.τ a i) x0 j' l :=
    A.τ_g a i x0 hov
  have key := Gch_chart_change (A.chart a).g (A.chart i).g (A.τ a i) (f ∘ (A.chart i).pt)
    (h ∘ (A.chart i).pt) x0 (hτ.differentiableAt (by norm_num))
    (((A.smooth_contDiffAt hf i (A.τ_mem a i x0 hov).1).differentiableAt (by norm_num)))
    (((A.smooth_contDiffAt hh i (A.τ_mem a i x0 hov).1).differentiableAt (by norm_num))) hlaw
  rw [hτx] at key
  rw [key]
  exact Gch_congr_eventually (A.comp_eventually a i f hov) (A.comp_eventually a i h hov)

/-- **Chart independence of `L`, derived from the transition laws** (Piola identity inside). -/
theorem glueL_indep {f : M → ℝ} (hf : A.Smooth 2 f) (i : A.ι) {x : Ev d} (hx : x ∈ (A.chart i).U) :
    A.glueL f ((A.chart i).pt x) =
      Lch (A.chart i).g (A.chart i).w (f ∘ (A.chart i).pt) x := by
  set p := (A.chart i).pt x with hp
  obtain ⟨hov, hτx⟩ := A.τ_eq (A.idx p) i (A.pos_mem p) hx ((A.pt_pos p).trans hp)
  set a := A.idx p
  set x0 := A.pos p
  unfold glueL
  have hτ := A.τ_contDiffAt a i hov
  have hmem := (A.τ_mem a i x0 hov).1
  have hlaw : ∀ᶠ z in 𝓝 x0, ∀ i' j', (A.chart i).g i' j' (A.τ a i z) =
      ∑ k, ∑ l, jac (A.τ a i) z i' k * (A.chart a).g k l z * jac (A.τ a i) z j' l := by
    filter_upwards [(A.overlap_open a i).mem_nhds hov] with z hz
    exact A.τ_g a i z hz
  have hwlaw : ∀ᶠ z in 𝓝 x0, (A.chart a).w z = (A.chart i).w (A.τ a i z) * |(jac (A.τ a i) z).det| := by
    filter_upwards [(A.overlap_open a i).mem_nhds hov] with z hz
    exact A.τ_w a i z hz
  have key := Lch_chart_change (A.chart a).g (A.chart i).g (A.chart a).w (A.chart i).w (A.τ a i)
    (f ∘ (A.chart i).pt) x0 hτ (A.smooth_contDiffAt hf i hmem)
    (A.g_contDiffAt a (A.pos_mem p)) (A.w_contDiffAt a (A.pos_mem p))
    (by rw [hτx]; exact A.g_contDiffAt i hx) (by rw [hτx]; exact A.w_contDiffAt i hx)
    ((A.chart a).w_pos x0 (A.pos_mem p)).ne' hlaw hwlaw
  rw [hτx] at key
  rw [key]
  exact Lch_congr_eventually (A.comp_eventually a i f hov)


section smoothness
variable {U : Set (Ev d)} {F H : Ev d → ℝ}

lemma contDiffOn_pderiv (hU : IsOpen U) {n : ℕ} (hF : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F U)
    (b : Fin d) : ContDiffOn ℝ (n : WithTop ℕ∞) (pderiv F b) U := by
  have h1 : ContDiffOn ℝ (n : WithTop ℕ∞) (fun y => fderiv ℝ F y) U :=
    hF.fderiv_of_isOpen hU (by push_cast; exact le_rfl)
  exact h1.clm_apply contDiffOn_const

lemma Gch_contDiffOn (c : Chart M d) {n : ℕ} (hF : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) F c.U)
    (hH : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) H c.U) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Gch c.g F H) c.U := by
  unfold Gch
  refine ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ => ?_
  refine ((((c.g_smooth i j).of_le (by exact_mod_cast le_top)).mul
    (contDiffOn_pderiv c.isOpen hF i))).mul (contDiffOn_pderiv c.isOpen hH j)

lemma Lch_contDiffOn (c : Chart M d) {n : ℕ} (hF : ContDiffOn ℝ ((n + 2 : ℕ) : WithTop ℕ∞) F c.U) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (Lch c.g c.w F) c.U := by
  unfold Lch
  have hF1 : ContDiffOn ℝ ((n + 1 + 1 : ℕ) : WithTop ℕ∞) F c.U := hF
  have hV : ∀ i, ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞)
      (fun y => c.w y * ∑ j, c.g i j y * pderiv F j y) c.U := by
    intro i
    refine ((c.w_smooth).of_le (by exact_mod_cast le_top)).mul ?_
    refine ContDiffOn.sum fun j _ => ?_
    exact ((c.g_smooth i j).of_le (by exact_mod_cast le_top)).mul (contDiffOn_pderiv c.isOpen hF1 j)
  refine ContDiffOn.mul (((c.w_smooth).of_le (by exact_mod_cast le_top)).inv fun x hx => (c.w_pos x hx).ne') ?_
  exact ContDiffOn.sum fun i _ => contDiffOn_pderiv c.isOpen (hV i) i

end smoothness

variable {f h : M → ℝ}

lemma Smooth.mono {k l : ℕ} (hkl : k ≤ l) (hf : A.Smooth l f) : A.Smooth k f :=
  fun i => (hf i).of_le (by exact_mod_cast hkl)

/-- the glued `Γ` of `C^{n+1}` functions is `C^n` in every chart -/
theorem glueΓ_smooth {n : ℕ} (hn : 1 ≤ n) (hf : A.Smooth (n + 1) f) (hh : A.Smooth (n + 1) h) :
    A.Smooth n (A.glueΓ f h) := by
  intro i
  refine (Gch_contDiffOn (A.chart i) (hf i) (hh i)).congr fun x hx => ?_
  exact A.glueΓ_indep (Smooth.mono A (by omega) hf) (Smooth.mono A (by omega) hh) i hx

/-- the glued `L` of a `C^{n+2}` function is `C^n` in every chart -/
theorem glueL_smooth {n : ℕ} (hf : A.Smooth (n + 2) f) : A.Smooth n (A.glueL f) := by
  intro i
  refine (Lch_contDiffOn (A.chart i) (hf i)).congr fun x hx => ?_
  exact A.glueL_indep (Smooth.mono A (by omega) hf) i hx

/-- **Chart independence of `Γ₂`** (from `glueΓ_indep`, `glueL_indep`). -/
theorem glueΓ₂_indep (hf : A.Smooth 4 f) (i : A.ι) {x : Ev d} (hx : x ∈ (A.chart i).U) :
    A.glueΓ₂ f ((A.chart i).pt x) =
      (1 / 2) * Lch (A.chart i).g (A.chart i).w
          (fun y => Gch (A.chart i).g (f ∘ (A.chart i).pt) (f ∘ (A.chart i).pt) y) x
        - Gch (A.chart i).g (f ∘ (A.chart i).pt)
          (fun y => Lch (A.chart i).g (A.chart i).w (f ∘ (A.chart i).pt) y) x := by
  have hΦ : A.Smooth 2 (A.glueΓ f f) := A.glueΓ_smooth (n := 2) (by norm_num) (Smooth.mono A (by norm_num) hf)
    (Smooth.mono A (by norm_num) hf)
  have hΨ : A.Smooth 2 (A.glueL f) := A.glueL_smooth (n := 2) hf
  have hnhds : (A.chart i).U ∈ 𝓝 x := (A.chart i).isOpen.mem_nhds hx
  unfold glueΓ₂
  rw [A.glueL_indep hΦ i hx, A.glueΓ_indep (Smooth.mono A (by norm_num) hf) hΨ i hx]
  congr 1
  · congr 1
    refine Lch_congr_eventually ?_
    filter_upwards [hnhds] with y hy
    exact A.glueΓ_indep (Smooth.mono A (by norm_num) hf) (Smooth.mono A (by norm_num) hf) i hy
  · refine Gch_congr_eventually (Filter.EventuallyEq.refl _ _) ?_
    filter_upwards [hnhds] with y hy
    exact A.glueL_indep (Smooth.mono A (by norm_num) hf) i hy

end Atlas

end MarkovTriple.BGL.Instances.Riemannian.R27
