import Mathlib
import MarkovTriple.BGL.Theory.GammaCalculus
import MarkovTriple.BGL.Theory.ALevel
import MarkovTriple.BGL.Theory.Gamma2Integral
import MarkovTriple.BGL.Frozen.CD

/-!
# Second-order calculus on the extended algebra `𝒜` of a full triple (from F3–F6)

Everything here is a.e. and uses only the change-of-variables formulas F6 with `k = 2` and the definition
`Γ(f,g) = ½(L(fg) − fLg − gLf)`:

* `L` is a.e. linear on `𝒜`, `L(const) = 0`;
* `Γ(hk, g) = hΓ(k,g) + kΓ(h,g)`;
* the Hessian product rule (BGL (3.3.4)):
  `Γ₂(hk, g) = hΓ₂(k,g) + kΓ₂(h,g) + Γ(h,Γ(k,g)) + Γ(k,Γ(h,g)) − Γ(g,Γ(h,k))`.
-/

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

namespace MarkovTriple.BGL

variable {E : Type*} [MeasurableSpace E]

namespace FullTriple

variable (T : FullTriple E)

/-- local notation for the carré du champ on `𝒜`. -/
noncomputable abbrev G (f g : E → ℝ) : E → ℝ := T.toDiffusionTriple.ΓA f g

section pd

lemma pderiv_prod0 (z : Fin 2 → ℝ) :
    pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 0 z = z 1 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 * z 1)
      (z 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 +
        z 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).mul (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z)
  unfold pderiv
  rw [hd.fderiv]
  simp

lemma pderiv_prod1 (z : Fin 2 → ℝ) :
    pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 1 z = z 0 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 * z 1)
      (z 0 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1 +
        z 1 • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).mul (hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z)
  unfold pderiv
  rw [hd.fderiv]
  simp

lemma pderiv_lin0 (s : ℝ) (z : Fin 2 → ℝ) :
    pderiv (fun z : Fin 2 → ℝ => z 0 + s * z 1) 0 z = 1 := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 + s * z 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
        s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z).const_mul s)
  unfold pderiv
  rw [hd.fderiv]
  simp

lemma pderiv_lin1 (s : ℝ) (z : Fin 2 → ℝ) :
    pderiv (fun z : Fin 2 → ℝ => z 0 + s * z 1) 1 z = s := by
  have hd : HasFDerivAt (fun z : Fin 2 → ℝ => z 0 + s * z 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 +
        s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) z :=
    (hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z).add
      ((hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z).const_mul s)
  unfold pderiv
  rw [hd.fderiv]
  simp

lemma pderiv2_lin (s : ℝ) (i j : Fin 2) (z : Fin 2 → ℝ) :
    pderiv₂ (fun z : Fin 2 → ℝ => z 0 + s * z 1) i j z = 0 := by
  unfold pderiv₂
  have : (fun y : Fin 2 → ℝ => pderiv (fun z : Fin 2 → ℝ => z 0 + s * z 1) i y) =
      fun _ => if i = 0 then 1 else s := by
    funext y
    fin_cases i
    · simp [pderiv_lin0]
    · simp [pderiv_lin1]
  rw [this]
  simp

lemma pderiv2_prod_00 (z : Fin 2 → ℝ) :
    pderiv₂ (fun z : Fin 2 → ℝ => z 0 * z 1) 0 0 z = 0 := by
  unfold pderiv₂
  have : (fun y : Fin 2 → ℝ => pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 0 y) = fun y => y 1 := by
    funext y; exact pderiv_prod0 y
  rw [this]
  have hd : HasFDerivAt (fun y : Fin 2 → ℝ => y 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) z :=
    hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z
  rw [hd.fderiv]
  simp

lemma pderiv2_prod_01 (z : Fin 2 → ℝ) :
    pderiv₂ (fun z : Fin 2 → ℝ => z 0 * z 1) 0 1 z = 1 := by
  unfold pderiv₂
  have : (fun y : Fin 2 → ℝ => pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 0 y) = fun y => y 1 := by
    funext y; exact pderiv_prod0 y
  rw [this]
  have hd : HasFDerivAt (fun y : Fin 2 → ℝ => y 1)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1) z :=
    hasFDerivAt_apply (𝕜 := ℝ) (1 : Fin 2) z
  rw [hd.fderiv]
  simp

lemma pderiv2_prod_10 (z : Fin 2 → ℝ) :
    pderiv₂ (fun z : Fin 2 → ℝ => z 0 * z 1) 1 0 z = 1 := by
  unfold pderiv₂
  have : (fun y : Fin 2 → ℝ => pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 1 y) = fun y => y 0 := by
    funext y; exact pderiv_prod1 y
  rw [this]
  have hd : HasFDerivAt (fun y : Fin 2 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z :=
    hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z
  rw [hd.fderiv]
  simp

lemma pderiv2_prod_11 (z : Fin 2 → ℝ) :
    pderiv₂ (fun z : Fin 2 → ℝ => z 0 * z 1) 1 1 z = 0 := by
  unfold pderiv₂
  have : (fun y : Fin 2 → ℝ => pderiv (fun z : Fin 2 → ℝ => z 0 * z 1) 1 y) = fun y => y 0 := by
    funext y; exact pderiv_prod1 y
  rw [this]
  have hd : HasFDerivAt (fun y : Fin 2 → ℝ => y 0)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0) z :=
    hasFDerivAt_apply (𝕜 := ℝ) (0 : Fin 2) z
  rw [hd.fderiv]
  simp

end pd

variable {T}

lemma contDiff_lin (s : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 2 → ℝ => z 0 + s * z 1) :=
  (contDiff_apply ℝ ℝ 0).add (contDiff_const.mul (contDiff_apply ℝ ℝ 1))

lemma contDiff_prod : ContDiff ℝ (⊤ : ℕ∞) (fun z : Fin 2 → ℝ => z 0 * z 1) :=
  (contDiff_apply ℝ ℝ 0).mul (contDiff_apply ℝ ℝ 1)

lemma mem2 {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) :
    ∀ i, (![f, g] : Fin 2 → E → ℝ) i ∈ T.A := by
  intro i; fin_cases i <;> simpa

/-- `L (f + s g) = L f + s L g` a.e. on `𝒜`. -/
theorem L_lin {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (s : ℝ) :
    T.L (fun x => f x + s * g x) =ᵐ[T.μ] fun x => T.L f x + s * T.L g x := by
  have key := T.diffusion_L_A 2 (fun z : Fin 2 → ℝ => z 0 + s * z 1) (contDiff_lin s) ![f, g]
    (mem2 hf hg)
  have e : (fun x => (fun z : Fin 2 → ℝ => z 0 + s * z 1) (fun i => (![f, g] : Fin 2 → E → ℝ) i x))
      = fun x => f x + s * g x := by funext x; simp
  rw [e] at key
  filter_upwards [key] with x hx
  rw [hx]
  simp [Fin.sum_univ_two, pderiv_lin0, pderiv_lin1, pderiv2_lin]

/-- `L (c) = 0` for constants. -/
theorem L_const (c : ℝ) : T.L (fun _ => c) =ᵐ[T.μ] 0 := by
  have key := T.diffusion_L_A 0 (fun _ => c) contDiff_const (fun i => i.elim0) (fun i => i.elim0)
  filter_upwards [key] with x hx
  simpa using hx

/-- `L(hk) = h Lk + k Lh + 2 Γ(h,k)`, exactly (definition of `ΓA`). -/
lemma L_mul_eq (h k : E → ℝ) (x : E) :
    T.L (h * k) x = h x * T.L k x + k x * T.L h x + 2 * G T h k x := by
  simp only [G, DiffusionTriple.ΓA]; ring

lemma G_comm (f g : E → ℝ) : G T f g = G T g f := DiffusionTriple.ΓA_comm T.toDiffusionTriple f g

/-- `Γ(h k, g) = h Γ(k,g) + k Γ(h,g)` a.e. -/
theorem G_mul_left {h k g : E → ℝ} (hh : h ∈ T.A) (hk : k ∈ T.A) (hg : g ∈ T.A) :
    G T (h * k) g =ᵐ[T.μ] fun x => h x * G T k g x + k x * G T h g x := by
  have key := T.diffusion_Γ_A 2 (fun z : Fin 2 → ℝ => z 0 * z 1) contDiff_prod ![h, k]
    (mem2 hh hk) g hg
  have e : (fun x => (fun z : Fin 2 → ℝ => z 0 * z 1) (fun i => (![h, k] : Fin 2 → E → ℝ) i x))
      = h * k := by funext x; simp
  rw [e] at key
  filter_upwards [key] with x hx
  refine hx.trans ?_
  simp [Fin.sum_univ_two, pderiv_prod0, pderiv_prod1]
  ring

/-- additivity / homogeneity of `Γ` in the first slot, in the `f + s g` form. -/
theorem G_lin_left {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (s : ℝ) {k : E → ℝ} (hk : k ∈ T.A) :
    G T (fun x => f x + s * g x) k =ᵐ[T.μ] fun x => G T f k x + s * G T g k x := by
  have key := T.diffusion_Γ_A 2 (fun z : Fin 2 → ℝ => z 0 + s * z 1) (contDiff_lin s) ![f, g]
    (mem2 hf hg) k hk
  have e : (fun x => (fun z : Fin 2 → ℝ => z 0 + s * z 1) (fun i => (![f, g] : Fin 2 → E → ℝ) i x))
      = fun x => f x + s * g x := by funext x; simp
  rw [e] at key
  filter_upwards [key] with x hx
  refine hx.trans ?_
  simp [Fin.sum_univ_two, pderiv_lin0, pderiv_lin1]


/-- membership: products, `L`, `Γ` stay in `𝒜`. -/
lemma G_mem {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) : G T f g ∈ T.A :=
  FullTriple.ΓA_mem_A T hf hg

lemma L_memA {f : E → ℝ} (hf : f ∈ T.A) : T.L f ∈ T.A := T.L_mem_A f hf

lemma L_add {f g : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) :
    T.L (f + g) =ᵐ[T.μ] fun x => T.L f x + T.L g x := by
  have e : (f + g) = fun x => f x + 1 * g x := by funext x; simp
  rw [e]
  filter_upwards [L_lin hf hg 1] with x hx
  simpa using hx

/-- `Γ(f + g, k) = Γ(f,k) + Γ(g,k)`. -/
lemma G_add_left {f g k : E → ℝ} (hf : f ∈ T.A) (hg : g ∈ T.A) (hk : k ∈ T.A) :
    G T (f + g) k =ᵐ[T.μ] fun x => G T f k x + G T g k x := by
  have e : (f + g) = fun x => f x + 1 * g x := by funext x; simp
  rw [e]
  filter_upwards [G_lin_left hf hg 1 hk] with x hx
  simpa using hx

/-- `Γ(f + c g, k)` in function form. -/
lemma G_const_left (c : ℝ) {k : E → ℝ} (hk : k ∈ T.A) : G T (fun _ => c) k =ᵐ[T.μ] 0 := by
  have key := T.diffusion_Γ_A 0 (fun _ => c) contDiff_const (fun i => i.elim0) (fun i => i.elim0) k hk
  filter_upwards [key] with x hx
  simpa using hx

/-- `Γ(c f, k) = c Γ(f,k)`. -/
lemma G_smul_left {f k : E → ℝ} (hf : f ∈ T.A) (hk : k ∈ T.A) (c : ℝ) :
    G T (c • f) k =ᵐ[T.μ] fun x => c * G T f k x := by
  have h0 : (fun _ : E => (0 : ℝ)) ∈ T.A := T.A.algebraMap_mem 0
  have e : (c • f) = fun x => 0 + c * f x := by funext x; simp
  rw [e]
  filter_upwards [G_lin_left h0 hf c hk, G_const_left (T := T) 0 hk] with x hx h1x
  refine hx.trans ?_
  simp only [Pi.zero_apply] at h1x
  rw [h1x]; ring

lemma Γ₂_eq (f g : E → ℝ) (x : E) :
    T.toDiffusionTriple.Γ₂ f g x =
      (T.L (G T f g) x - G T f (T.L g) x - G T (T.L f) g x) / 2 := rfl

/-- **Hessian product rule** (BGL (3.3.4)):
`Γ₂(hk, g) = hΓ₂(k,g) + kΓ₂(h,g) + Γ(h,Γ(k,g)) + Γ(k,Γ(h,g)) − Γ(g,Γ(h,k))` a.e. -/
theorem Γ₂_mul_left {h k g : E → ℝ} (hh : h ∈ T.A) (hk : k ∈ T.A) (hg : g ∈ T.A) :
    T.toDiffusionTriple.Γ₂ (h * k) g =ᵐ[T.μ] fun x =>
      h x * T.toDiffusionTriple.Γ₂ k g x + k x * T.toDiffusionTriple.Γ₂ h g x +
        G T h (G T k g) x + G T k (G T h g) x - G T g (G T h k) x := by
  have m1 : G T k g ∈ T.A := G_mem hk hg
  have m2 : G T h g ∈ T.A := G_mem hh hg
  have hm : h * k ∈ T.A := T.A.mul_mem hh hk
  have hLg : T.L g ∈ T.A := L_memA hg
  have hLk : T.L k ∈ T.A := L_memA hk
  have hLh : T.L h ∈ T.A := L_memA hh
  have hhk : G T h k ∈ T.A := G_mem hh hk
  have a1 : G T (h * k) g =ᵐ[T.μ] fun x => h x * G T k g x + k x * G T h g x :=
    G_mul_left hh hk hg
  have hsum : (h * G T k g + k * G T h g) ∈ T.A :=
    T.A.add_mem (T.A.mul_mem hh m1) (T.A.mul_mem hk m2)
  have a1' : G T (h * k) g =ᵐ[T.μ] (h * G T k g + k * G T h g) := by
    filter_upwards [a1] with x hx; simpa using hx
  have a2 : T.L (G T (h * k) g) =ᵐ[T.μ] T.L (h * G T k g + k * G T h g) :=
    L_congr_A T (G_mem hm hg) hsum a1'
  have a3 : T.L (h * G T k g + k * G T h g) =ᵐ[T.μ]
      fun x => T.L (h * G T k g) x + T.L (k * G T h g) x :=
    L_add (T.A.mul_mem hh m1) (T.A.mul_mem hk m2)
  have a4 : G T (h * k) (T.L g) =ᵐ[T.μ] fun x => h x * G T k (T.L g) x + k x * G T h (T.L g) x :=
    G_mul_left hh hk hLg
  have eL : T.L (h * k) = (h * T.L k + k * T.L h) + (2 : ℝ) • G T h k := by
    funext x; simp only [Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    rw [L_mul_eq]
  have p1 : h * T.L k ∈ T.A := T.A.mul_mem hh hLk
  have p2 : k * T.L h ∈ T.A := T.A.mul_mem hk hLh
  have p12 : h * T.L k + k * T.L h ∈ T.A := T.A.add_mem p1 p2
  have b1 : G T (T.L (h * k)) g =ᵐ[T.μ] fun x => G T (h * T.L k + k * T.L h) g x +
      2 * G T (G T h k) g x := by
    rw [eL]
    have e : ((h * T.L k + k * T.L h) + (2 : ℝ) • G T h k) =
        fun x => (h * T.L k + k * T.L h) x + 2 * G T h k x := by
      funext x; simp
    rw [e]
    exact G_lin_left p12 hhk 2 hg
  have b2 : G T (h * T.L k + k * T.L h) g =ᵐ[T.μ]
      fun x => G T (h * T.L k) g x + G T (k * T.L h) g x :=
    G_add_left p1 p2 hg
  have b3 : G T (h * T.L k) g =ᵐ[T.μ] fun x => h x * G T (T.L k) g x + T.L k x * G T h g x :=
    G_mul_left hh hLk hg
  have b4 : G T (k * T.L h) g =ᵐ[T.μ] fun x => k x * G T (T.L h) g x + T.L h x * G T k g x :=
    G_mul_left hk hLh hg
  filter_upwards [a1, a2, a3, a4, b1, b2, b3, b4] with x e1 e2 e3 e4 f1 f2 f3 f4
  have c1 := L_mul_eq (T := T) h (G T k g) x
  have c2 := L_mul_eq (T := T) k (G T h g) x
  rw [Γ₂_eq, Γ₂_eq, Γ₂_eq]
  rw [e2, e3, e4, f1, f2, f3, f4, c1, c2]
  have g1 : G T g (G T h k) x = G T (G T h k) g x := by rw [G_comm]
  have g2 : G T (G T k g) h x = G T h (G T k g) x := by rw [G_comm]
  have g3 : G T (T.L k) g x = G T g (T.L k) x := by rw [G_comm]
  rw [g1]
  ring

end FullTriple

end MarkovTriple.BGL
