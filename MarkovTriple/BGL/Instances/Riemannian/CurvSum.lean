import Mathlib

/-!
# Finite-sum reindexing helpers (index gymnastics for tensor identities)

`p3_*`, `p4_*`: all permutations of the order of a nested triple/quadruple sum over `Fin d`
(`p3_bca : ∑ a, ∑ b, ∑ c, F a b c = ∑ b, ∑ c, ∑ a, F a b c`, etc.), and the tactics `sums2`, `sums3`, `sums4`
closing `∑∑∑ f = ∑∑∑ f'` when the two sides agree after a permutation of the summation order and `ring` on the bodies.
-/

namespace MarkovTriple.BGL.Instances.Riemannian

variable {d : ℕ}

lemma sw2 (F : Fin d → Fin d → ℝ) : ∑ a, ∑ b, F a b = ∑ b, ∑ a, F a b := Finset.sum_comm

lemma s3a (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ b, ∑ a, ∑ c, F a b c := Finset.sum_comm

lemma s3b (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c = ∑ a, ∑ c, ∑ b, F a b c :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma s4a (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ b, ∑ a, ∑ c, ∑ e, F a b c e := Finset.sum_comm

lemma s4b (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ a, ∑ c, ∑ b, ∑ e, F a b c e :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma s4c (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e = ∑ a, ∑ b, ∑ e, ∑ c, F a b c e :=
  Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm

lemma p3_bac (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c =
    ∑ b, ∑ a, ∑ c, F a b c :=
  (s3a (fun x0 x1 x2 => F x0 x1 x2))

lemma p3_acb (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c =
    ∑ a, ∑ c, ∑ b, F a b c :=
  (s3b (fun x0 x1 x2 => F x0 x1 x2))

lemma p3_bca (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c =
    ∑ b, ∑ c, ∑ a, F a b c :=
  ((s3a (fun x0 x1 x2 => F x0 x1 x2))).trans (s3b (fun x0 x1 x2 => F x1 x0 x2))

lemma p3_cab (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c =
    ∑ c, ∑ a, ∑ b, F a b c :=
  ((s3b (fun x0 x1 x2 => F x0 x1 x2))).trans (s3a (fun x0 x1 x2 => F x0 x2 x1))

lemma p3_cba (F : Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, F a b c =
    ∑ c, ∑ b, ∑ a, F a b c :=
  (((s3a (fun x0 x1 x2 => F x0 x1 x2))).trans (s3b (fun x0 x1 x2 => F x1 x0 x2))).trans (s3a (fun x0 x1 x2 => F x2 x0 x1))

lemma p4_bace (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ b, ∑ a, ∑ c, ∑ e, F a b c e :=
  (s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))

lemma p4_acbe (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ a, ∑ c, ∑ b, ∑ e, F a b c e :=
  (s4b (fun x0 x1 x2 x3 => F x0 x1 x2 x3))

lemma p4_abec (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ a, ∑ b, ∑ e, ∑ c, F a b c e :=
  (s4c (fun x0 x1 x2 x3 => F x0 x1 x2 x3))

lemma p4_bcae (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ b, ∑ c, ∑ a, ∑ e, F a b c e :=
  ((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x2 x3))

lemma p4_baec (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ b, ∑ a, ∑ e, ∑ c, F a b c e :=
  ((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x1 x0 x2 x3))

lemma p4_cabe (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ c, ∑ a, ∑ b, ∑ e, F a b c e :=
  ((s4b (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4a (fun x0 x1 x2 x3 => F x0 x2 x1 x3))

lemma p4_aceb (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ a, ∑ c, ∑ e, ∑ b, F a b c e :=
  ((s4b (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x0 x2 x1 x3))

lemma p4_aebc (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ a, ∑ e, ∑ b, ∑ c, F a b c e :=
  ((s4c (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x0 x1 x3 x2))

lemma p4_cbae (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ c, ∑ b, ∑ a, ∑ e, F a b c e :=
  (((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4a (fun x0 x1 x2 x3 => F x2 x0 x1 x3))

lemma p4_bcea (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ b, ∑ c, ∑ e, ∑ a, F a b c e :=
  (((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x2 x0 x1 x3))

lemma p4_beac (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ b, ∑ e, ∑ a, ∑ c, F a b c e :=
  (((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x3 x2))

lemma p4_caeb (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ c, ∑ a, ∑ e, ∑ b, F a b c e :=
  (((s4b (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4a (fun x0 x1 x2 x3 => F x0 x2 x1 x3))).trans (s4c (fun x0 x1 x2 x3 => F x1 x2 x0 x3))

lemma p4_aecb (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ a, ∑ e, ∑ c, ∑ b, F a b c e :=
  (((s4b (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x0 x2 x1 x3))).trans (s4b (fun x0 x1 x2 x3 => F x0 x3 x1 x2))

lemma p4_eabc (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ e, ∑ a, ∑ b, ∑ c, F a b c e :=
  (((s4c (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x0 x1 x3 x2))).trans (s4a (fun x0 x1 x2 x3 => F x0 x2 x3 x1))

lemma p4_cbea (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ c, ∑ b, ∑ e, ∑ a, F a b c e :=
  ((((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4a (fun x0 x1 x2 x3 => F x2 x0 x1 x3))).trans (s4c (fun x0 x1 x2 x3 => F x2 x1 x0 x3))

lemma p4_beca (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ b, ∑ e, ∑ c, ∑ a, F a b c e :=
  ((((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x2 x0 x1 x3))).trans (s4b (fun x0 x1 x2 x3 => F x3 x0 x1 x2))

lemma p4_ebac (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ e, ∑ b, ∑ a, ∑ c, F a b c e :=
  ((((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x3 x2))).trans (s4a (fun x0 x1 x2 x3 => F x2 x0 x3 x1))

lemma p4_ceab (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ c, ∑ e, ∑ a, ∑ b, F a b c e :=
  ((((s4b (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4a (fun x0 x1 x2 x3 => F x0 x2 x1 x3))).trans (s4c (fun x0 x1 x2 x3 => F x1 x2 x0 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x3 x0 x2))

lemma p4_eacb (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ e, ∑ a, ∑ c, ∑ b, F a b c e :=
  ((((s4b (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x0 x2 x1 x3))).trans (s4b (fun x0 x1 x2 x3 => F x0 x3 x1 x2))).trans (s4a (fun x0 x1 x2 x3 => F x0 x3 x2 x1))

lemma p4_ceba (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ c, ∑ e, ∑ b, ∑ a, F a b c e :=
  (((((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4a (fun x0 x1 x2 x3 => F x2 x0 x1 x3))).trans (s4c (fun x0 x1 x2 x3 => F x2 x1 x0 x3))).trans (s4b (fun x0 x1 x2 x3 => F x3 x1 x0 x2))

lemma p4_ebca (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ e, ∑ b, ∑ c, ∑ a, F a b c e :=
  (((((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4c (fun x0 x1 x2 x3 => F x2 x0 x1 x3))).trans (s4b (fun x0 x1 x2 x3 => F x3 x0 x1 x2))).trans (s4a (fun x0 x1 x2 x3 => F x3 x0 x2 x1))

lemma p4_ecab (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ e, ∑ c, ∑ a, ∑ b, F a b c e :=
  (((((s4b (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4a (fun x0 x1 x2 x3 => F x0 x2 x1 x3))).trans (s4c (fun x0 x1 x2 x3 => F x1 x2 x0 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x3 x0 x2))).trans (s4a (fun x0 x1 x2 x3 => F x2 x3 x0 x1))

lemma p4_ecba (F : Fin d → Fin d → Fin d → Fin d → ℝ) :
    ∑ a, ∑ b, ∑ c, ∑ e, F a b c e =
    ∑ e, ∑ c, ∑ b, ∑ a, F a b c e :=
  ((((((s4a (fun x0 x1 x2 x3 => F x0 x1 x2 x3))).trans (s4b (fun x0 x1 x2 x3 => F x1 x0 x2 x3))).trans (s4a (fun x0 x1 x2 x3 => F x2 x0 x1 x3))).trans (s4c (fun x0 x1 x2 x3 => F x2 x1 x0 x3))).trans (s4b (fun x0 x1 x2 x3 => F x3 x1 x0 x2))).trans (s4a (fun x0 x1 x2 x3 => F x3 x2 x0 x1))


open Lean in
/-- close `∑ a, ∑ b, f a b = ∑ x, ∑ y, g x y` up to commuting the two sums and `ring` on the bodies -/
macro "sums2" : tactic =>
  `(tactic| first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (sw2 _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1))

open Lean in
macro "sums3" : tactic =>
  `(tactic| first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p3_bac _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p3_acb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p3_bca _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p3_cab _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p3_cba _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1))

open Lean in
macro "sums4" : tactic =>
  `(tactic| first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_bace _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_acbe _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_abec _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_bcae _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_baec _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_cabe _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_aceb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_aebc _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_cbae _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_bcea _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_beac _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_caeb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_aecb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_eabc _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_cbea _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_beca _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_ebac _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_ceab _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_eacb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_ceba _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_ebca _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_ecab _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1)
    | (refine (p4_ecba _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; ring1))

open Lean in
macro "sums3s" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p3_bac _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p3_acb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p3_bca _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p3_cab _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p3_cba _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1))

open Lean in
macro "sums4s" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_bace _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_acbe _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_abec _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_bcae _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_baec _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_cabe _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_aceb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_aebc _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_cbae _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_bcea _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_beac _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_caeb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_aecb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_eabc _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_cbea _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_beca _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_ebac _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_ceab _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_eacb _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_ceba _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_ebca _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_ecab _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (p4_ecba _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1))

open Lean in
macro "sums2s" "[" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| first
    | (refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1)
    | (refine (sw2 _).trans ?_; refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_; (try simp only [$ls,*]) <;> ring1))

end MarkovTriple.BGL.Instances.Riemannian
