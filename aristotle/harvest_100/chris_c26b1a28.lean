import Mathlib
import RequestProject.Jones

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# The Kauffman bracket / Jones polynomial of braid closures (3-strand case)

This file develops, from scratch, a concrete algebraic model of the Kauffman bracket
state sum for closures of braids on at most three strands, via the Temperley–Lieb
algebras `TL₂` and `TL₃`, and proves that the writhe-normalised bracket
(the Jones polynomial, up to the substitution `A = t^{-1/4}`) is invariant under the
Reidemeister moves that are visible in this setting:

* Reidemeister II  : cancelling a pair `σᵢ σᵢ⁻¹` (or `σᵢ⁻¹ σᵢ`) anywhere in the braid word;
* Reidemeister III : the braid relation `σ₁σ₂σ₁ = σ₂σ₁σ₂` (and its negative version);
* Reidemeister I   : Markov stabilisation, `closure (ι w · σ₂^{±1}) = closure w`.

Everything takes place over an arbitrary commutative ring `R` with two elements
`A B : R` satisfying `A * B = 1` (so `B = A⁻¹`), and `δ = -A² - B²` is the loop value.
-/

namespace Frontier

/-! ## The Temperley–Lieb algebra `TL₃` -/

/-- An element of the Temperley–Lieb algebra `TL₃` over `R`, written in the standard
diagram basis `1, e₁, e₂, e₁e₂, e₂e₁`. -/
@[ext]
structure TL3 (R : Type*) where
  c1 : R
  ce1 : R
  ce2 : R
  ce12 : R
  ce21 : R

/-- An element of the Temperley–Lieb algebra `TL₂` over `R`, written in the standard
diagram basis `1, e₁`. -/
@[ext]
structure TL2 (R : Type*) where
  c1 : R
  ce1 : R

variable {R : Type*} [CommRing R]

/-- The loop value `δ = -A² - A⁻²` of the Kauffman bracket. -/
def delta (A B : R) : R := -A ^ 2 - B ^ 2

/-- The identity element of `TL₃`. -/
def TL3.one (R : Type*) [CommRing R] : TL3 R := ⟨1, 0, 0, 0, 0⟩

/-- The identity element of `TL₂`. -/
def TL2.one (R : Type*) [CommRing R] : TL2 R := ⟨1, 0⟩

/-- Right multiplication by the Temperley–Lieb generator `e₁` in `TL₃`. -/
def TL3.mulE1 (A B : R) (x : TL3 R) : TL3 R :=
  ⟨0, x.c1 + delta A B * x.ce1 + x.ce12, 0, 0, x.ce2 + delta A B * x.ce21⟩

/-- Right multiplication by the Temperley–Lieb generator `e₂` in `TL₃`. -/
def TL3.mulE2 (A B : R) (x : TL3 R) : TL3 R :=
  ⟨0, 0, x.c1 + delta A B * x.ce2 + x.ce21, x.ce1 + delta A B * x.ce12, 0⟩

/-- Right multiplication by the Temperley–Lieb generator `e₁` in `TL₂`. -/
def TL2.mulE1 (A B : R) (x : TL2 R) : TL2 R :=
  ⟨0, x.c1 + delta A B * x.ce1⟩

/-- A letter of a `3`-braid word: the first component selects the generator
(`false ↦ σ₁`, `true ↦ σ₂`), the second component is the sign of the crossing. -/
abbrev Letter := Bool × Bool

/-- The Kauffman smoothing action of a braid letter on `TL₃`:
`σᵢ ↦ A + A⁻¹ eᵢ`, `σᵢ⁻¹ ↦ A⁻¹ + A eᵢ` (acting by right multiplication). -/
def TL3.act (A B : R) (l : Letter) (x : TL3 R) : TL3 R :=
  let a : R := if l.2 then A else B
  let b : R := if l.2 then B else A
  let y : TL3 R := if l.1 then TL3.mulE2 A B x else TL3.mulE1 A B x
  ⟨a * x.c1 + b * y.c1, a * x.ce1 + b * y.ce1, a * x.ce2 + b * y.ce2,
    a * x.ce12 + b * y.ce12, a * x.ce21 + b * y.ce21⟩

/-- The Kauffman smoothing action of a signed crossing on `TL₂`. -/
def TL2.act (A B : R) (s : Bool) (x : TL2 R) : TL2 R :=
  let a : R := if s then A else B
  let b : R := if s then B else A
  let y : TL2 R := TL2.mulE1 A B x
  ⟨a * x.c1 + b * y.c1, a * x.ce1 + b * y.ce1⟩

/-- The Markov trace on `TL₃`: the Kauffman bracket of the closure of a diagram,
normalised so that the empty diagram has bracket `1` (hence a single circle has
bracket `δ`). -/
def TL3.tr (A B : R) (x : TL3 R) : R :=
  delta A B ^ 3 * x.c1 + delta A B ^ 2 * (x.ce1 + x.ce2) + delta A B * (x.ce12 + x.ce21)

/-- The Markov trace on `TL₂`. -/
def TL2.tr (A B : R) (x : TL2 R) : R :=
  delta A B ^ 2 * x.c1 + delta A B * x.ce1

/-- The Temperley–Lieb element of a `3`-braid word. -/
def tl3 (A B : R) (w : List Letter) : TL3 R :=
  w.foldl (fun x l => TL3.act A B l x) (TL3.one R)

/-- The Temperley–Lieb element of a `2`-braid word (a list of crossing signs). -/
def tl2 (A B : R) (w : List Bool) : TL2 R :=
  w.foldl (fun x s => TL2.act A B s x) (TL2.one R)

/-- The Kauffman bracket of the closure of a `3`-braid word. -/
def bracket3 (A B : R) (w : List Letter) : R := TL3.tr A B (tl3 A B w)

/-- The Kauffman bracket of the closure of a `2`-braid word. -/
def bracket2 (A B : R) (w : List Bool) : R := TL2.tr A B (tl2 A B w)

/-- The writhe normalisation factor `(-A³)^{-writhe}` of a `3`-braid word. -/
def normFactor3 (A B : R) (w : List Letter) : R :=
  (-B ^ 3) ^ (w.countP fun l => l.2) * (-A ^ 3) ^ (w.countP fun l => !l.2)

/-- The writhe normalisation factor `(-A³)^{-writhe}` of a `2`-braid word. -/
def normFactor2 (A B : R) (w : List Bool) : R :=
  (-B ^ 3) ^ (w.countP fun s => s) * (-A ^ 3) ^ (w.countP fun s => !s)

/-- The Jones polynomial (in Kauffman's variable `A`, and in the normalisation where
the unknot takes the value `δ`) of the closure of a `3`-braid word. -/
def jones3 (A B : R) (w : List Letter) : R := normFactor3 A B w * bracket3 A B w

/-- The Jones polynomial of the closure of a `2`-braid word. -/
def jones2 (A B : R) (w : List Bool) : R := normFactor2 A B w * bracket2 A B w

/-- The inclusion `B₂ → B₃` of braid words. -/
def incl (w : List Bool) : List Letter := w.map fun s => (false, s)


/-- The embedding `TL₂ → TL₃` induced by the inclusion of braid groups `B₂ → B₃`. -/
def TL3.ofTL2 (x : TL2 R) : TL3 R := ⟨x.c1, x.ce1, 0, 0, 0⟩

/-! ## Reidemeister II : cancellation of `σᵢ σᵢ⁻¹` -/

theorem TL3.act_cancel_pos_neg (A B : R) (hAB : A * B = 1) (i : Bool) (x : TL3 R) :
    TL3.act A B (i, false) (TL3.act A B (i, true) x) = x := by
  cases i <;> ext <;> simp [TL3.act, TL3.mulE1, TL3.mulE2, delta] <;> grind

theorem TL3.act_cancel_neg_pos (A B : R) (hAB : A * B = 1) (i : Bool) (x : TL3 R) :
    TL3.act A B (i, true) (TL3.act A B (i, false) x) = x := by
  cases i <;> ext <;> simp [TL3.act, TL3.mulE1, TL3.mulE2, delta] <;> grind

/-! ## Reidemeister III : the braid relation -/

set_option maxHeartbeats 4000000 in
theorem TL3.act_braid (A B : R) (hAB : A * B = 1) (s : Bool) (x : TL3 R) :
    TL3.act A B (false, s) (TL3.act A B (true, s) (TL3.act A B (false, s) x)) =
      TL3.act A B (true, s) (TL3.act A B (false, s) (TL3.act A B (true, s) x)) := by
  cases s <;> ext <;> simp [TL3.act, TL3.mulE1, TL3.mulE2, delta] <;> grind

/-! ## Basic fold lemmas -/

theorem tl3_append (A B : R) (w₁ w₂ : List Letter) :
    tl3 A B (w₁ ++ w₂) = w₂.foldl (fun x l => TL3.act A B l x) (tl3 A B w₁) := by
  simp [tl3, List.foldl_append]

theorem tl3_foldl_congr (A B : R) (x y : TL3 R) (h : x = y) (w : List Letter) :
    w.foldl (fun x l => TL3.act A B l x) x = w.foldl (fun x l => TL3.act A B l x) y := by
  rw [h]

/-! ## Invariance of the Temperley–Lieb element -/

theorem tl3_R2_pos (A B : R) (hAB : A * B = 1) (i : Bool) (w₁ w₂ : List Letter) :
    tl3 A B (w₁ ++ (i, true) :: (i, false) :: w₂) = tl3 A B (w₁ ++ w₂) := by
  rw [tl3_append, tl3_append]
  refine tl3_foldl_congr A B _ _ ?_ w₂
  simp [TL3.act_cancel_pos_neg A B hAB i]

theorem tl3_R2_neg (A B : R) (hAB : A * B = 1) (i : Bool) (w₁ w₂ : List Letter) :
    tl3 A B (w₁ ++ (i, false) :: (i, true) :: w₂) = tl3 A B (w₁ ++ w₂) := by
  rw [tl3_append, tl3_append]
  refine tl3_foldl_congr A B _ _ ?_ w₂
  simp [TL3.act_cancel_neg_pos A B hAB i]

theorem tl3_R3 (A B : R) (hAB : A * B = 1) (s : Bool) (w₁ w₂ : List Letter) :
    tl3 A B (w₁ ++ (false, s) :: (true, s) :: (false, s) :: w₂) =
      tl3 A B (w₁ ++ (true, s) :: (false, s) :: (true, s) :: w₂) := by
  rw [tl3_append, tl3_append]
  refine tl3_foldl_congr A B _ _ ?_ w₂
  simpa using TL3.act_braid A B hAB s (tl3 A B w₁)

/-! ## Invariance of the writhe normalisation -/

theorem neg_pow_three_mul (A B : R) (hAB : A * B = 1) : (-B ^ 3) * (-A ^ 3) = 1 := by
  have h : (-B ^ 3) * (-A ^ 3) = (A * B) ^ 3 := by ring
  rw [h, hAB, one_pow]

theorem normFactor3_R2_pos (A B : R) (hAB : A * B = 1) (i : Bool) (w₁ w₂ : List Letter) :
    normFactor3 A B (w₁ ++ (i, true) :: (i, false) :: w₂) = normFactor3 A B (w₁ ++ w₂) := by
  have h1 : (w₁ ++ (i, true) :: (i, false) :: w₂).countP (fun l => l.2)
      = (w₁ ++ w₂).countP (fun l => l.2) + 1 := by
    simp [List.countP_append]
    omega
  have h2 : (w₁ ++ (i, true) :: (i, false) :: w₂).countP (fun l => !l.2)
      = (w₁ ++ w₂).countP (fun l => !l.2) + 1 := by
    simp [List.countP_append]
    omega
  rw [normFactor3, normFactor3, h1, h2, pow_succ (-B ^ 3), pow_succ (-A ^ 3)]
  calc (-B ^ 3) ^ (w₁ ++ w₂).countP (fun l => l.2) * (-B ^ 3) *
        ((-A ^ 3) ^ (w₁ ++ w₂).countP (fun l => !l.2) * (-A ^ 3))
      = ((-B ^ 3) ^ (w₁ ++ w₂).countP (fun l => l.2) *
          (-A ^ 3) ^ (w₁ ++ w₂).countP (fun l => !l.2)) * ((-B ^ 3) * (-A ^ 3)) := by ring
    _ = _ := by rw [neg_pow_three_mul A B hAB, mul_one]

theorem normFactor3_R2_neg (A B : R) (hAB : A * B = 1) (i : Bool) (w₁ w₂ : List Letter) :
    normFactor3 A B (w₁ ++ (i, false) :: (i, true) :: w₂) = normFactor3 A B (w₁ ++ w₂) := by
  have h1 : (w₁ ++ (i, false) :: (i, true) :: w₂).countP (fun l => l.2)
      = (w₁ ++ w₂).countP (fun l => l.2) + 1 := by
    simp [List.countP_append]
    omega
  have h2 : (w₁ ++ (i, false) :: (i, true) :: w₂).countP (fun l => !l.2)
      = (w₁ ++ w₂).countP (fun l => !l.2) + 1 := by
    simp [List.countP_append]
    omega
  rw [normFactor3, normFactor3, h1, h2, pow_succ (-B ^ 3), pow_succ (-A ^ 3)]
  calc (-B ^ 3) ^ (w₁ ++ w₂).countP (fun l => l.2) * (-B ^ 3) *
        ((-A ^ 3) ^ (w₁ ++ w₂).countP (fun l => !l.2) * (-A ^ 3))
      = ((-B ^ 3) ^ (w₁ ++ w₂).countP (fun l => l.2) *
          (-A ^ 3) ^ (w₁ ++ w₂).countP (fun l => !l.2)) * ((-B ^ 3) * (-A ^ 3)) := by ring
    _ = _ := by rw [neg_pow_three_mul A B hAB, mul_one]

theorem normFactor3_R3 (A B : R) (s : Bool) (w₁ w₂ : List Letter) :
    normFactor3 A B (w₁ ++ (false, s) :: (true, s) :: (false, s) :: w₂) =
      normFactor3 A B (w₁ ++ (true, s) :: (false, s) :: (true, s) :: w₂) := by
  simp only [normFactor3, List.countP_append, List.countP_cons]

/-! ## The Jones polynomial is invariant under R2 and R3 -/

theorem jones3_R2_pos (A B : R) (hAB : A * B = 1) (i : Bool) (w₁ w₂ : List Letter) :
    jones3 A B (w₁ ++ (i, true) :: (i, false) :: w₂) = jones3 A B (w₁ ++ w₂) := by
  simp only [jones3, bracket3, normFactor3_R2_pos A B hAB i w₁ w₂, tl3_R2_pos A B hAB i w₁ w₂]

theorem jones3_R2_neg (A B : R) (hAB : A * B = 1) (i : Bool) (w₁ w₂ : List Letter) :
    jones3 A B (w₁ ++ (i, false) :: (i, true) :: w₂) = jones3 A B (w₁ ++ w₂) := by
  simp only [jones3, bracket3, normFactor3_R2_neg A B hAB i w₁ w₂, tl3_R2_neg A B hAB i w₁ w₂]

theorem jones3_R3 (A B : R) (hAB : A * B = 1) (s : Bool) (w₁ w₂ : List Letter) :
    jones3 A B (w₁ ++ (false, s) :: (true, s) :: (false, s) :: w₂) =
      jones3 A B (w₁ ++ (true, s) :: (false, s) :: (true, s) :: w₂) := by
  simp only [jones3, bracket3, normFactor3_R3 A B s w₁ w₂, tl3_R3 A B hAB s w₁ w₂]

/-! ## Reidemeister I : Markov stabilisation -/

theorem TL3.act_ofTL2 (A B : R) (s : Bool) (x : TL2 R) :
    TL3.act A B (false, s) (TL3.ofTL2 x) = TL3.ofTL2 (TL2.act A B s x) := by
  cases s <;> ext <;> simp [TL3.act, TL2.act, TL3.mulE1, TL2.mulE1, TL3.ofTL2, delta]

theorem incl_cons (s : Bool) (w : List Bool) : incl (s :: w) = (false, s) :: incl w := rfl

theorem tl3_incl_aux (A B : R) (w : List Bool) (x : TL2 R) :
    (incl w).foldl (fun x l => TL3.act A B l x) (TL3.ofTL2 x) =
      TL3.ofTL2 (w.foldl (fun x s => TL2.act A B s x) x) := by
  induction w generalizing x with
  | nil => rfl
  | cons s w ih =>
      rw [incl_cons]
      simp only [List.foldl_cons]
      rw [TL3.act_ofTL2, ih]

theorem tl3_incl (A B : R) (w : List Bool) :
    tl3 A B (incl w) = TL3.ofTL2 (tl2 A B w) := by
  have h : TL3.one R = TL3.ofTL2 (TL2.one R) := by ext <;> simp [TL3.one, TL2.one, TL3.ofTL2]
  simp [tl3, tl2, h, tl3_incl_aux]

theorem TL3.tr_stab_pos (A B : R) (hAB : A * B = 1) (x : TL2 R) :
    TL3.tr A B (TL3.act A B (true, true) (TL3.ofTL2 x)) = (-A ^ 3) * TL2.tr A B x := by
  simp only [TL3.tr, TL2.tr, TL3.act, TL3.mulE2, TL3.ofTL2, delta]
  grind

theorem TL3.tr_stab_neg (A B : R) (hAB : A * B = 1) (x : TL2 R) :
    TL3.tr A B (TL3.act A B (true, false) (TL3.ofTL2 x)) = (-B ^ 3) * TL2.tr A B x := by
  simp only [TL3.tr, TL2.tr, TL3.act, TL3.mulE2, TL3.ofTL2, delta]
  grind

theorem normFactor3_incl (A B : R) (w : List Bool) :
    normFactor3 A B (incl w) = normFactor2 A B w := by
  simp [normFactor3, normFactor2, incl, List.countP_map, Function.comp_def]

theorem normFactor3_stab_pos (A B : R) (w : List Bool) :
    normFactor3 A B (incl w ++ [(true, true)]) = (-B ^ 3) * normFactor2 A B w := by
  simp only [normFactor3, List.countP_append, List.countP_cons, pow_add]
  simp [normFactor2, incl, List.countP_map, Function.comp_def]
  ring

theorem normFactor3_stab_neg (A B : R) (w : List Bool) :
    normFactor3 A B (incl w ++ [(true, false)]) = (-A ^ 3) * normFactor2 A B w := by
  simp only [normFactor3, List.countP_append, List.countP_cons, pow_add]
  simp [normFactor2, incl, List.countP_map, Function.comp_def]
  ring

theorem bracket3_stab_pos (A B : R) (hAB : A * B = 1) (w : List Bool) :
    bracket3 A B (incl w ++ [(true, true)]) = (-A ^ 3) * bracket2 A B w := by
  rw [bracket3, tl3_append, tl3_incl]
  simpa [bracket2] using TL3.tr_stab_pos A B hAB (tl2 A B w)

theorem bracket3_stab_neg (A B : R) (hAB : A * B = 1) (w : List Bool) :
    bracket3 A B (incl w ++ [(true, false)]) = (-B ^ 3) * bracket2 A B w := by
  rw [bracket3, tl3_append, tl3_incl]
  simpa [bracket2] using TL3.tr_stab_neg A B hAB (tl2 A B w)

theorem jones3_stab_pos (A B : R) (hAB : A * B = 1) (w : List Bool) :
    jones3 A B (incl w ++ [(true, true)]) = jones2 A B w := by
  rw [jones3, jones2, normFactor3_stab_pos, bracket3_stab_pos A B hAB]
  have h : (-B ^ 3) * (-A ^ 3) = 1 := by grind
  calc (-B ^ 3) * normFactor2 A B w * ((-A ^ 3) * bracket2 A B w)
      = ((-B ^ 3) * (-A ^ 3)) * (normFactor2 A B w * bracket2 A B w) := by ring
    _ = normFactor2 A B w * bracket2 A B w := by rw [h, one_mul]

theorem jones3_stab_neg (A B : R) (hAB : A * B = 1) (w : List Bool) :
    jones3 A B (incl w ++ [(true, false)]) = jones2 A B w := by
  rw [jones3, jones2, normFactor3_stab_neg, bracket3_stab_neg A B hAB]
  have h : (-A ^ 3) * (-B ^ 3) = 1 := by grind
  calc (-A ^ 3) * normFactor2 A B w * ((-B ^ 3) * bracket2 A B w)
      = ((-A ^ 3) * (-B ^ 3)) * (normFactor2 A B w * bracket2 A B w) := by ring
    _ = normFactor2 A B w * bracket2 A B w := by rw [h, one_mul]


/-! ## Markov conjugation invariance

The Kauffman bracket of a braid closure depends only on the conjugacy class of the
braid word; equivalently, it is invariant under cyclic permutation of the word.  This is
the second Markov move, and it follows from the trace property `tr (x * y) = tr (y * x)`
of the Markov trace on `TL₃`. -/

/-- Multiplication in `TL₃`, in the diagram basis `1, e₁, e₂, e₁e₂, e₂e₁`. -/
def TL3.mul (A B : R) (x y : TL3 R) : TL3 R :=
  ⟨x.c1 * y.c1,
   x.c1 * y.ce1 + x.ce1 * (y.c1 + delta A B * y.ce1 + y.ce21)
     + x.ce12 * (y.ce1 + delta A B * y.ce21),
   x.c1 * y.ce2 + x.ce2 * (y.c1 + delta A B * y.ce2 + y.ce12)
     + x.ce21 * (y.ce2 + delta A B * y.ce12),
   x.c1 * y.ce12 + x.ce1 * (y.ce2 + delta A B * y.ce12)
     + x.ce12 * (y.c1 + delta A B * y.ce2 + y.ce12),
   x.c1 * y.ce21 + x.ce2 * (y.ce1 + delta A B * y.ce21)
     + x.ce21 * (y.c1 + delta A B * y.ce1 + y.ce21)⟩

theorem TL3.mul_one (A B : R) (x : TL3 R) : TL3.mul A B x (TL3.one R) = x := by
  ext <;> simp [TL3.mul, TL3.one]

theorem TL3.one_mul (A B : R) (x : TL3 R) : TL3.mul A B (TL3.one R) x = x := by
  ext <;> simp [TL3.mul, TL3.one]

set_option maxHeartbeats 4000000 in
theorem TL3.mul_assoc (A B : R) (x y z : TL3 R) :
    TL3.mul A B (TL3.mul A B x y) z = TL3.mul A B x (TL3.mul A B y z) := by
  ext <;> simp only [TL3.mul, delta] <;> ring

set_option maxHeartbeats 4000000 in
theorem TL3.act_eq_mul (A B : R) (l : Letter) (x : TL3 R) :
    TL3.act A B l x = TL3.mul A B x (TL3.act A B l (TL3.one R)) := by
  cases l with
  | mk i s =>
      cases i <;> cases s <;> ext <;>
        simp only [TL3.act, TL3.mul, TL3.mulE1, TL3.mulE2, TL3.one, delta,
          if_true, if_false, Bool.false_eq_true] <;> ring

theorem tl3_foldl_eq_mul (A B : R) (w : List Letter) (x : TL3 R) :
    w.foldl (fun x l => TL3.act A B l x) x = TL3.mul A B x (tl3 A B w) := by
  induction w generalizing x with
  | nil => simp [tl3, TL3.mul_one]
  | cons l w ih =>
      have h1 : (l :: w).foldl (fun x l => TL3.act A B l x) x
          = w.foldl (fun x l => TL3.act A B l x) (TL3.act A B l x) := by
        simp only [List.foldl_cons]
      have h2 : tl3 A B (l :: w) = TL3.mul A B (TL3.act A B l (TL3.one R)) (tl3 A B w) := by
        rw [tl3]
        simp only [List.foldl_cons]
        exact ih (TL3.act A B l (TL3.one R))
      rw [h1, ih (TL3.act A B l x), h2, TL3.act_eq_mul A B l x, TL3.mul_assoc]

theorem tl3_append_mul (A B : R) (w₁ w₂ : List Letter) :
    tl3 A B (w₁ ++ w₂) = TL3.mul A B (tl3 A B w₁) (tl3 A B w₂) := by
  rw [tl3_append, tl3_foldl_eq_mul]

set_option maxHeartbeats 4000000 in
theorem TL3.tr_mul_comm (A B : R) (x y : TL3 R) :
    TL3.tr A B (TL3.mul A B x y) = TL3.tr A B (TL3.mul A B y x) := by
  simp only [TL3.tr, TL3.mul, delta]
  ring

theorem bracket3_cyclic (A B : R) (w₁ w₂ : List Letter) :
    bracket3 A B (w₁ ++ w₂) = bracket3 A B (w₂ ++ w₁) := by
  rw [bracket3, bracket3, tl3_append_mul, tl3_append_mul, TL3.tr_mul_comm]

theorem normFactor3_comm (A B : R) (w₁ w₂ : List Letter) :
    normFactor3 A B (w₁ ++ w₂) = normFactor3 A B (w₂ ++ w₁) := by
  simp only [normFactor3, List.countP_append]
  rw [Nat.add_comm (w₁.countP fun l => l.2), Nat.add_comm (w₁.countP fun l => !l.2)]

/-- **Markov move II** : the Jones polynomial of a braid closure is invariant under
conjugation of the braid word (equivalently, under cyclic permutation of the word). -/
theorem jones3_conj (A B : R) (w₁ w₂ : List Letter) :
    jones3 A B (w₁ ++ w₂) = jones3 A B (w₂ ++ w₁) := by
  rw [jones3, jones3, bracket3_cyclic, normFactor3_comm]

/-! ## Base computations -/

/-- The Jones polynomial of the unknot, presented as the closure of the one-crossing
`2`-braid `σ₁^{±1}`, is `δ` — that is, `1` in the normalisation in which the unknot has
value `1`. In particular it does not depend on the sign of the kink: this is
Reidemeister I for the one-crossing unknot diagrams. -/
theorem jones2_unknot (A B : R) (hAB : A * B = 1) (s : Bool) :
    jones2 A B [s] = delta A B := by
  cases s <;>
    simp [jones2, normFactor2, bracket2, tl2, TL2.act, TL2.one, TL2.mulE1, TL2.tr, delta] <;>
    grind

/-- The Kauffman bracket of the (right-handed) trefoil, as the closure of `σ₁³`:
`δ * (-A⁵ - A⁻³ + A⁻⁷)`, i.e. `-A⁵ - A⁻³ + A⁻⁷` in the normalisation where the
unknot has bracket `1`. -/
theorem bracket2_trefoil (A B : R) (hAB : A * B = 1) :
    bracket2 A B [true, true, true] = delta A B * (-A ^ 5 - B ^ 3 + B ^ 7) := by
  simp only [bracket2, tl2, List.foldl_cons, List.foldl_nil, TL2.act, TL2.one, TL2.mulE1,
    TL2.tr, delta, if_pos]
  grind

/-! ## Main theorem -/

/-- **The Jones polynomial is a link invariant** (the three-strand braid-closure case).

Working over any commutative ring `R` with an invertible element `A` (with inverse `B`),
the writhe-normalised Kauffman bracket `jones3` of the closure of a braid word on three
strands is unchanged by all the Reidemeister moves available in this model:

* `Reidemeister II`: deleting a cancelling pair `σᵢ σᵢ⁻¹` or `σᵢ⁻¹ σᵢ` anywhere in the word;
* `Reidemeister III`: the braid relation `σ₁σ₂σ₁ = σ₂σ₁σ₂` (for either crossing sign);
* `Markov conjugation`: cyclic permutation (conjugation) of the braid word;
* `Reidemeister I` (Markov stabilisation): appending a single crossing `σ₂^{±1}` to (the
  image of) a two-strand braid word does not change the value; the writhe correction
  exactly cancels the factor `-A^{±3}` produced by the extra kink. -/
theorem jones_polynomial_invariant (A B : R) (hAB : A * B = 1) :
    (∀ (i : Bool) (w₁ w₂ : List Letter),
        jones3 A B (w₁ ++ (i, true) :: (i, false) :: w₂) = jones3 A B (w₁ ++ w₂)) ∧
    (∀ (i : Bool) (w₁ w₂ : List Letter),
        jones3 A B (w₁ ++ (i, false) :: (i, true) :: w₂) = jones3 A B (w₁ ++ w₂)) ∧
    (∀ (s : Bool) (w₁ w₂ : List Letter),
        jones3 A B (w₁ ++ (false, s) :: (true, s) :: (false, s) :: w₂) =
          jones3 A B (w₁ ++ (true, s) :: (false, s) :: (true, s) :: w₂)) ∧
    (∀ w : List Bool, jones3 A B (incl w ++ [(true, true)]) = jones2 A B w) ∧
    (∀ w : List Bool, jones3 A B (incl w ++ [(true, false)]) = jones2 A B w) ∧
    (∀ w₁ w₂ : List Letter, jones3 A B (w₁ ++ w₂) = jones3 A B (w₂ ++ w₁)) :=
  ⟨fun i w₁ w₂ => jones3_R2_pos A B hAB i w₁ w₂,
   fun i w₁ w₂ => jones3_R2_neg A B hAB i w₁ w₂,
   fun s w₁ w₂ => jones3_R3 A B hAB s w₁ w₂,
   fun w => jones3_stab_pos A B hAB w,
   fun w => jones3_stab_neg A B hAB w,
   fun w₁ w₂ => jones3_conj A B w₁ w₂⟩

/-- The invariant is not constant: at the specialisation `A = 2` over `ℚ` it takes
different values on the trefoil (the closure of `σ₁³`) and on the unknot (the closure
of `σ₁`), so the theory above is not vacuous. -/
theorem jones_trefoil_ne_unknot :
    jones2 (2 : ℚ) (1 / 2) [true, true, true] ≠ jones2 (2 : ℚ) (1 / 2) [true] := by
  norm_num [jones2, normFactor2, bracket2, tl2, TL2.act, TL2.one, TL2.mulE1, TL2.tr, delta]

#print axioms Frontier.jones_polynomial_invariant
#print axioms Frontier.jones2_unknot
#print axioms Frontier.bracket2_trefoil
#print axioms Frontier.jones_trefoil_ne_unknot

end Frontier

