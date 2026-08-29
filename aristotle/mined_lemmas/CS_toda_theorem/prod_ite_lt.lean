import Mathlib

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

/-
Isolation (Valiant–Vazirani) lemma over `GF(2)`, in the counting form needed for
Toda's theorem.
-/
import Mathlib

namespace CS.Toda

open Finset

/-- Bit vectors of length `m`, as vectors over `GF(2)`. -/
abbrev Vec (m : ℕ) := Fin m → ZMod 2

/-- The standard `GF(2)`-bilinear form. -/

lemma prod_ite_lt {M : Type*} [CommMonoid M] {m k : ℕ} (hk : k ≤ m+1) (a b : M) :
    ∏ i : Fin (m+1), (if (i:ℕ) < k then a else b) = a^k * b^(m+1-k) := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  rw [card_filter_lt hk]
  congr 1
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (m+1))))
      (p := fun i : Fin (m+1) => (i:ℕ) < k)
  rw [card_filter_lt hk] at this
  simp only [Finset.card_univ, Fintype.card_fin] at this
  congr 1
  omega

