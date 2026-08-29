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

lemma card_pair_single {m : ℕ} (y : Vec m) :
    (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2)).card = 2^m := by
  classical
  rw [show (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2)).card
      = (univ : Finset (Vec m)).card from ?_]
  · simp
  · apply Finset.card_nbij' (fun p => p.1) (fun r => (r, ip r y)) <;>
      intro p hp <;> simp_all

