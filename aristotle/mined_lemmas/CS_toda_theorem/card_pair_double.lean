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

lemma card_pair_double {m : ℕ} {y y' : Vec m} (hne : y ≠ y') :
    2 * (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)).card
      = 2^m := by
  classical
  have hu : y + y' ≠ 0 := by
    intro h
    exact hne (funext fun j =>
      (by decide : ∀ a b : ZMod 2, a + b = 0 → a = b) (y j) (y' j) (congrFun h j))
  rw [show (univ.filter (fun p : Vec m × ZMod 2 => ip p.1 y = p.2 ∧ ip p.1 y' = p.2)).card
      = (univ.filter (fun r : Vec m => ip (y+y') r = 0)).card from ?_]
  · exact card_ip_zero hu
  · apply Finset.card_nbij' (fun p => p.1) (fun r => (r, ip r y))
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hp ⊢
      rw [ip_comm, ip_add, hp.1, hp.2]
      exact (by decide : ∀ z : ZMod 2, z + z = 0) _
    · intro r hr
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hr ⊢
      rw [ip_comm, ip_add] at hr
      have h2 : ip r y' = ip r y := by
        have h3 : ip r y' = - ip r y := by linear_combination (norm := abel_nf) hr
        rw [h3]; exact (by decide : ∀ z : ZMod 2, -z = z) _
      exact h2
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hp
      simp [hp.1]
    · intro r _; rfl

