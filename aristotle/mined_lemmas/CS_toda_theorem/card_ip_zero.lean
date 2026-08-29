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

lemma card_ip_zero {m : ℕ} {u : Vec m} (hu : u ≠ 0) :
    2 * (univ.filter (fun v : Vec m => ip u v = 0)).card = 2 ^ m := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i, u i ≠ 0 := by
    by_contra h; push_neg at h; exact hu (funext h)
  have hu1 : u i0 = 1 := zmod2_ne_zero hi0
  have hbij : (univ.filter (fun v : Vec m => ip u v = 0)).card
      = (univ.filter (fun v : Vec m => ip u v = 1)).card := by
    apply Finset.card_nbij' (fun v => v + Pi.single i0 1) (fun v => v + Pi.single i0 1)
    · intro v hv
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hv ⊢
      rw [ip_add, ip_single, hv, hu1]; ring
    · intro v hv
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hv ⊢
      rw [ip_add, ip_single, hv, hu1]; decide
    · intro v _; simp [add_assoc, single_add_single]
    · intro v _; simp [add_assoc, single_add_single]
  have htot : (univ.filter (fun v : Vec m => ip u v = 0)).card
      + (univ.filter (fun v : Vec m => ip u v = 1)).card = 2 ^ m := by
    have h2 : (univ.filter (fun v : Vec m => ip u v = 1))
        = (univ.filter (fun v : Vec m => ¬ (ip u v = 0))) := by
      apply Finset.filter_congr
      intro v _
      exact ⟨fun h => by rw [h]; decide, fun h => zmod2_ne_zero h⟩
    rw [h2, Finset.card_filter_add_card_filter_not]
    simp
  omega

/-- The space of hash functions: `m+1` linear forms together with `m+1` constants. -/
abbrev Hsp (m : ℕ) := Fin (m+1) → (Vec m × ZMod 2)

/-- `y` survives the hash `h` cut down to its first `k` rows. -/
