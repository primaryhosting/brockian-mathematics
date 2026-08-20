import Mathlib

/-!
# Hydra Kirby Paris
Category: Frontier — Set Theory
Target: Frontier.Hydra_Kirby_Paris
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Ordinal
open scoped NaturalOps

namespace Frontier

/-!
## Part 1: `ω ^ c` is principal for natural (Hessenberg) addition

Mathlib knows that `ω ^ c` is principal for ordinary ordinal addition, but not for the
natural sum `♯`.  We prove this here, since the ordinal assignment used for the hydra
game relies on it.
-/

/-- Every ordinal below `ω ^ d * ω` can be written as `ω ^ d * m + r` with `m` a natural
number and `r < ω ^ d`. -/

theorem opow_mul_nat_add_lt (d : Ordinal) (m : ℕ) (r : Ordinal) (hr : r < ω ^ d) :
    ω ^ d * (m : Ordinal) + r < ω ^ d * ω := by
  have h1 : ω ^ d * (m : Ordinal) + r < ω ^ d * (m : Ordinal) + ω ^ d :=
    (add_lt_add_iff_left _).2 hr
  have h2 : ω ^ d * (m : Ordinal) + ω ^ d = ω ^ d * ((m : Ordinal) + 1) := by
    rw [mul_add, mul_one]
  have h3 : ω ^ d * ((m : Ordinal) + 1) < ω ^ d * ω := by
    apply mul_lt_mul_of_pos_left _ (Ordinal.opow_pos d omega0_pos)
    have := Ordinal.nat_lt_omega0 (m + 1)
    push_cast at this
    exact this
  exact h1.trans (h2 ▸ h3)

/-- Comparing two base-`ω ^ d` decompositions. -/
