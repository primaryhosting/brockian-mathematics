import Mathlib

/-!
# Triangular Mod 5 Mem
Category: Cone Line
Target: Brockian.ConeLine.triangular_mod5_mem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


set_option autoImplicit false

namespace Brockian.ConeLine

/-- The `n`-th triangular number, `T n = n(n+1)/2` (natural-number division, which is
exact here since `n(n+1)` is even). -/
def T (n : ℕ) : ℕ := n * (n + 1) / 2

/-- Doubling a triangular number recovers `n(n+1)`. -/
lemma two_mul_T (n : ℕ) : 2 * T n = n * (n + 1) := by
  have h : 2 ∣ n * (n + 1) := (Nat.even_mul_succ_self n).two_dvd
  rw [T, Nat.mul_div_cancel' h]

/-- In `ZMod 5`, the only solutions of `2 * a = b * (b + 1)` have `a ∈ {0, 1, 3}`. -/
lemma mem_of_two_mul_eq (a b : ZMod 5) (h : 2 * a = b * (b + 1)) :
    a = 0 ∨ a = 1 ∨ a = 3 := by
  revert a b
  decide

/-- Triangular numbers land only on the residues `0, 1, 3` modulo `5`:
for every `n`, `T n = n(n+1)/2` satisfies `(T n : ZMod 5) ∈ {0, 1, 3}`. -/
theorem triangular_mod5_mem (n : ℕ) :
    ((n * (n + 1) / 2 : ℕ) : ZMod 5) ∈ ({0, 1, 3} : Set (ZMod 5)) := by
  have h : (2 : ZMod 5) * ((T n : ℕ) : ZMod 5) = (n : ZMod 5) * ((n : ZMod 5) + 1) := by
    have := congrArg (fun m : ℕ => (m : ZMod 5)) (two_mul_T n)
    push_cast at this
    simpa using this
  have := mem_of_two_mul_eq _ _ h
  simpa [T, Set.mem_insert_iff, Set.mem_singleton_iff] using this

end Brockian.ConeLine

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

