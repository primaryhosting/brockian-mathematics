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

/-!
# Gilbreath Conjecture
Category: Brockian Conjecture
Target: Brockian.GilbreathConjecture.GilbreathConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.GilbreathConjecture

/-! ## Primes -/

/-- `n` is prime: it is at least `2` and has no divisor `d` with `2 ≤ d < n`. -/

theorem head_iterD_eq_one {a : Nat → Nat} {n j : Nat} (h : IsOdlyzko a n) (hj : j ≤ n) :
    (iterD j a) 0 = 1 := by
  induction j generalizing a n with
  | zero => exact h.1
  | succ j ih =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      rw [iterD]
      exact ih (isOdlyzko_diffSeq h) (by omega)

/-- The combinatorial core: for an arbitrary initial sequence, the Odlyzko
condition forces every row after the zeroth to begin with `1`. -/
