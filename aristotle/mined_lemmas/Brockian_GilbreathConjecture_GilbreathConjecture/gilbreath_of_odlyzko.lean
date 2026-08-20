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

theorem gilbreath_of_odlyzko (p : Nat → Nat) (H : OdlyzkoCondition p) :
    GilbreathStatement p := by
  intro m hm
  obtain ⟨k, n, hk, hkn, ho⟩ := H m hm
  obtain ⟨j, rfl⟩ : ∃ j, m = k + j := ⟨m - k, by omega⟩
  rw [gilbreathRow_add]
  exact head_iterD_eq_one ho (by omega)

/-- **Conditional reduction of Gilbreath's conjecture.**

Gilbreath's conjecture — that every row after the first of the iterated absolute
difference triangle of the primes begins with `1` — is an open problem.  What is
proved here is the standard reduction (in essence due to Odlyzko): for any
increasing enumeration `p` of the primes, Gilbreath's conjecture follows from the
purely combinatorial `OdlyzkoCondition`, namely that every row index is covered by
an earlier row of the form `1, 0/2, 0/2, …` with a long enough `0/2`-stretch.

No assumption is hidden: the Odlyzko condition is an explicit hypothesis of the
theorem.  (The primality hypothesis `hp` is part of the statement, pinning the
triangle to the primes; the combinatorial argument itself does not use it.) -/
