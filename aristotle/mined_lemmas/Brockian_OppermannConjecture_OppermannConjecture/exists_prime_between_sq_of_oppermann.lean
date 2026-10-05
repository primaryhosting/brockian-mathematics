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


theorem exists_prime_between_sq_of_oppermann (H : OppermannConjecture) (n : Nat) (hn : 1 < n) :
    ∃ p : Nat, IsPrimeNat p ∧ n * n < p ∧ p < n * n + n := by
  obtain ⟨-, p, hp, hp1, hp2⟩ := H n hn
  rw [Nat.mul_succ] at hp2
  exact ⟨p, hp, hp1, hp2⟩

end Brockian.OppermannConjecture

import Mathlib
import Brockian.OppermannConjecture

/-!
# Bridge between the import-free Oppermann file and Mathlib

`Brockian/OppermannConjecture.lean` must begin with a fixed header comment, which forces it
to be import-free.  Here we check that its self-contained notion of primality coincides with
Mathlib's `Nat.Prime`, and consequently that `Brockian.OppermannConjecture.OppermannConjecture`
is equivalent to the statement of Oppermann's conjecture phrased with `Nat.Prime`.
-/

namespace Brockian.OppermannConjecture

/-- The self-contained primality predicate agrees with Mathlib's `Nat.Prime`. -/
