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

def IsPrimeNat (n : Nat) : Prop := 2 ≤ n ∧ ∀ d, d < n → 2 ≤ d → ¬ (d ∣ n)

/-- Decidability of bounded universal quantification over `Nat`. -/
instance decidableBallLTNat (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    Decidable (∀ d, d < n → P d) := by
  induction n with
  | zero => exact isTrue (fun d hd => absurd hd (by omega))
  | succ n ih =>
      match ih with
      | isFalse h => exact isFalse (fun H => h (fun d hd => H d (by omega)))
      | isTrue h =>
          match inferInstanceAs (Decidable (P n)) with
          | isFalse h2 => exact isFalse (fun H => h2 (H n (by omega)))
          | isTrue h2 =>
              refine isTrue (fun d hd => ?_)
              by_cases hdn : d = n
              · exact hdn ▸ h2
              · exact h d (by omega)

instance : DecidablePred IsPrimeNat := fun n =>
  inferInstanceAs (Decidable (2 ≤ n ∧ ∀ d, d < n → 2 ≤ d → ¬ (d ∣ n)))

/-- `p` enumerates the primes in increasing order. -/
