import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The statement of Chen's theorem -/

/-- `AlmostPrime2 q` says that `q` has at most two prime factors, counted with
multiplicity (i.e. `Ω(q) ≤ 2`); such a number is classically called a `P₂`.
Note that primes themselves satisfy this (`Ω = 1`). -/

theorem chenRep_of_primes {n p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : n = p + q) : ChenRep n :=
  ⟨p, q, hp, almostPrime2_of_prime hq, h⟩

/-! ## A verified base case -/

/-- The primes below `1000`. -/
