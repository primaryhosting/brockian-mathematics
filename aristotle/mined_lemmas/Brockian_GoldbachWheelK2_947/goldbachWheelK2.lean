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

set_option grind.warning false

namespace Brockian

/-- The `K2` Goldbach wheel property at modulus `m`:

every residue class `r` modulo `m` is represented as `p + q` with `p`, `q` prime, where moreover
the two primes may be taken arbitrarily large (larger than any prescribed bound `N`).

This is the "wheel" (residue-class) shadow of the binary Goldbach problem: it says that, modulo
`m`, no congruence obstruction can rule out a representation as a sum of two primes, uniformly in
the size of the primes used. -/

def GoldbachWheelK2 (m : ℕ) : Prop :=
  ∀ (N : ℕ) (r : ZMod m), ∃ p q : ℕ,
    N < p ∧ N < q ∧ Nat.Prime p ∧ Nat.Prime q ∧ (p : ZMod m) + (q : ZMod m) = r

/-- Auxiliary "wheel splitting" property: every residue modulo `m` is a sum of two units of
`ZMod m`.  Units are precisely the residues that can contain large primes, so this is the exact
residue-theoretic content of `GoldbachWheelK2`. -/
