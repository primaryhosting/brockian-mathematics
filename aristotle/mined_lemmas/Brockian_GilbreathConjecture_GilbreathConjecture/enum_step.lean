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

theorem enum_step {p : Nat → Nat} (hp : IsPrimeEnumeration p) {k q r : Nat}
    (hk : p k = q) (hr : IsPrimeNat r) (hqr : q < r)
    (hgap : ∀ m, m < r → q < m → ¬ IsPrimeNat m) : p (k + 1) = r := by
  obtain ⟨n, hn⟩ := hp.2.2 r hr
  have hkn : k < n := by
    rcases Nat.lt_or_ge k n with h | h
    · exact h
    · have := enum_le hp h
      omega
  have hle : p (k + 1) ≤ p n := enum_le hp (by omega)
  have hlt : p k < p (k + 1) := hp.2.1 k (k + 1) (by omega)
  rcases Nat.lt_or_ge (p (k + 1)) r with h | h
  · exact absurd (hp.1 (k + 1)) (hgap _ h (by omega))
  · omega

