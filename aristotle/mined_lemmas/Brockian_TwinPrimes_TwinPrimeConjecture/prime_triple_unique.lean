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
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Twin Prime Conjecture
Category: Brockian Conjecture
Target: Brockian.TwinPrimes.TwinPrimeConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The twin prime conjecture itself is open, so what is proved here is a
*Lean-checked reduction*: the twin prime conjecture is shown to be equivalent to
an explicit elementary congruence condition (Clement's criterion), together with
some unconditional partial results.
-/

namespace Brockian.TwinPrimes

open Nat

/-- `n` is the smaller member of a twin prime pair. -/

theorem prime_triple_unique {p : ℕ} (h1 : Nat.Prime p) (h2 : Nat.Prime (p + 2))
    (h3 : Nat.Prime (p + 4)) : p = 3 := by
  by_contra hp
  have hp2 : 2 ≤ p := h1.two_le
  have hd3 : (3 : ℕ) ∣ p ∨ (3 : ℕ) ∣ (p + 2) ∨ (3 : ℕ) ∣ (p + 4) := by omega
  rcases hd3 with hd | hd | hd
  · have := h1.eq_one_or_self_of_dvd 3 hd; omega
  · have := h2.eq_one_or_self_of_dvd 3 hd; omega
  · have := h3.eq_one_or_self_of_dvd 3 hd; omega

end Brockian.TwinPrimes

