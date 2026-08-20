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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The whole development below is therefore
self-contained and uses only the Lean 4 core library (no Mathlib).
-/

namespace Brockian.FortunateNumbers

/-! ## Primality and the primorial -/

/-- `IsPrime p` : `p` is a prime natural number. -/

theorem not_dvd_of_isFortunate {n m q : Nat} (h : IsFortunate n m) (hq : IsPrime q)
    (hqn : q ≤ n) : ¬ q ∣ m := by
  intro hdvd
  have hdP : q ∣ primorial n := prime_dvd_primorial hq hqn
  have hsum : q ∣ primorial n + m := Nat.dvd_add hdP hdvd
  have hqle : q ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hdP
  have hlt : q < primorial n + m := by have := h.1; omega
  exact h.2.1.not_dvd hlt hq.two_le hsum

/-- **Key reduction.** A fortunate number that is at most the square of its index is prime. -/
