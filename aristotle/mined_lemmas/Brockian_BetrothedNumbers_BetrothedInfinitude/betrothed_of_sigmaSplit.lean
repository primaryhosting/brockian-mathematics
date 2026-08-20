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
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Betrothed Infinitude
Category: Brockian Conjecture
Target: Brockian.BetrothedNumbers.BetrothedInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` lines to precede any module docstring, so the header comment above is a
plain block comment and is repeated here as the module docstring.)
-/

open ArithmeticFunction

namespace Brockian.BetrothedNumbers

/-- Two positive integers `m ≠ n` are *betrothed* (a quasi-amicable pair) when the sum of the
divisors of each equals `m + n + 1`; equivalently, the sum of the divisors of each strictly
between `1` and the number itself equals the other number. -/

theorem betrothed_of_sigmaSplit {A P Q : ℕ} (h : SigmaSplit A P Q) :
    Betrothed (A * P) (A * Q) := by
  obtain ⟨hA, hP, hQ, hPQ, hAP, hAQ, hsig, heq⟩ := h
  have hmul : ∀ B : ℕ, Nat.Coprime A B → sigma 1 (A * B) = sigma 1 A * sigma 1 B := by
    intro B hB
    exact (isMultiplicative_sigma (k := 1)).map_mul_of_coprime hB
  have hm : sigma 1 (A * P) = A * P + A * Q + 1 := by
    rw [hmul P hAP, heq, Nat.mul_add]
  have hn : sigma 1 (A * Q) = A * P + A * Q + 1 := by
    rw [hmul Q hAQ, ← hsig, heq, Nat.mul_add]
  exact ⟨Nat.mul_pos hA hP, Nat.mul_pos hA hQ,
    fun hc => hPQ (Nat.eq_of_mul_eq_mul_left hA hc), hm, hn⟩

set_option maxRecDepth 100000 in
/-- The sigma split behind the smallest betrothed pair `(48, 75)`. In particular the notion is
not vacuous. -/
