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
# Amicable Infinitude
Category: Brockian Conjecture
Target: Brockian.AmicableNumbers.AmicableInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
The infinitude of amicable numbers is a well-known open problem.  What is proved here is a
*conditional reduction*: if Thabit ibn Qurra's rule produces amicable pairs for arbitrarily
large parameters (i.e. there are arbitrarily large `m` for which the three Thabit numbers
`3·2^m - 1`, `3·2^(m+1) - 1`, `9·2^(2m+1) - 1` are all prime), then there are infinitely many
amicable numbers.  The Thabit construction itself is proved unconditionally
(`Brockian.AmicableNumbers.isAmicablePair_thabit`), as is the classical example `(220, 284)`.
-/

namespace Brockian.AmicableNumbers

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- `a` and `b` form an amicable pair: they are distinct and each one's proper divisors sum to
the other, equivalently `σ a = σ b = a + b`. -/

theorem AmicableInfinitude (H : ∀ N : ℕ, ∃ m, N ≤ m ∧ ThabitTriple m) :
    {a : ℕ | IsAmicable a}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨m, hmN, hm⟩ := H N
  refine ⟨2 ^ (m + 1) * ((3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1)),
    ⟨_, isAmicablePair_thabit hm⟩, ?_⟩
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_two_pow
  have hpos : 0 < (3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1) :=
    Nat.mul_pos (by omega) (by omega)
  calc N < 2 ^ (m + 1) :=
        lt_of_le_of_lt hmN (lt_of_lt_of_le Nat.lt_two_pow_self
          (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ m)))
    _ ≤ 2 ^ (m + 1) * ((3 * 2 ^ m - 1) * (3 * 2 ^ (m + 1) - 1)) :=
        Nat.le_mul_of_pos_right _ hpos

end Brockian.AmicableNumbers

