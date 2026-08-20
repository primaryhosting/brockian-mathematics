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
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Legendre Conjecture
Category: Brockian Conjecture
Target: Brockian.LegendreConjecture.LegendreConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.LegendreConjecture

/-- **Legendre's conjecture** (open): for every `n ≥ 1` there is a prime strictly
between `n ^ 2` and `(n + 1) ^ 2`. -/

theorem legendre_small (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 12) :
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < p ∧ p < (n + 1) ^ 2 := by
  interval_cases n
  · exact ⟨2, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨37, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨53, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨67, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨83, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨101, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨127, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨149, by norm_num, by norm_num, by norm_num⟩

/-- A weaker unconditional statement that *is* provable from Mathlib: by Bertrand's postulate
(`Nat.exists_prime_lt_and_le_two_mul`) there is a prime `p` with `n ^ 2 < p ≤ 2 * n ^ 2`
for every `n ≥ 1`. Narrowing `2 * n ^ 2` to `(n + 1) ^ 2` is exactly Legendre's conjecture. -/
