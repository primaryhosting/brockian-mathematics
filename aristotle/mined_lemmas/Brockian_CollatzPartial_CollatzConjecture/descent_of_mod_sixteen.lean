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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The full Collatz conjecture is open.  What is proved here is:

* `CollatzConjecture` : a Lean-checked *conditional reduction* — if every integer `> 1`
  eventually iterates to a strictly smaller value (the descent property), then every
  positive integer reaches `1`.
* unconditional partial results: the descent property holds for every `n > 1` outside the
  residue class `3 (mod 4)`, and every power of two reaches `1`.
-/

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n/2` if `n` is even, `n ↦ 3n+1` if `n` is odd. -/

theorem descent_of_mod_sixteen {n : ℕ} (hn : 1 < n)
    (h7 : n % 16 ≠ 7) (h11 : n % 16 ≠ 11) (h15 : n % 16 ≠ 15) :
    ∃ k, 0 < k ∧ collatz^[k] n < n := by
  rcases Nat.mod_two_eq_zero_or_one n with h2 | h2
  · exact ⟨1, one_pos, by simpa using descent_of_even hn h2⟩
  · rcases eq_or_ne (n % 4) 1 with h1 | h1
    · exact ⟨3, by norm_num, descent_of_one_mod_four hn h1⟩
    · exact ⟨6, by norm_num, descent_of_three_mod_sixteen (by omega)⟩

/-- Every power of two reaches `1`, unconditionally. -/
