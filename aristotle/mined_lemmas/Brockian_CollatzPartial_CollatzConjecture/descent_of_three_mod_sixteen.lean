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

theorem descent_of_three_mod_sixteen {n : ℕ} (h : n % 16 = 3) : collatz^[6] n < n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 16 * m + 3 := ⟨n / 16, by omega⟩
  have e1 : collatz (16 * m + 3) = 48 * m + 10 := by
    rw [collatz_odd (by omega)]; omega
  have e2 : collatz (48 * m + 10) = 24 * m + 5 := by
    rw [collatz_even (by omega)]; omega
  have e3 : collatz (24 * m + 5) = 72 * m + 16 := by
    rw [collatz_odd (by omega)]; omega
  have e4 : collatz (72 * m + 16) = 36 * m + 8 := by
    rw [collatz_even (by omega)]; omega
  have e5 : collatz (36 * m + 8) = 18 * m + 4 := by
    rw [collatz_even (by omega)]; omega
  have e6 : collatz (18 * m + 4) = 9 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  show collatz (collatz (collatz (collatz (collatz (collatz (16 * m + 3)))))) < 16 * m + 3
  rw [e1, e2, e3, e4, e5, e6]
  omega

/-- Sharpened unconditional descent: the descent property holds for every `n > 1` whose
residue mod `16` is not `7`, `11` or `15`, i.e. for `13` of the `16` residue classes. -/
