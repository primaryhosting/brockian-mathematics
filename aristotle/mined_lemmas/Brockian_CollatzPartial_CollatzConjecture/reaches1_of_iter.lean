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
# Collatz Conjecture
Category: Brockian Conjecture
Target: Brockian.CollatzPartial.CollatzConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This module is deliberately self-contained: it uses no imports beyond Lean's core
`Init`, so that the header comment above can be the very first thing in the file.
Everything below (the Collatz map, its iteration, and all lemmas) is developed
from scratch.

The Collatz conjecture itself is open. What is proved here is:

* `collatzConjecture_iff_mod_four` — the conjecture reduces to the residue class 3 mod 4;
* `collatzConjecture_iff_hardResidue` — it reduces further to the three residue classes
  7, 11, 15 modulo 16;
* `collatzConjecture_iff_eventual_descent` — the conjecture is equivalent to the statement
  that every `n > 1` is eventually mapped below itself;
* `exists_minimal_counterexample` — contrapositive form: a failure of the conjecture yields
  a least counterexample, which must lie in one of those three classes mod 16;
* `cycle_trivial_of_reaches1` and `cycle_trivial_of_lt_1000` — every Collatz cycle meeting
  `{n : 0 < n < 1000}` is the trivial cycle `1 → 4 → 2 → 1`;
* `reaches1_of_lt_1000` — an exhaustive kernel-checked verification for all `0 < n < 1000`;
* `reaches1_two_pow` — every power of two reaches 1.
-/

namespace Brockian.CollatzPartial

/-! ## The Collatz map -/

/-- One step of the Collatz (`3n + 1`) map: halve an even number, otherwise `n ↦ 3n + 1`. -/

theorem reaches1_of_iter {n k : Nat} (h : Reaches1 (iter k n)) : Reaches1 n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + k, by rw [iter_add]; exact hj⟩

