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
This file is deliberately self-contained (no `import` lines), so that the header comment
above can literally be the first thing in the file: Lean requires `import` commands to
precede every other command, including module documentation.  Consequently the few
standard facts about function iteration that are used below are proved from scratch.

The Collatz conjecture is a famous open problem.  What is established here is:

* an unconditional reduction of the conjecture to a *descent* hypothesis
  (`reaches1_of_descends`);
* unconditional proofs of descent for every residue class modulo `32` except
  `7`, `15`, `27` and `31`, which sharpen the reduction so that only those four
  classes remain (`CollatzConjecture`);
* unconditional verification of the conjecture for all powers of two and for all
  positive integers below `1000`.
-/

namespace Brockian.CollatzPartial

/-! ## Iteration -/

/-- `iterate f k n` is the `k`-fold application of `f` to `n`. -/

theorem descends_of_three_mod_sixteen {n : Nat} (h : n % 16 = 3) : Descends n := by
  obtain ⟨m, rfl⟩ : ∃ m : Nat, n = 16 * m + 3 := ⟨n / 16, by omega⟩
  refine ⟨6, by omega, ?_⟩
  have h1 : collatz (16 * m + 3) = 48 * m + 10 := by
    rw [collatz_odd (by omega)]; omega
  have h2 : collatz (48 * m + 10) = 24 * m + 5 := by
    rw [collatz_even (by omega)]; omega
  have h3 : collatz (24 * m + 5) = 72 * m + 16 := by
    rw [collatz_odd (by omega)]; omega
  have h4 : collatz (72 * m + 16) = 36 * m + 8 := by
    rw [collatz_even (by omega)]; omega
  have h5 : collatz (36 * m + 8) = 18 * m + 4 := by
    rw [collatz_even (by omega)]; omega
  have h6 : collatz (18 * m + 4) = 9 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  show iterate collatz 6 (16 * m + 3) < 16 * m + 3
  rw [iterate_succ_apply, iterate_succ_apply, iterate_succ_apply, iterate_succ_apply,
    iterate_succ_apply, iterate_succ_apply, iterate_zero, h1, h2, h3, h4, h5, h6]
  omega

/-- Descent is unconditional for `n ≡ 11 [MOD 32]`: eight Collatz steps take `32 * m + 11`
to `27 * m + 10`. -/
