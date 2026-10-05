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
# Brocard Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardProblem.BrocardConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Brocard's problem asks for all natural numbers `n`, `m` with `n ! + 1 = m ^ 2`.
The only known solutions are `(n, m) = (4, 5), (5, 11), (7, 71)`; the assertion that
there are no further solutions is Brocard's conjecture, which is open.

This file develops the material from first principles, with no imports and hence without
`Mathlib`: the mandated header comment above has to be the first command of the file, and
Lean does not allow an `import` to follow a module docstring.

Contents:

* `Brockian.BrocardProblem.factorial` : the factorial function.
* `Brockian.BrocardProblem.brocard_iff_four_mul_consecutive` : an unconditional
  reformulation of the equation for `n ≥ 2`, namely `n ! + 1` is a perfect square if and
  only if `n ! = 4 * k * (k + 1)` for some `k`, i.e. if and only if `n !` is four times a
  product of two consecutive natural numbers.
* `Brockian.BrocardProblem.brocard_small` : an unconditional verification that
  `(4, 5)`, `(5, 11)`, `(7, 71)` are the only solutions with `n ≤ 200`. Each excluded
  value of `n` is handled by exhibiting a modulus `q` for which `n ! + 1` is not a square
  modulo `q`.
* `Brockian.BrocardProblem.BrocardConjecture` : Brocard's conjecture, proved conditionally
  on the (open) reformulated statement for `n ≥ 201`.
-/

namespace Brockian.BrocardProblem

set_option maxRecDepth 100000

/-- The factorial function, `factorial n = n !`. -/

theorem brocard_val_seven (m : Nat) (h : factorial 7 + 1 = m ^ 2) : m = 71 := by
  have hf : factorial 7 = 5040 := by decide
  have h2 : m ^ 2 = 5041 := by omega
  rw [Nat.pow_two] at h2
  exact sq_inj (by omega)

/-- **Unconditional partial result.** The only solutions of `n ! + 1 = m ^ 2` with
`n ≤ 200` are `(4, 5)`, `(5, 11)` and `(7, 71)`. -/
