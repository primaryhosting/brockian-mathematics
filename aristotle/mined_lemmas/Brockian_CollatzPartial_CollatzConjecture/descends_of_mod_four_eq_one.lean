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
This file is deliberately self-contained (it uses only the Lean 4 core library),
so that the header comment above can appear at the very top of the file:
Lean does not permit a module docstring to precede `import` commands.
-/

namespace Brockian
namespace CollatzPartial

/-- The Collatz step: `n ↦ n / 2` if `n` is even, `n ↦ 3 * n + 1` if `n` is odd. -/

theorem descends_of_mod_four_eq_one {n : Nat} (h1 : 1 < n) (h4 : n % 4 = 1) :
    iter collatz 3 n < n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  show collatz (collatz (collatz (4 * m + 1))) < 4 * m + 1
  have e1 : collatz (4 * m + 1) = 12 * m + 4 := by
    rw [collatz, if_neg (by omega)]; omega
  have e2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [collatz, if_pos (by omega)]; omega
  have e3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [collatz, if_pos (by omega)]; omega
  rw [e1, e2, e3]
  omega

/-- **Reduction of the descent property to the residue class `3 mod 4`.**  If every `n > 1`
with `n % 4 = 3` eventually iterates to a smaller value, then `Descends` holds, and hence
(by `CollatzConjecture`) so does the full Collatz conjecture. -/
