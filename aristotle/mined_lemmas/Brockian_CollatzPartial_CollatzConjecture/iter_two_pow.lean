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

theorem iter_two_pow (m : Nat) : iter collatz m (2 ^ m) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [iter_succ]
      have h2 : collatz (2 ^ (m + 1)) = 2 ^ m := by
        have hp : 2 ^ (m + 1) = 2 ^ m * 2 := by
          rw [Nat.pow_succ]
        have he : 2 ^ (m + 1) % 2 = 0 := by
          rw [hp]; omega
        rw [collatz, if_pos he, hp]
        omega
      rw [h2, ih]

/-- Every power of two reaches `1`. -/
