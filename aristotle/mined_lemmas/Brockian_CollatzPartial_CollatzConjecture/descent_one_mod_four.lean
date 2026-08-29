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
This file deliberately has no `import` line: the required header above is a module
docstring, and Lean requires all imports to precede any command, including module
docstrings.  Everything below therefore uses only core Lean 4 (no Mathlib), which
is sufficient for the development.
-/

set_option autoImplicit false

namespace Brockian.CollatzPartial

/-- One step of the Collatz map: `n ↦ n / 2` for even `n`, `n ↦ 3 * n + 1` for odd `n`. -/

theorem descent_one_mod_four {n : Nat} (hn : 1 < n) (h : n % 4 = 1) :
    ∃ k, 0 < k ∧ iter k n < n := by
  refine ⟨3, by omega, ?_⟩
  obtain ⟨m, hm⟩ : ∃ m, n = 4 * m + 1 := ⟨n / 4, by omega⟩
  have hm1 : 1 ≤ m := by omega
  have h1 : collatz n = 12 * m + 4 := by
    rw [collatz_odd (by omega)]; omega
  have h2 : collatz (12 * m + 4) = 6 * m + 2 := by
    rw [collatz_even (by omega)]; omega
  have h3 : collatz (6 * m + 2) = 3 * m + 1 := by
    rw [collatz_even (by omega)]; omega
  have hexp : iter 3 n = collatz (collatz (collatz n)) := rfl
  rw [hexp, h1, h2, h3]
  omega

/-- Auxiliary bounded form of the reduction, proved by induction on a bound `N`. -/
