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

theorem reachesOne_of_iter {n k : Nat} (h : ReachesOne (iter collatz k n)) : ReachesOne n := by
  obtain ⟨m, hm⟩ := h
  exact ⟨m + k, by rw [iter_add]; exact hm⟩

/-- **Conditional Collatz theorem.**  The Collatz conjecture — every positive natural number
reaches `1` under iteration of the Collatz map — follows from the (weaker looking) descent
property `Descends`, namely that every `n > 1` eventually iterates to some value smaller
than `n` itself. -/
