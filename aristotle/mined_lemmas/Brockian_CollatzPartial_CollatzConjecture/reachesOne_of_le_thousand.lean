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

theorem reachesOne_of_le_thousand (n : Nat) (h0 : 0 < n) (h : n ≤ 1000) : ReachesOne n := by
  have key : ∀ m, m < 1001 → 0 < m → ∃ k, k < 200 ∧ iter collatz k m = 1 := by decide +kernel
  obtain ⟨k, -, hk⟩ := key n (by omega) h0
  exact ⟨k, hk⟩

end CollatzPartial
end Brockian

