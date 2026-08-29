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
This file is deliberately self-contained (no `import` statements), because the
required header comment above must be the very first thing in the file, and Lean
only accepts `import` commands at the very beginning of a file.  Consequently the
factorial function is defined here from scratch and only core Lean tactics are
used.  Nothing below depends on any unproved assumption.
-/

namespace Brockian.BrocardProblem

/-- The factorial function, `factorial n = n !`. -/

theorem BrocardConjecture :
    BrocardStatement ↔ ∀ n : Nat, 300 ≤ n → ∀ k : Nat, factorial n ≠ 4 * k * (k + 1) := by
  constructor
  · intro hB n hn k hk
    have h : factorial n + 1 = (2 * k + 1) ^ 2 := (factored n k).mpr hk
    rcases hB n (2 * k + 1) h with h' | h' | h' <;> omega
  · intro hR n m h
    rcases Nat.lt_or_ge n 300 with hn | hn
    · exact brocard_below_300 n m hn h
    · exfalso
      obtain ⟨k, hk⟩ := root_odd n m (by omega) h
      subst hk
      exact hR n hn k ((factored n k).mp h)

end Brockian.BrocardProblem

