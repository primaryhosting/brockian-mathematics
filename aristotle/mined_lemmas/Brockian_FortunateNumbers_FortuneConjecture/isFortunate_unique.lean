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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the required header above is a module docstring, which Lean parses as a
command, so no `import` line may follow it.  The whole development below is therefore
self-contained and uses only the Lean 4 core library (no Mathlib).
-/

namespace Brockian.FortunateNumbers

/-! ## Primality and the primorial -/

/-- `IsPrime p` : `p` is a prime natural number. -/

theorem isFortunate_unique {n m₁ m₂ : Nat} (h₁ : IsFortunate n m₁) (h₂ : IsFortunate n m₂) :
    m₁ = m₂ := by
  rcases Nat.lt_trichotomy m₁ m₂ with h | h | h
  · exact absurd h₁.2.1 (h₂.2.2 m₁ h h₁.1)
  · exact h
  · exact absurd h₂.2.1 (h₁.2.2 m₂ h h₂.1)

/-- **Unconditional partial result.** No prime `q ≤ n` divides the `n`-th fortunate number:
all prime factors of a fortunate number exceed its index. -/
