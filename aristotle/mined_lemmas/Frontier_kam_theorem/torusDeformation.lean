import Mathlib
/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

variable {n : ℕ}

/-- The Euclidean pairing `⟨c, x⟩ = ∑ⱼ cⱼ xⱼ` on `Fin n → ℝ`. -/

noncomputable def torusDeformation (ω : Fin n → ℝ) (ε : ℝ) (s : Finset (Fin n → ℤ))
    (a : (Fin n → ℤ) → ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => -ε * ∑ k ∈ s, a k * (k j : ℝ) * Real.cos (2 * Real.pi * dotZR k x) / dotZR k ω

/-- The `j`-th partial derivative of a function of several real variables. -/
