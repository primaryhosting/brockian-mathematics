import Mathlib

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
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

namespace QI

/-! ## The Boolean cube as an `𝔽₂`-vector space -/

/-- `n`-bit strings, viewed as the elementary abelian 2-group `(ℤ/2)ⁿ`;
addition is bitwise XOR. -/
abbrev V (n : ℕ) : Type := Fin n → ZMod 2


lemma dotp_zero_right {n : ℕ} (x : V n) : dotp x 0 = 0 := by
  simp [dotp]

/-! ## The quantum side: interference in Simon's algorithm

After the oracle call and the measurement of the second register, the first register of
Simon's algorithm carries the uniform superposition over the coset `{x₀, x₀ + s}`.
Applying the Hadamard transform and measuring yields an outcome `y`, and the two lemmas
below say exactly that this outcome is *uniformly distributed over the hyperplane*
`s^⊥ = {y | ⟪s, y⟫ = 0}`: outcomes with `⟪s, y⟫ = 1` have amplitude `0`, and each of the
`2ⁿ⁻¹` remaining outcomes has probability `2 / 2ⁿ = 2^{-(n-1)}`. -/

/-- The character `a ↦ (-1)ᵃ` of `ℤ/2`. -/
