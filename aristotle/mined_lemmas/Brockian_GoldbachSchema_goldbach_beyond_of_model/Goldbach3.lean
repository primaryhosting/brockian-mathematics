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

/-
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Goldbach Beyond Of Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_beyond_of_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
namespace Brockian
namespace GoldbachSchema

/-- The binary Goldbach property: `n` is a sum of two primes. -/

def Goldbach3 (n : ℕ) : Prop :=
  ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧ p + q + r = n

example : Goldbach2 10 := ⟨3, 7, by norm_num, by norm_num, by norm_num⟩

example : Goldbach3 9 := ⟨3, 3, 3, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- A *model* of binary Goldbach beyond a bound: a witness function assigning to every even
`n ≥ bound` a prime `witness n ≤ n` whose complement `n - witness n` is again prime. -/
structure Model where
  /-- The bound beyond which the model certifies the binary Goldbach property. -/
  bound : ℕ
  /-- The witness function: the smaller summand attached to an even number. -/
  witness : ℕ → ℕ
  /-- The witness never exceeds the number it decomposes. -/
  witness_le : ∀ n : ℕ, bound ≤ n → Even n → witness n ≤ n
  /-- The witness is prime. -/
  witness_prime : ∀ n : ℕ, bound ≤ n → Even n → Nat.Prime (witness n)
  /-- The complement of the witness is prime. -/
  cowitness_prime : ∀ n : ℕ, bound ≤ n → Even n → Nat.Prime (n - witness n)

/-- Every model certifies the binary Goldbach property beyond its bound. -/
